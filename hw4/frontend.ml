open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list  (* stream is in reversed order of the actual flow *)
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

let cmp_binop_to_bop : Ast.binop -> Ll.bop = function
  | Add  -> Ll.Add
  | Sub  -> Ll.Sub
  | Mul  -> Ll.Mul
  | And  -> Ll.And  (* TODO: really? *)
  | Or   -> Ll.Or
  | IAnd -> Ll.And
  | IOr  -> Ll.Or
  | Shl  -> Ll.Shl
  | Shr  -> Ll.Lshr
  | Sar  -> Ll.Ashr
  | _ -> failwith "cmp_binop_to_bop: invalid binop"

let cmp_binop_to_cnd : Ast.binop -> Ll.cnd = function
  | Eq  -> Ll.Eq
  | Neq -> Ll.Ne
  | Lt  -> Ll.Slt
  | Lte -> Ll.Sle
  | Gt  -> Ll.Sgt
  | Gte -> Ll.Sge
  | _ -> failwith "cmp_binop_to_cnd: invalid binop"

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the stack, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t: Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t: Ast.ty) (size: Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]


(* Decode a Ptr type to the type it is referencing *)
let decode_ptr_ty (ptr_ty: Ll.ty) (loc) : Ll.ty =
  match ptr_ty with
  | Ptr ty -> ty
  | _ -> failwith @@ "decode_ptr_ty: ptr_ty is not Ptr " ^ Range.string_of_range loc


(* Decode wrapper type and element type from the return type of array expression
   Example: { i64, [0 x T] }* -> { i64, [0 x T] }, T
 *)
let decode_arr_ty (arr_struct_ptr_ty: Ll.ty) (loc) : Ll.ty * Ll.ty =
  let arr_struct_ty = decode_ptr_ty arr_struct_ptr_ty loc in
  match arr_struct_ty with
  | Struct (_ :: arr_ty :: []) -> (
    match arr_ty with
    | Array (_, elem_ty) -> arr_struct_ty, elem_ty
    | _ -> failwith "decode_arr_ty: unexpected arr_ty"
  )
  | _ -> failwith "decode_arr_ty: unexpected arr_struct_ty"



(* Compiles an expression exp in context c, outputting the Ll operand that will
   receive the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c: Ctxt.t) (exp: Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull rty -> (cmp_rty rty), Null, []
  | CBool b -> (
    match b with
    | true -> I1, Const 1L, []
    | false -> I1, Const 0L, []
  )
  | CInt i -> I64, Const i, []
  | CStr s -> (
    let gid = gensym "global_str" in
    let uid = gensym "cstr" in
    let ty = Array (1 + (String.length s), I8) in
    Ptr I8, (Id uid), [I (uid, Bitcast (Ptr ty, (Gid gid), Ptr I8));
                        G (gid, (ty, GString s))]
  )
  | CArr (ty, vals) -> (
     let val_count = Const (Int64.of_int (List.length vals)) in
     let arr_ty, arr_op, arr_stream = oat_alloc_array ty val_count in
     let stream, _ = List.fold_left (fun (s, index) exp ->
       let exp_ty, exp_operand, exp_stream = cmp_exp c exp in
       let uid = gensym "carr_store" in
       let store_stream = exp_stream
        >:: (I (uid, Gep (arr_ty, arr_op, [Const 0L; Const 1L; Const (Int64.of_int index)])))
        >:: (I (uid, Store (exp_ty, exp_operand, Id uid)))
       in
       s >@ store_stream, index + 1
       ) (arr_stream, 0) vals in
     arr_ty, arr_op, stream
  )
  | NewArr (ty, size) -> (
    let size_ty, size_operand, size_stream = cmp_exp c size in
    let new_arr_ty, new_arr_op, new_arr_stream =  oat_alloc_array ty size_operand in
    new_arr_ty, new_arr_op, size_stream >@ new_arr_stream
    )
  | Id id -> (
    let ptr_ty, ptr_operand = Ctxt.lookup id c in
    let ty = decode_ptr_ty ptr_ty exp.loc in
    let uid =  gensym id in
    ty, (Id uid), [I (uid, Load (ptr_ty, ptr_operand))]
  )
  | Index (arr, idx) -> (
    (* Get the pointer to the element *)
    let ptr_ty, ptr_operand, ptr_stream = cmp_ref c exp in
    let ty = decode_ptr_ty ptr_ty exp.loc in
    let uid =  gensym "load" in
    ty, (Id uid), ptr_stream >:: (I (uid, Load (ptr_ty, ptr_operand)))
  )
  | Call (func, args) -> (
    let func_ty, func_operand, stream = cmp_ref c func in
    let fold_arg ((ll_args: (Ll.ty * Ll.operand) list), (stream)) (arg: Ast.exp node) =
      let arg_ty, arg_operand, arg_stream = cmp_exp c arg in
      ll_args >:: (arg_ty, arg_operand),  (* reversed *)
      stream >@ arg_stream
    in
    let ll_args, stream = List.fold_left fold_arg ([], stream) args in
    let ll_args = List.rev ll_args (* reverse *) in
    let uid = gensym "call" in
    match func_ty with
    | Ptr (Fun (_, ret_ty)) -> (
      ret_ty, (Id uid), stream >:: (I (uid, Call (ret_ty, func_operand, ll_args)))
    )
    | _ -> failwith  "cmp_exp: Call not bound to a function"
  )
  | Bop (binop, op1, op2) -> (
    let uid = gensym "bop" in
    let op1_ty, op1_operand, op1_stream = cmp_exp c op1 in
    let op2_ty, op2_operand, op2_stream = cmp_exp c op2 in
    let expected_op1_ast_ty, expected_op2_ast_ty, res_ast_ty = typ_of_binop binop in
    let expected_op1_ty = cmp_ty expected_op1_ast_ty in
    let expected_op2_ty = cmp_ty expected_op2_ast_ty in
    let res_ty = cmp_ty res_ast_ty in
    if op1_ty <> expected_op1_ty || op2_ty <> expected_op2_ty || op1_ty <> op2_ty then
      failwith "cmp_exp: Bop with unexpected operand type"
    else
      let op_ty = op1_ty in
      let insn : Ll.insn = (
        if op_ty = res_ty then
          Binop (cmp_binop_to_bop binop, op_ty, op1_operand, op2_operand)
        else
          Icmp (cmp_binop_to_cnd binop, op_ty, op1_operand, op2_operand)
      ) in
      res_ty, (Id uid), op1_stream >@ op2_stream >:: (I (uid, insn))
  )
  | Uop (unop, op) -> (
    let op_ty, op_operand, op_stream = cmp_exp c op in
    let op1_ty, op2_ty = typ_of_unop unop in
    let res_ty = cmp_ty op2_ty in
    let uid = gensym "uop" in
    let insn: Ll.insn = (
     match unop with
     | Neg -> Binop (Sub, res_ty, Const 0L, op_operand)
     | Lognot -> Binop (Xor, res_ty, Const 1L, op_operand)
     | Bitnot -> Binop (Xor, res_ty, Const (-1L), op_operand)
    ) in
    res_ty, Id uid, op_stream >:: (I (uid, insn))
  )

and cmp_ref (c: Ctxt.t) (exp: Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  (* Variable *)
  | Id id -> (
    let ty, operand = Ctxt.lookup id c in
    ty, operand, []
  )
  (* Array subscript *)
  | Index (arr, idx) -> (
    (* Evaluate expression (not reference) of the array*)
    let arr_ty, arr_operand, arr_stream = cmp_exp c arr in
    let arr_struct_ty, elem_ty = decode_arr_ty arr_ty exp.loc in
    (* Evaluate index *)
    let idx_ty, idx_operand, idx_stream = cmp_exp c idx in
    (* Perform getelementptr *)
    let uid = gensym "gep" in
    (Ptr elem_ty), (Id uid), (arr_stream >@ idx_stream >:: I (
      uid, Gep (arr_ty, arr_operand, [Const 0L; Const 1L; idx_operand])
    ))
  )
  (* Not a valid lhs expression *)
  | _ -> failwith "cmp_lhs: unexpected exp.elt type"

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec cmp_stmt (c: Ctxt.t) (rt: (Ll.ty * Ll.operand * Ll.lbl)) (stmt: Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Assn (lhs, rhs) -> (
    let lhs_ty, lhs_operand, lhs_stream = cmp_ref c lhs in
    let rhs_ty, rhs_operand, rhs_stream = cmp_exp c rhs in
    if lhs_ty <> Ptr rhs_ty then
      failwith @@ "cmp_stmt: Assn types unmatched at " ^ Range.string_of_range stmt.loc
    else
      c, lhs_stream >@ rhs_stream >@ [I (gensym "store", Store (rhs_ty, rhs_operand, lhs_operand))]
  )
  | Decl (id, exp) -> (
    let exp_ty, exp_operand, exp_stream = cmp_exp c exp in
    let uid = gensym id in
    Ctxt.add c id (Ptr exp_ty, Id uid),  (* local variable has pointer type *)
    exp_stream >:: (* exp_stream should consist of normal I *)
    (E (uid, Alloca exp_ty)) >::  (* only Alloca is hoisted *)
    (I (gensym "store", Store (exp_ty, exp_operand, Id uid)))  (* Store after exp_stream *)
  )
  | Ret exp_option -> (
    let rt_ty, rt_operand, rt_lbl = rt in
    match exp_option with
    | Some exp -> (
      let exp_ty, exp_operand, exp_stream = cmp_exp c exp in
      if exp_ty <> rt_ty then failwith "cmp_stmt: Ret types unmatched"
      else
        c, exp_stream
          >:: (I (gensym "store", Store (rt_ty, exp_operand, rt_operand)))
          >:: (T (Br rt_lbl))
    )
    | None -> (
      if Void <> rt_ty then failwith "cmp_stmt: Ret types unmatched"
      else
        c, [T (Br rt_lbl)]
    )
  )
  | SCall (func, args) -> (
    let ret_ty, ret_operand, stream = cmp_exp c { elt = (Ast.Call (func, args)); loc = stmt.loc } in
    c, stream
  )
  | If (cond, then_block, else_block) -> (
    let cond_ty, cond_operand, cond_stream = cmp_exp c cond in
    let then_lbl = gensym "if_then" in
    let _ (* discard *), then_stream = cmp_block c rt then_block in
    let end_lbl = gensym "if_end" in
    let else_lbl, else_block_stream = (
      match else_block with
      | [] -> end_lbl, []
      | _ -> (
        let else_lbl = gensym "if_else" in
        let _ (* discard *), else_stream = cmp_block c rt else_block in
        else_lbl, [L else_lbl] >@ else_stream >:: (T (Br end_lbl))
      )
    ) in
    c, cond_stream
      >:: (T (Cbr (cond_operand, then_lbl, else_lbl)))
      >:: (L then_lbl)
      >@  then_stream
      >:: (T (Br end_lbl))
      >@  else_block_stream
      >:: (L end_lbl)
  )
  | For (vdecls, cond_option, next_option, body_stmts) -> (
    (* Transform to Decls + While *)
    let fold_vdecl (inner_c, stream) vdecl =
      let inner_c', stream' = cmp_stmt inner_c rt { elt = (Ast.Decl vdecl); loc = stmt.loc } in
      (* No loc for vdecls, use stmt.loc instead *)
      inner_c', stream >@ stream'
    in
    let inner_c, vdecls_stream = List.fold_left fold_vdecl (c, []) vdecls in
    let while_cond : Ast.exp node = (
      match cond_option with
      | Some cond -> cond
      | None -> { elt = (CBool true); loc = stmt.loc }
    ) in
    let while_stmts: stmt node list = (
      match next_option with
      | Some next -> body_stmts @ [next]
      | None -> body_stmts
    ) in
    let _, while_stream = cmp_stmt
      inner_c (* vdecls are available inside the body *)
      rt
      { elt = (Ast.While (while_cond, while_stmts)); loc = stmt.loc } in
    c (* inner context is no longer available *),
    vdecls_stream >@ while_stream
  )
  | While (cond, body_stmts) -> (
    let cond_ty, cond_operand, cond_stream = cmp_exp c cond in
    let inner_c, body = cmp_block c rt body_stmts in
    let begin_lbl = gensym "while_begin" in
    let while_lbl = gensym "while_body" in
    let end_lbl = gensym "while_end" in
    c (* inner_c are only available inside the body *),
    [T (Br begin_lbl)]
    >:: (L begin_lbl)
    >@  cond_stream
    >:: (T (Cbr (cond_operand, while_lbl, end_lbl)))
    >:: (L while_lbl)
    >@  body
    >:: (T (Br begin_lbl))
    >:: (L end_lbl)
  )


(* Compile a series of statements *)
and cmp_block (c: Ctxt.t) (rt: (Ll.ty * Ll.operand * Ll.lbl)) (stmts: Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifier to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c: Ctxt.t) (p: Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
    | Ast.Gvdecl { elt={ name; init } } ->
       let ll_ty = (
        match init.elt with
        | CNull rty -> cmp_ty (TRef rty)
        | CBool _ -> cmp_ty TBool
        | CInt _ -> cmp_ty TInt
        | CStr _ -> cmp_ty (TRef RString)
        | CArr (ty, _) | NewArr (ty, _) -> cmp_ty (TRef (RArray ty))
        | _ -> failwith "cmp_global_ctxt: invalid init.elt"
       ) in
       Ctxt.add c name (Ptr ll_ty, Gid name)
    | _ -> c
  ) c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

let cmp_fdecl (c: Ctxt.t) (f: Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  (* Compile return type, operand and label *)
  let rt_ty: Ll.ty = cmp_ret_ty f.elt.frtyp in
  let rt_uid: Ll.uid = gensym "ret" in
  let rt_operand: Ll.operand = Id rt_uid in
  let rt_lbl: Ll.lbl = gensym (f.elt.fname ^ "ret") in
  let alloc_ret_stream = (
    match rt_ty with
    | Void -> []
    | _ -> [I (rt_uid, Alloca rt_ty)]
  ) in

  (* Process args *)
  let fold_arg (c, (arg_uids: Ll.uid list), (arg_tys: Ll.ty list), stream) ((ty, id): Ast.ty * id) = (
    let ll_ty = cmp_ty ty in
    let uid = gensym "arg" in
    Ctxt.add c id (Ptr ll_ty, Id uid),
    id :: arg_uids,    (* reversed *)
    ll_ty :: arg_tys,  (* reversed *)
    stream >@ lift [
      (uid, Alloca ll_ty)
    ; (gensym "fdecl_store", Store (ll_ty, Id id, Id uid))
    ]
  ) in
  let c, arg_uids, arg_tys, arg_stream = List.fold_left fold_arg (c, [], [], []) f.elt.args in
  let arg_uids: Ll.uid list = List.rev arg_uids in
  let arg_tys: Ll.ty list = List.rev arg_tys in

  (* Compile function body *)
  let c, block_stream = cmp_block c (rt_ty, rt_operand, rt_lbl) f.elt.body in

  (* Handle unified return block *)
  let ret_stream = [T (Br rt_lbl)] >:: (L rt_lbl) >@ (
    match rt_ty with
    | Void -> [T (Ret (Void, None))]
    | _ -> (
      let val_uid = gensym "ret_val" in
      [I (val_uid, Load (Ptr rt_ty, rt_operand))] >::
      (T (Ret (rt_ty, Some (Id val_uid))))
    )
  ) in

  (* Process the stream *)
  let cfg, gdecls = cfg_of_stream (alloc_ret_stream >@
                                   arg_stream >@
                                   block_stream >@
                                   ret_stream)
  in

  (* Output *)
  {
    f_ty = (arg_tys, rt_ty)
  ; f_param = arg_uids
  ; f_cfg = cfg
  }, gdecls



(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e: Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull rty -> (cmp_ty (Ast.TRef rty), GNull), []
  | CBool b -> (cmp_ty Ast.TBool, GInt (
    match b with
    | true -> 1L
    | false -> 0L
  )), []
  | CInt i -> (I64, GInt i), []
  | CStr s -> (
    let str_lit_gid = gensym "global_str" in
    let str_lit_type = Array ((String.length s) + 1, I8) in
    (* Pointer to the start of string literal *)
    (Ptr I8, GBitcast (Ptr (str_lit_type), GGid str_lit_gid, Ptr I8)),
    (* Additional gdecl for string literal *)
    [str_lit_gid, (str_lit_type, GString s)]
  )
  | CArr (ty, vals) -> (
    let val_count = List.length vals in
    let arr_struct_gid = gensym "global_arr" in
    let arr_body_ty = Array(val_count, cmp_ty ty) in
    let actual_arr_struct_ty = Struct [I64; arr_body_ty] in
    let abstract_arr_struct_ty = cmp_rty (RArray ty) in
    let fold_val ((init_list: Ll.gdecl list), (more_gdecls: (Ll.gid * Ll.gdecl) list)) (e: Ast.exp node) =
      let init, more_gdecls' = cmp_gexp c e in
      init :: init_list,  (* reversed *)
      more_gdecls @ more_gdecls'
    in
    let init_list, more_gdecls = List.fold_left fold_val ([], []) vals in
    let init_list = List.rev init_list (* reverse *) in
    (* Pointer to the array structure *)
    (Ptr abstract_arr_struct_ty, GBitcast (Ptr actual_arr_struct_ty, GGid arr_struct_gid, Ptr abstract_arr_struct_ty)),
    (* Actual element storage *)
    (arr_struct_gid, (actual_arr_struct_ty,
      GStruct [ I64, GInt (Int64.of_int val_count)
              ; arr_body_ty, GArray init_list])
    ) :: more_gdecls
  )
  | _ -> failwith "cmp_gexp: invalid e.elt type"

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
