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

end

(* Mapping of identifiers representing struct definitions to 
 * the corresponding name-to-name-to-type map.

   Note:  You will need to use these operations when compiling structures.
*)
module TypeCtxt = struct
  type t = (Ast.id * Ast.field list) list  (* struct id, fields *)
  let empty = []

  let add c id bnd = (id, bnd) :: c
  let lookup id c = List.assoc id c
  let lookup_field st_name f_name (c : t) = 
    let rec lookup_field_aux f_name l =
      match l with
      | [] -> failwith "TypeCtxt.lookup_field: Not_found"
      | h :: t -> if h.fieldName = f_name then h.ftyp else lookup_field_aux f_name t in
    lookup_field_aux f_name (List.assoc st_name c)

  let rec index_of f l i =
    match l with
    | [] -> None
    | h :: t -> if h.fieldName = f then Some i else index_of f t (i + 1) 

  (* Return the index of a field in the struct. *)
  let index_of_field_opt st f (c : t) = 
    index_of f (List.assoc st c) 0

  let index_of_field st f c =
    match index_of_field_opt st f c with
    | None -> failwith "index_of_field: Not found"
    | Some x -> x

  (* Return a pair of base type and index into struct *)
  let rec lookup_field_name (st:Ast.id) (f:Ast.id) (c : t) : (Ast.ty * Int64.t) =
    let fields = lookup st c in
    match index_of f fields 0 with
    | None -> failwith "no such field"
    | Some x -> List.(nth fields x).ftyp, Int64.of_int x 
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   NOTE: structure types are named, so they compile to their named form
*)

let rec cmp_ty (tc: TypeCtxt.t) : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty tc r)
  | Ast.TNullRef r -> Ptr (cmp_rty tc r)


and cmp_ret_ty (tc: TypeCtxt.t) : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty tc t

and cmp_fty (tc: TypeCtxt.t) (ts, r) : Ll.fty =
  List.map (cmp_ty tc) ts, cmp_ret_ty tc r

and cmp_rty (tc: TypeCtxt.t) : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array (0, cmp_ty tc u)]
  | Ast.RStruct r -> Namedt r
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty tc (ts, t) in
      Fun (args, ret)

let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)


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

let str_arr_ty s = Array(1 + String.length s, I8)
let i1_op_of_bool b   = Ll.Const (if b then 1L else 0L)
let i64_op_of_int i   = Ll.Const (Int64.of_int i)


(* Decode a Ptr type to the type it is referencing *)
let decode_ptr_ty (ptr_ty: Ll.ty) : Ll.ty =
  match ptr_ty with
  | Ptr ty -> ty
  | _ -> failwith @@ "decode_ptr_ty: ptr_ty is not Ptr"


(* Decode wrapper type and element type from the return type of array expression
   Example: { i64, [0 x T] }* -> { i64, [0 x T] }, T                             *)
let decode_arr_ty (arr_struct_ptr_ty: Ll.ty) : Ll.ty * Ll.ty =
  let arr_struct_ty = decode_ptr_ty arr_struct_ptr_ty in
  match arr_struct_ty with
  | Struct (_ :: arr_ty :: []) -> (
    match arr_ty with
    | Array (_, elem_ty) -> arr_struct_ty, elem_ty
    | _ -> failwith "decode_arr_ty: unexpected arr_ty"
  )
  | _ -> failwith "decode_arr_ty: unexpected arr_struct_ty"


(* Generate code to allocate an array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array ct (t: Ast.ty) (size: Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty ct @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]


(* STRUCT TASK (done): Complete this helper function that allocates an oat structure on the
   heap and returns a target operand with the appropriate reference.  
   
   - generate a call to 'oat_malloc' and use bitcast to convert the
     resulting pointer to the right type

   - make sure to calculate the correct amount of space to allocate!
*)
let oat_alloc_struct ct (id: Ast.id) : Ll.ty * operand * stream =
  let fields = TypeCtxt.lookup id ct in
  let ans_id, raw_id = gensym "struct", gensym "raw_struct" in
  let ans_ty = cmp_ty ct @@ TRef (RStruct id) in
  let raw_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ raw_id, Call (raw_ty, Gid "oat_malloc", [I64, i64_op_of_int (8 * List.length fields)])
    ; ans_id, Bitcast (raw_ty, Id raw_id, ans_ty) ]


let cmp_binop_to_bop : Ast.binop -> Ll.bop = function
  | Add  -> Ll.Add
  | Sub  -> Ll.Sub
  | Mul  -> Ll.Mul
  | And  -> Ll.And
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

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 
*)
let rec cmp_exp (tc: TypeCtxt.t) (c: Ctxt.t) (exp: Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | Ast.CInt i  -> I64, Const i, []
  | Ast.CNull r -> cmp_ty tc (TNullRef r), Null, []
  | Ast.CBool b -> I1, i1_op_of_bool b, []

  | Ast.CStr s ->
    let gid = gensym "str_arr" in
    let str_typ = str_arr_ty s in
    let uid = gensym "str" in
        Ptr I8, Id uid, []
    >:: G(gid, (str_typ, GString s))
    >:: I(uid, Gep(Ptr str_typ, Gid gid, [Const 0L; Const 0L;]))

  | Ast.Bop (binop, op1, op2) ->
    let uid = gensym "bop" in

    let op1_ty, op1_operand, op1_stream = cmp_exp tc c op1 in
    let op2_ty, op2_operand, op2_stream = cmp_exp tc c op2 in
    let op_ty = op1_ty in  (* with typechecker, op1_ty and op1_ty must be equal, denoted as op_ty *)

    let expected_op_ast_ty, _, res_ast_ty = typ_of_binop binop in
    let res_ty = cmp_ty tc res_ast_ty in
    let insn : Ll.insn = (
      if expected_op_ast_ty = res_ast_ty
      (* Here we use op_ty (type of operands) to generate instruction, to support pointer comparison *)
      then Binop (cmp_binop_to_bop binop, op_ty, op1_operand, op2_operand)
      else Icmp (cmp_binop_to_cnd binop, op_ty, op1_operand, op2_operand)
    ) in
    (* For the return type, we use the expected type from binop.
       Comparing pointers generates boolean, which matches the expected res_ty.
       If the input program performs AND, OR, etc. on pointers, the error will be in LLVM-IR. *)
    res_ty, (Id uid), op1_stream >@ op2_stream >:: (I (uid, insn))

  | Ast.Uop (uop, e) ->
    let t, ret_ty = typ_of_unop uop in
    let op, code = cmp_exp_as tc c e (cmp_ty tc t) in
    let ans_id = gensym "unop" in
    let cmp_uop op = function
      | Ast.Neg    -> Binop (Sub, I64, i64_op_of_int 0, op)
      | Ast.Lognot -> Icmp  (Eq, I1, op, i1_op_of_bool false)
      | Ast.Bitnot -> Binop (Xor, I64, op, i64_op_of_int (-1)) in
    cmp_ty tc ret_ty, Id ans_id, code >:: I (ans_id, cmp_uop op uop)

  | Ast.Id id ->
    let t, op = Ctxt.lookup id c in
    begin match t with
      | Ptr (Fun _) -> t, op, []
      | Ptr t ->
        let ans_id = gensym id in
        t, Id ans_id, [I(ans_id, Load(Ptr t, op))]
      | _ -> failwith "broken invariant: identifier not a pointer"
    end

  (* ARRAY TASK (done): complete this case to compile the length(e) expression.
       The emitted code should yield the integer stored as part 
       of the array struct representation.
  *)
  (* TODO: test *)
  | Ast.Length e ->
    let arr_ty, arr_op, arr_code = cmp_exp tc c e in
    let ans_ty = match arr_ty with
      | Ptr (Struct [_; Array (_, t)]) -> t
      | _ -> failwith "Length: on non array"
    in
    let len_ptr_uid = gensym "length_ptr" in
    let len_uid = gensym "length" in
    ans_ty, (Id len_uid),
    arr_code >@ lift
      [ len_ptr_uid, Gep (arr_ty, arr_op, [i64_op_of_int 0; i64_op_of_int 0])
      ; len_uid, Load (Ptr (I64), Id len_ptr_uid)
      ]

  | Ast.Index (e, i) ->
    let ptr_ans_ty, ptr_op, code = cmp_exp_lhs tc c exp in
    let ans_ty = decode_ptr_ty ptr_ans_ty in
    let ans_id = gensym "index" in
    ans_ty, Id ans_id, code >:: I (ans_id, Load (ptr_ans_ty, ptr_op))

  | Ast.Call (f, es) ->
    cmp_call tc c f es 

  | Ast.CArr (elt_ty, cs)  ->
    (* All tys (TBool, TInt, TRef, TNullRef) are stored as I64 *)
    let size_op = Ll.Const (Int64.of_int @@ List.length cs) in
    let arr_ty, arr_op, alloc_code = oat_alloc_array tc elt_ty size_op in
    let ll_elt_ty = cmp_ty tc elt_ty in
    let add_elt s (i, elt) =
      let elt_op, elt_code = cmp_exp_as tc c elt ll_elt_ty in
      let ind = gensym "ind" in 
      s >@ elt_code >@ lift
        [ ind, Gep(arr_ty, arr_op, [Const 0L; Const 1L; i64_op_of_int i ])
        ; "",  Store(ll_elt_ty, elt_op, Id ind) ] 
    in
    let ind_code = List.(fold_left add_elt [] @@ mapi (fun i e -> i, e) cs) in
    arr_ty, arr_op, alloc_code >@ ind_code

  (* ARRAY TASK (done): Modify the compilation of the NewArr construct to implement the
     initializer:
         - the initializer is a loop that uses id as the index
         - each iteration of the loop the code evaluates e2 and assigns it
           to the index stored in id.

     Note: You can either write code to generate the LL loop directly, or
     you could write the loop using abstract syntax and then call cmp_stmt to
     compile that into LL code...
  *)
  | Ast.NewArr (elt_ty, e1, x, e2) ->
    (* All tys (TBool, TInt, TRef, TNullRef) are stored as I64 *)
    let _, size_op, size_code = cmp_exp tc c e1 in
    let arr_ty, arr_op, alloc_code = oat_alloc_array tc elt_ty size_op in
    let _, elt_ty = decode_arr_ty arr_ty in

    let x_id = gensym x in
    let c' = Ctxt.add c x (Ptr I64, Id x_id) in

    let begin_lbl = gensym "newarr_begin" in
    let while_lbl = gensym "newarr_body" in
    let end_lbl = gensym "newarr_end" in

    let cond_id = gensym "newarr_cond" in
    let ptr_id = gensym "newarr_ptr" in
    let idx_id, idx_id2 = gensym "newarr_idx", gensym "newarr_idx" in

    let value_op, value_code = cmp_exp_as tc c' e2 elt_ty in

    arr_ty, arr_op, size_code >@ alloc_code
      (* Declaration *)
      >:: (E (x_id, Alloca I64))
      >:: (I ("", Store (I64, Const 0L, Id x_id)))
      (* While loop head *)
      >:: (T (Br begin_lbl))
      >:: (L begin_lbl)
      (* Condition *)
      >:: (I (idx_id, Load (Ptr I64, Id x_id)))
      >:: (I (cond_id, Icmp (Slt, I64, Id idx_id, size_op)))
      >:: (T (Cbr (Id cond_id, while_lbl, end_lbl)))
      >:: (L while_lbl)
      (* Evaluate exp2 *)
      >@  value_code
      (* Index *)
      >:: (I (ptr_id, Gep (arr_ty, arr_op, [i64_op_of_int 0; i64_op_of_int 1; Id idx_id])))
      (* Assign *)
      >:: (I ("", Store (elt_ty, value_op, Id ptr_id)))
      (* Increment *)
      >:: (I (idx_id2, Binop (Add, I64, Id idx_id, Const 1L)))
      >:: (I ("", Store (I64, Id idx_id2, Id x_id)))
      (* Loop back *)
      >:: (T (Br begin_lbl))
      >:: (L end_lbl)


   (* STRUCT TASK (done): complete this code that compiles struct expressions.
      For each field component of the struct
       - use the TypeCtxt operations to compute getelementptr indices
       - compile the initializer expression
       - store the resulting value into the structure
   *)
  | Ast.CStruct (s_id, l) ->
    (* All tys (TBool, TInt, TRef, TNullRef) are stored as I64 *)
    let s_ty, s_op, alloc_code = oat_alloc_struct tc s_id in
    let set_field (stream) (f_id, exp) =
      let f_ty, f_ind = TypeCtxt.lookup_field_name s_id f_id tc in
      let ll_f_ty = cmp_ty tc f_ty in
      let exp_op, exp_code = cmp_exp_as tc c exp ll_f_ty in
      let ind = gensym "ind" in
      stream >@ exp_code >@ lift
        [ ind, Gep (s_ty, s_op, [Const 0L; Ll.Const f_ind])
        ; "",  Store (ll_f_ty, exp_op, Id ind) ]
    in
    let fields_code = List.(fold_left set_field [] l) in
    s_ty, s_op, alloc_code >@ fields_code

  | Ast.Proj (e, id) ->
    let ptr_ans_ty, ptr_op, code = cmp_exp_lhs tc c exp in
    let ans_ty = decode_ptr_ty ptr_ans_ty in
    let ans_id = gensym "proj" in
    ans_ty, Id ans_id, code >:: I (ans_id, Load (ptr_ans_ty, ptr_op))


and cmp_exp_lhs (tc: TypeCtxt.t) (c: Ctxt.t) (e: exp node) : Ll.ty * Ll.operand * stream =
  match e.elt with
  | Ast.Id x ->
    let t, op = Ctxt.lookup x c in
    t, op, []

  (* STRUCT TASK (done): Complete this code that emits LL code to compute the
     address of the i'th field from a value of struct type.  Note that
     the actual load from the address to project the value is handled by the
     Ast.proj case of the cmp_exp function (above).

     You will find the TypeCtxt.lookup_field_name function helpful.
  *)
  | Ast.Proj (e, f_id) ->
    let s_ty, s_op, s_code = cmp_exp tc c e in
    let s_id = match s_ty with
      | Ptr (Namedt id) -> id
      | _ -> failwith "Proj: non struct"
    in
    let f_ty, f_ind = TypeCtxt.lookup_field_name s_id f_id tc in
    let ll_f_ty = cmp_ty tc f_ty in
    let ptr_id = gensym "field" in
    (Ptr ll_f_ty), (Id ptr_id),
    s_code >:: (I (ptr_id, Gep (s_ty, s_op, [i64_op_of_int 0; Const f_ind])))


  (* ARRAY TASK (done): Modify this index code to call 'oat_assert_array_length' before doing the
     GEP calculation. This should be very straightforward, except that you'll need to use a Bitcast.
     You might want to take a look at the implementation of 'oat_assert_array_length'
     in runtime.c.   (That check is where the infamous "ArrayIndexOutOfBounds" exception would 
     be thrown...)
  *)
  (* TODO: test *)
  | Ast.Index (e, i) ->
    (* Evaluate expression (not reference) of the array*)
    let arr_ty, arr_op, arr_code = cmp_exp tc c e in

    (* Evaluate index *)
    let _, ind_op, ind_code = cmp_exp tc c i in
    let ans_ty = match arr_ty with 
      | Ptr (Struct [_; Array (_,t)]) -> t 
      | _ -> failwith "Index: indexed into non pointer" in
    let ptr_id, tmp_id = gensym "index_ptr", gensym "tmp" in
    (Ptr ans_ty), (Id ptr_id),
    arr_code >@ ind_code >@ lift
      [ tmp_id, Bitcast (arr_ty, arr_op, Ptr (I64))
      ; gensym "result", Call (Void, Gid "oat_assert_array_length", [(Ptr I64, Id tmp_id); (I64, ind_op)])
      ; ptr_id, Gep (arr_ty, arr_op, [i64_op_of_int 0; i64_op_of_int 1; ind_op])
      ]

  | _ -> failwith "invalid lhs expression"

and cmp_call (tc : TypeCtxt.t) (c:Ctxt.t) (exp:Ast.exp node) (es:Ast.exp node list) : Ll.ty * Ll.operand * stream =
  let (t, op, s) = cmp_exp tc c exp in
  let (ts, rt) = 
    match t with
    | Ptr (Fun (l, r)) -> l, r
    | _ -> failwith "nonfunction passed to cmp_call" in
  let args, args_code = List.fold_right2
      (fun e t (args, code) ->
         let arg_op, arg_code = cmp_exp_as tc c e t in
         (t, arg_op)::args, arg_code @ code
      ) es ts ([],[]) in
  let res_id = gensym "result" in
  rt, Id res_id, s >@ args_code >:: I (res_id, Call (rt, op, args))

and cmp_exp_as (tc : TypeCtxt.t) (c:Ctxt.t) (e:Ast.exp node) (t:Ll.ty) : Ll.operand * stream =
  let from_t, op, code = cmp_exp tc c e in
  if from_t = t then op, code
  else let res_id = gensym "cast" in
    Id res_id, code >:: I (res_id, Bitcast (from_t, op, t))

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.
 *)
and cmp_stmt (tc : TypeCtxt.t) (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =

  match stmt.elt with
  | Ast.Decl (id, init) ->
     let ll_ty, init_op, init_code = cmp_exp tc c init in
     let res_id = gensym id in
     let c' = Ctxt.add c id (Ptr ll_ty, Id res_id) in
     c', init_code 
         >:: E (res_id, Alloca ll_ty)
         >:: I ("",     Store (ll_ty, init_op, Id res_id))
     
  | Ast.Assn (lhs, rhs) ->
     let lhs_ty, lhs_op, lhs_code = cmp_exp_lhs tc c lhs in
     let rhs_ty = decode_ptr_ty lhs_ty in
     let rhs_op, rhs_code = cmp_exp_as tc c rhs rhs_ty in
     c, lhs_code >@ rhs_code >:: I ("", (Store (rhs_ty, rhs_op, lhs_op)))

  | Ast.If (guard, st1, st2) -> 
     let guard_ty, guard_op, guard_code = cmp_exp tc c guard in
     let then_code = cmp_block tc c rt st1 in
     let else_code = cmp_block tc c rt st2 in
     let lt, le, lm = gensym "then", gensym "else", gensym "merge" in
     c, guard_code 
        >:: T (Cbr (guard_op, lt, le))
        >:: L lt >@ then_code >:: T (Br lm)
        >:: L le >@ else_code >:: T (Br lm)
        >:: L lm

  (* CAST TASK: Fill in this case of the compiler to implement the 'if?' checked
     null downcast statement.  
       - check whether the value computed by exp is null, if so jump to
         the 'null' block, otherwise take the 'notnull' block

       - the identifier id is in scope in the 'notnull' block and so
         needs to be allocated (and added to the context)

       - as in the if-the-else construct, you should jump to the common
         merge label after either block
  *)
  (* TODO: test!!!!!!!!!! *)
  | Ast.Cast (rty, x, exp, notnull, null) ->

    let ll_ty = cmp_ty tc (TRef rty) (* Ptr *) in
    let exp_op, exp_code = cmp_exp_as tc c exp ll_ty in

    let cond_uid = gensym "cond" in

    let x_uid = gensym x in
    let c' = Ctxt.add c x (Ptr ll_ty (* double pointer *), Id x_uid) in

    let notnull_lbl = gensym "notnull" in
    let null_lbl = gensym "null" in
    let merge_lbl = gensym "merge" in

    c, exp_code
       >:: I (cond_uid, Icmp (Ne, ll_ty, exp_op, Null))
       >:: T (Cbr (Id cond_uid, notnull_lbl, null_lbl))
       >:: L notnull_lbl
       >:: E (x_uid, Alloca ll_ty)
       >:: I ("", Store (ll_ty, exp_op, Id x_uid))
       >@  cmp_block tc c' (* use new context *) rt notnull
       >:: T (Br merge_lbl)
       >:: L null_lbl
       >@  cmp_block tc c rt null
       >:: T (Br merge_lbl)
       >:: L merge_lbl

  | Ast.While (guard, body) ->
     let guard_ty, guard_op, guard_code = cmp_exp tc c guard in
     let lcond, lbody, lpost = gensym "cond", gensym "body", gensym "post" in
     let body_code = cmp_block tc c rt body  in
     c, [] 
        >:: T (Br lcond)
        >:: L lcond >@ guard_code >:: T (Cbr (guard_op, lbody, lpost))
        >:: L lbody >@ body_code  >:: T (Br lcond)
        >:: L lpost

  | Ast.For (inits, guard, after, body) ->
     let guard = match guard with Some e -> e | None -> no_loc (CBool true) in
     let after = match after with Some s -> [s] | None -> [] in
     let body = body @ after in
     let ds = List.map (fun d -> no_loc (Decl d)) inits in
     let stream = cmp_block tc c rt (ds @ [no_loc @@ Ast.While (guard, body)]) in
     c, stream

  | Ast.Ret None ->
     c, [T (Ret(Void, None))]

  | Ast.Ret (Some e) ->
     let op, code = cmp_exp_as tc c e rt in
     c, code >:: T(Ret (rt, Some op))

  | Ast.SCall (f, es) ->
     let _, op, code = cmp_call tc c f es in
     c, code

(* Compile a series of statements *)
and cmp_block (tc: TypeCtxt.t) (c: Ctxt.t) (rt: Ll.ty) (stmts: Ast.block) : stream =
  snd @@ List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt tc c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Construct the structure context for compilation.  We could reuse
   the H component from the Typechecker rather than recomputing this
   information here, but we do it this way to make the two parts of
   the project less interdependent.  *)
let get_struct_defns (p: Ast.prog) : TypeCtxt.t =
  List.fold_right (fun d ts ->
    match d with
    | Ast.Gtdecl { elt=(id, fs) } ->
        TypeCtxt.add ts id fs
    | _ -> ts) p TypeCtxt.empty


(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (tc: TypeCtxt.t) (c: Ctxt.t) (p: Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty tc ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C and Id's 
   for global function values). 
*)
let cmp_global_ctxt (tc: TypeCtxt.t) (c: Ctxt.t) (p: Ast.prog) : Ctxt.t =
  let gexp_ty c = function
    | Id id -> fst (Ctxt.lookup id c)
    | CStruct (t, cs) -> Ptr (Namedt t)
    | CNull r -> cmp_ty tc (TNullRef r)
    | CBool b -> I1
    | CInt i  -> I64
    | CStr s  -> Ptr (str_arr_ty s)
    | CArr (u, cs) -> Ptr (Struct [I64; Array(0, cmp_ty tc u)])
    | x -> failwith ( "bad global initializer: " ^ (Astlib.string_of_exp (no_loc x)))
  in
  List.fold_left (fun c -> function
    | Ast.Gvdecl { elt={ name; init } } ->
        Ctxt.add c name (Ptr (gexp_ty c init.elt), Gid name)
    | _ -> c) c p


(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.
 *)
let cmp_fdecl (tc: TypeCtxt.t) (c: Ctxt.t) (f: Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let {frtyp; args; body} = f.elt in
  let add_arg (s_typ, s_id) (c,code,args) =
    let ll_id = gensym s_id in
    let ll_ty = cmp_ty tc s_typ in
    let alloca_id = gensym s_id in
    let c = Ctxt.add c s_id (Ptr ll_ty, Ll.Id alloca_id)in
    c, [] 
       >:: E(alloca_id, Alloca ll_ty)
       >:: I("", Store(ll_ty, Id ll_id, Id alloca_id))
       >@ code,
    (ll_ty, ll_id)::args
  in
  let c, args_code, args = List.fold_right add_arg args (c,[],[]) in
  let ll_rty = cmp_ret_ty tc frtyp in
  let block_code = cmp_block tc c ll_rty body in
  let argtys, f_param = List.split args in
  let f_ty = (argtys, ll_rty) in
  let return_code =
    let return_val =
      match frtyp with
      | RetVoid -> None
      | RetVal TBool | RetVal TInt -> Some (Const 0L)
      | RetVal (TRef _) -> Some Null
      | RetVal (TNullRef _) -> Some Null
    in
    [T (Ret (ll_rty, return_val))]
  in
  let f_cfg, globals = cfg_of_stream (args_code >@ block_code >@ return_code) in
  {f_ty; f_param; f_cfg}, globals



(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.
*)
let rec cmp_gexp c (tc: TypeCtxt.t) (e: Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull r -> (cmp_ty tc (TNullRef r), GNull), []
  | CBool b -> (I1, (if b then GInt 1L else GInt 0L)), []
  | CInt i  -> (I64, GInt i), []
  | Id id   -> ((fst @@ Ctxt.lookup id c), GGid id), [] 

  | CStr s ->
    let gid = gensym "str" in
    let ll_ty = str_arr_ty s in
    (Ptr ll_ty, GGid gid), [gid, (ll_ty, GString s)]

  | CArr (ty, vals) ->

    let val_count = List.length vals in
    let arr_struct_gid = gensym "global_arr" in
    let arr_body_ty = Array (val_count, cmp_ty tc ty) in
    let actual_arr_struct_ty = Struct [I64; arr_body_ty] in
    let abstract_arr_struct_ty = cmp_rty tc (RArray ty) in

    let fold_val ((init_list: Ll.gdecl list), (more_gdecls: (Ll.gid * Ll.gdecl) list)) (e: Ast.exp node) =
      let init, more_gdecls' = cmp_gexp c tc e in
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

  (* STRUCT TASK (done): Complete this code that generates the global initializers for a struct value. *)
  (* TODO: test *)
  | CStruct (s_id, cs) ->
    let lookup_cs (f_id) = List.assoc f_id cs in
    let fields: Ast.field list = TypeCtxt.lookup s_id tc in

    (* Fold in the order of fields *)
    let fold_fields (init, more) ({fieldName = f_id}) =
      let init', more' = cmp_gexp c tc (lookup_cs f_id) in
      init' :: init,  (* reversed *)
      more @ more'
    in
    let init, more = List.fold_left fold_fields ([], []) fields in
    let init = List.rev init (* reverse *) in

    (* Double pointer *)
    let s_gid = gensym "global_struct" in
    let ll_s_ty = cmp_rty tc (RStruct s_id) in
    (Ptr ll_s_ty, GGid s_gid),
    (s_gid, (ll_s_ty, GStruct init)) :: more

  | _ -> failwith "bad global initializer"

(* Oat internals function context ------------------------------------------- *)
let internals =
  [ "oat_malloc",              Ll.Fun ([I64], Ptr I64)
  ; "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ; "oat_assert_not_null",     Ll.Fun ([Ptr I8], Void)
  ; "oat_assert_array_length", Ll.Fun ([Ptr I64; I64], Void)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins = List.map
    (fun (fname, ftyp) -> 
      let args, ret = cmp_fty TypeCtxt.empty ftyp in
      (fname, Ll.Fun (args, ret)))
    Typechecker.builtins


let tctxt_to_tdecls c =
  List.map (fun (i, l) -> i, Struct (List.map (fun f -> cmp_ty c f.ftyp) l)) c

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  let tc = get_struct_defns p in
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt tc init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt tc fc p in
  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c tc gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl tc c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
        | Ast.Gtdecl _ ->
            fs, gs
      ) p ([], [])
  in
  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = tctxt_to_tdecls tc; gdecls; fdecls; edecls }
