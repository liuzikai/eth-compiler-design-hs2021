open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c: Tctxt.t) (t1: Ast.ty) (t2: Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt | TBool, TBool -> true  (* SUB_SUB_INT & SUB_SUB_BOOL *)
  | TNullRef r1, TNullRef r2           (* SUB_SUB_NREF *)
  | TRef r1, TRef r2                   (* SUB_SUB_REF *)
  | TRef r1, TNullRef r2               (* SUB_SUB_NRREF *)
    -> subtype_ref c r1 r2
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c: Tctxt.t) (t1: Ast.rty) (t2: Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true  (* SUB_SUBRSTRING *)
  | RArray a1, RArray a2 -> (a1 = a2)  (* SUB_SUBRARRAY *)

  (* SUB_SUBRSTRUCT *)
  | RStruct id1, RStruct id2 -> (
    let fields1 = lookup_struct id1 c in
    let fields2 = lookup_struct id2 c in
    let rec is_prefix (fields: Ast.field list) (prefix: Ast.field list) : bool =
      match fields, prefix with
      | f :: fs, p :: ps -> if (f = p) then is_prefix fs ps else false
      | _, [] -> true
      | [], _ -> false
    in
    is_prefix fields1 fields2
  )

  (* SUB_SUBRFUNT *)
  | RFun (args1, rt1), RFun (args2, rt2) -> (
    let rec arg_subtype (args: ty list) (args': ty list) : bool =
      match args, args' with
      | arg :: tl, arg' :: tl' -> if (subtype c arg' arg) then arg_subtype tl tl' else false
      | [], [] -> true
      | _ -> false
    in
    if (arg_subtype args1 args2) then (subtype_ret_ty c rt1 rt2) else false
  )
  | _ -> false

(* Decides whether H |-rt rt1 <: rt2 *)
and subtype_ret_ty (c: Tctxt.t) (t1: Ast.ret_ty) (t2: Ast.ret_ty) : bool =
  match t1, t2 with
  | RetVoid, RetVoid -> true  (* SUB_SUBRETSVOID *)
  | RetVal t1, RetVal t2 -> subtype c t1 t2  (* SUB_SUBRETRTTYP *)
  | _ -> false


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l: 'a Ast.node) (tc: Tctxt.t) (t: Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef rty | TNullRef rty -> typecheck_rty l tc rty

(* Decides whether H |-r ref *)
and typecheck_rty (l: 'a Ast.node) (tc: Tctxt.t) (t: Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray t -> typecheck_ty l tc t
  | RStruct id -> (
    match lookup_struct_option id tc with
    | Some _ -> ()
    | None -> type_error l ("struct " ^ id ^ " is not defined")
  )
  | RFun (args, rt) -> (
    let rec check_args = function
      | h :: tl -> typecheck_ty l tc h; check_args tl
      | [] -> ()
    in
    check_args args; typecheck_ret_ty l tc rt
  )

(* Decides whether H |-rt rt *)
and typecheck_ret_ty (l: 'a Ast.node) (tc: Tctxt.t) (t: Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l tc t

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c: Tctxt.t) (e: Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull rty -> typecheck_rty e c rty; TNullRef rty  (* TYP_NULL *)
  | CBool _ -> TBool  (* TYP_BOOL *)
  | CInt _ -> TInt  (* TYP_INT *)
  | CStr _ -> TRef RString  (* TYP_STRING *)

  (* TYP_LOCAL & TYP_GLOBAL *)
  | Id id -> (
    match lookup_local_option id c with
    | Some t -> t
    | None -> (
      match lookup_global_option id c with
      | Some t -> t
      | _ -> type_error e ("unknown identifier " ^ id)
    )
  )

  (* TYP_CARR *)
  | CArr (t, exps) -> (
    typecheck_ty e c t;
    let check_exp exp = (if not (subtype c (typecheck_exp c exp) t) then
        type_error e ("invalid type of array initializer value")
    ) in
    List.iter check_exp exps;
    TRef (RArray t)
  )

  (* TYP_NEWARRAY *)
  | NewArr ((t: ty), exp1, (x: id), exp2) -> (
    typecheck_ty e c t;
    if (typecheck_exp c exp1) <> TInt then
      type_error e ("new array expression expects numerical length")
    else if (lookup_local_option x c) <> None then
      type_error e ("identifier " ^ x ^ " is already defined in the local context")
    else
      let t' = typecheck_exp (add_local c x TInt) exp2 in
      if (subtype c t' t) = false then
        type_error e ("initializer expression does not match the array type")
      else
        TRef (RArray t)
  )

  (* TYP_INDEX *)
  | Index (exp1, exp2) -> (
    match typecheck_exp c exp1 with
    | TRef (RArray t) -> (
      if (typecheck_exp c exp2) = TInt then t else type_error e ("index is not an integer")
    )
    | _ -> type_error e ("not an array")
  )

  (* TYP_LENGTH *)
  | Length (exp) -> (
    match typecheck_exp c exp with
    | TRef (RArray _) -> TInt
    | _ -> type_error e ("not an array")
  )

  (* TYP_STRUCTEX *)
  | CStruct (s, inits) -> (
     match lookup_struct_option s c with
     | Some fields -> (
        if not (List.length fields = List.length inits) then
          type_error e ("number of fields does not match")
        else
          let check_init ((id, exp): id * exp node) (field: Ast.field) : unit =
            if id <> field.fieldName then
              type_error exp ("unexpected field " ^ id)
            else if not (subtype c (typecheck_exp c exp) field.ftyp) then
              type_error exp ("unexpected type for field " ^ id)
          in
          List.iter2 check_init
                    (List.sort (fun (id1, _) (id2, _) -> String.compare id1 id2) inits)
                    (List.sort (fun f1 f2 -> String.compare f1.fieldName f2.fieldName) fields);
          TRef (RStruct s)
     )
     | None -> type_error e ("struct " ^ s ^ " is not defined")
  )

  (* TYP_FIELD *)
  | Proj (exp, x) -> (
    match typecheck_exp c exp with
    | TRef (RStruct t) -> (
      match lookup_field_option t x c with
      | Some t -> t
      | None -> type_error e ("field " ^ x ^ " undefined")
    )
    | _ -> type_error e ("not a struct")
  )

  (* TYP_CALL *)
  | Call (exp, args) -> (
    match typecheck_exp c exp with
    | TRef (RFun (t_args, RetVal t)) -> (
      if not (List.length t_args = List.length args) then
        type_error e ("number of arguments does not match")
      else
        let check_exp arg t_arg =
          if not (subtype c (typecheck_exp c arg) t_arg)
          then type_error e ("invalid type of argument value")
        in
        List.iter2 check_exp args t_args;
        t
    )
    | _ -> type_error e ("not a function")
  )

  | Bop (bop, exp1, exp2) -> (
    let t1 = typecheck_exp c exp1 in
    let t2 = typecheck_exp c exp2 in
    match bop with
    | Eq | Neq -> (
      (* TYP_EQ & TYP_NEQ *)
      if not (subtype c t1 t2 && subtype c t2 t1)
      then type_error e ("values of different types are compared")
      else TBool
    )
    | _ -> (
      (* TYP_BOP *)
      let (t1', t2', t) = typ_of_binop bop in
      if (t1 <> t1') || (t2 <> t2')
      then type_error e ("invalid type of bop operand")
      else t
    )
  )

  (* TYP_UOP *)
  | Uop (uop, exp) -> (
    let (_, t) = typ_of_unop uop in
    if typecheck_exp c exp <> t
    then type_error e ("invalid type of uop operand")
    else t
  )


(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entire conditional statement might
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)

(* H;G;L1 |- vdecl => L2

   Input s for error reporting context. Placed as the first argument so that
   (typecheck_vdecl s) is a function application that can be used for
   List.fold_left.
*)
let typecheck_vdecl (s: Ast.stmt node) (tc: Tctxt.t) ((id, exp): Ast.vdecl) : Tctxt.t =
  let t = typecheck_exp tc exp in
  if lookup_local_option id tc <> None then
    type_error s ("identifier " ^ id ^ " is already defined in the local context")
  else
    add_local tc id t


(* H;G;L0 |- vdecls => Li *)
let typecheck_vdecls (s: Ast.stmt node) (tc: Tctxt.t) (vdecls: Ast.vdecl list) : Tctxt.t =
  List.fold_left (typecheck_vdecl s) tc vdecls


(* H;G;L1;rt |- stmt => L2;returns *)
let rec typecheck_stmt (tc: Tctxt.t) (s: Ast.stmt node) (to_ret: ret_ty) : Tctxt.t * bool =
  match s.elt with

  (* TYP_ASSN *)
  | Assn (lhs, exp) -> (
    (* Check lhs in L or lhs is not a global function id *)
    let _ = match lhs.elt with
    | Id id -> (
      if (lookup_local_option id tc) <> None then ()
      else match (lookup_global_option id tc) with
        (* TODO: really? test cases? *)
        | Some (TRef RFun _) | Some (TNullRef RFun _) ->
          type_error s ("cannot assign to function identifier " ^ id)
        | _ -> ()
    )
    | _ -> ()
    in
    (* Check for remaining rules *)
    let t = typecheck_exp tc lhs in
    let t' = typecheck_exp tc exp in
    if (subtype tc t' t) = false then
      type_error s ("assignment types unmatched")
    else
      tc (* L *), false (* might not return *)
  )

  (* TYP_STMTDECL *)
  | Decl vdecl -> (typecheck_vdecl s tc vdecl) (* L2 *), false (* might not return *)

  (* TYP_SCALL *)
  | SCall (exp, args (* exp1 ... expn *)) -> (
    match typecheck_exp tc exp with
    (* Check for void-return function *)
    | TRef (RFun (ts (* t1 ... tn *), RetVoid)) -> (
      (* Check the number of arguments *)
      let cnt = List.length ts in
      let cnt' = List.length args in
      if cnt <> cnt' then
        type_error s ("expecting " ^ (string_of_int cnt) ^ " argument(s) but " ^ (string_of_int cnt') ^ " are given")
      else
        (* Check each argument *)
        let check_arg (t1: Ast.ty) (exp1: Ast.exp node) = (
          let t1' = typecheck_exp tc exp1 in
          if not (subtype tc t1' t1) then type_error s ("invalid argument type")
        ) in
        List.iter2 check_arg ts args;
        tc (* L *), false (* might not return *)
    )
    | _ -> type_error s ("not a void-return function")
  )

  (* TYP_IF *)
  | If (exp, block1, block2) -> (
    if (typecheck_exp tc exp) <> TBool then
      type_error s ("if condition does not have type bool")
    else
      let r1 = typecheck_block tc block1 to_ret in
      let r2 = typecheck_block tc block2 to_ret in
      tc (* L *), r1 && r2 (* might not return *)
  )

  (* TYP_IFQ *)
  | Cast (rty (* ref *), id, exp, block1, block2) -> (
    match typecheck_exp tc exp with
    | TNullRef ref' -> (
      if not (subtype_ref tc ref' rty) then
        type_error s ("if? expression cannot be casted to the given type")
      else
        let tc' = add_local tc id (TRef rty) in
        let r1 = typecheck_block tc' block1 to_ret in
        let r2 = typecheck_block tc' block2 to_ret in
        tc (* L *), r1 && r2 (* might not return *)
    )
    | _ -> type_error s ("if? expression does not have type ref?")
  )

  (* TYP_WHILE *)
  | While (exp, block) -> (
    if (typecheck_exp tc exp <> TBool) then
      type_error s ("while condition does not have type bool")
    else
      let _ = typecheck_block tc block to_ret in
      tc (* L *), false (* might not return*)
  )

  (* TYP_ FOR *)
  | For (vdecls, exp_opt, stmt_opt, block) -> (
    let tc_with_l2 = typecheck_vdecls s tc vdecls in
    let _ = match exp_opt with
      | Some exp -> if (typecheck_exp tc_with_l2 exp <> TBool) then
                      type_error s ("for loop condition does not have type bool")
      | None -> ()
    in
    let _ = match stmt_opt with
      | Some stmt -> if (snd (typecheck_stmt tc_with_l2 stmt to_ret)) then
                        type_error s ("for loop stmt definitely returns")
      | None -> ()
    in
    let _ = typecheck_block tc_with_l2 block to_ret in
    tc (* L *), false (* might not return*)
  )

  (* TYP_ RETT *)
  | Ret Some exp -> (
    match to_ret with
    | RetVal t -> if not (subtype tc (typecheck_exp tc exp) t) then
                    type_error s ("ret val error")
                  else tc (* L *), true (* definitely returns  *)
    | _ -> type_error s ("ret val error")
  )

  (* TYP_RETVOID *)
  | Ret None -> (
    if to_ret <> RetVoid then
        type_error s ("ret void error")
    else tc (* L *), true (* definitely returns  *)
  )

(* H;G;L;rt |- block;returns, TYP_BLOCK *)
and typecheck_block (tc: Tctxt.t) (b: Ast.block) (to_ret: ret_ty) : bool =
  let _, must_ret = typecheck_stmts tc b to_ret in must_ret (* drop tc' *)

(* H;G;L0;rt |-ss stmt1 .. stmtn => Ln;returns, TYP_STMTS *)
and typecheck_stmts (tc: Tctxt.t) (b: Ast.stmt node list) (to_ret: ret_ty) : Tctxt.t * bool =
  match b with
  | [] -> tc, false  (* only when b is empty at entering *)
  | s :: b' -> (
    let tc', must_ret = typecheck_stmt tc s to_ret in
    match b' with
    | [] -> tc', must_ret  (* no more stmt, here is the last *)
    | _ -> (
      if must_ret
      then type_error s ("block returns early (dead code)")
      else typecheck_stmts tc' b' to_ret
    )
  )


(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elsewhere in the type system.
 *)

let typecheck_tdecl (tc: Tctxt.t) (id) (fs: field list) (l: 'a Ast.node) : unit =
  (* Helper function to look for duplicate field names *)
  let rec check_dups fs =
    match fs with
    | [] -> false
    | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t
  in
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)
let typecheck_fdecl (tc: Tctxt.t) (f: Ast.fdecl) (l: 'a Ast.node) : unit =
  let rec process_args (tc: Tctxt.t) (args: (ty * id) list) : Tctxt.t =
    match args with
    | [] -> tc
    | (ty, id) :: t -> (
      if List.exists (fun (ty', id') -> (id' = id)) t then
        type_error l ("Repeated arguments in " ^ f.fname)
      else
        process_args (add_local tc id ty) t
    )
  in
  let tc' = process_args tc f.args in
  let must_ret = typecheck_block tc' f.body f.frtyp in
  if not must_ret then
    type_error l ("function " ^ f.fname ^ " may not return")

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p: Ast.prog) : Tctxt.t =
  let rec create_struct_ctxt_aux (tc: Tctxt.t) (p: Ast.prog) : Tctxt.t =
    match p with
    | [] -> tc
    | (Gtdecl ({elt = (id, fs)} as l)) :: p' -> (
      if (lookup_struct_option id tc) <> None then
         type_error l ("Repeated struct definition " ^ id)
      else
        create_struct_ctxt_aux (add_struct tc id fs) p'
    )
    | _ :: p' -> create_struct_ctxt_aux tc p'
  in
  create_struct_ctxt_aux Tctxt.empty p

let rec create_function_ctxt (tc: Tctxt.t) (p: Ast.prog) : Tctxt.t =
  (* Add user-defined functions *)
  match p with
  | [] -> tc
  | (Gfdecl ({elt = f} as l)) :: p' -> (
    (* TYP_FTYP *)
    let _ = typecheck_ret_ty l tc f.frtyp in
    let arg_tys = List.map (fun (ty, id) -> typecheck_ty l tc ty; ty) f.args in
    let t = TRef (RFun (arg_tys, f.frtyp)) in
    (* TYP_FFDECL remaining *)
    if (lookup_global_option f.fname tc) <> None then
      type_error l ("Repeated global identifier " ^ f.fname)
    else
      create_function_ctxt (add_global tc f.fname t) p'
  )
  | _ :: p' -> create_function_ctxt tc p'


let create_global_ctxt (tc: Tctxt.t) (p: Ast.prog) : Tctxt.t =
  let fold_gdecl (ret_tc: Tctxt.t) (d: Ast.decl) : Tctxt.t =
    match d with
    | Gvdecl ({elt = g} as l) -> (
      (* TODO: test this *)
      let t = typecheck_exp tc (* NOTE: original tc without global variables*) g.init in
      if (lookup_global_option g.name ret_tc) <> None then
        type_error l ("Repeated global identifier " ^ g.name)
      else
        add_global ret_tc g.name t
    )
    | _ -> ret_tc
  in
  List.fold_left fold_gdecl tc p


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p: Ast.prog) : unit =
  let sc = create_struct_ctxt p in

  (* Add built-in functions *)
  let fold_buildin (tc) (id, (args, ret_ty)) =
    add_global tc id (TRef (RFun (args, ret_ty)))
  in
  let bfc = List.fold_left fold_buildin sc builtins in

  let fc = create_function_ctxt bfc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
