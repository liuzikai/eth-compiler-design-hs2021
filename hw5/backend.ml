(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge

(* Map LL binary opcodes to X86 opcodes *)
let compile_bop = function
  | Ll.Add  -> X86.Addq
  | Ll.Sub  -> X86.Subq
  | Ll.Mul -> X86.Imulq
  | Ll.Shl -> X86.Shlq
  | Ll.Lshr -> X86.Shrq
  | Ll.Ashr -> X86.Sarq
  | Ll.And -> X86.Andq
  | Ll.Or -> X86.Orq
  | Ll.Xor -> X86.Xorq

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  match n with
  | 0 -> Reg Rdi
  | 1 -> Reg Rsi
  | 2 -> Reg Rdx
  | 3 -> Reg Rcx
  | 4 -> Reg R08
  | 5 -> Reg R09
  | _ -> Ind3 (Lit (Int64.of_int ((n - 4) * 8)), Rbp)

let align_16 (n: int) : int =
  if (n mod 16) = 0 then n else ((n / 16 + 1) * 16)

(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt: ctxt) (dest: X86.operand) : Ll.operand -> ins = function
    | Null -> (Movq, [Imm (Lit 0L); dest])
    | Const c -> (Movq, [Imm (Lit c); dest])
    | Gid g -> (Leaq, [Ind3 (Lbl (Platform.mangle g), Rip); dest])
    | Id u -> (Movq, [lookup ctxt.layout u; dest])



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

let compile_call (ctxt: ctxt) (ret_uid: uid)
  ((ret_ty: ty), (f: Ll.operand), (params: (ty * Ll.operand) list)) : X86.ins list =

  (* Enforce 16-byte alignment if there is param on the stack by pushing a dummy 0 *)
  let param_count = List.length params in
  let param_count, params = (
    if param_count > 6 && (param_count mod 2) <> 0 then
      (param_count + 1), (params @ [(I64, Const 0L)])
    else
      param_count, params
  ) in

  (* Push parameters *)
  let rec pushing_params (ret: X86.ins list) (i: int) : X86.ins list = (
    if i = param_count then ret else (
      let _, ll_op = List.nth params i in

      (* Get the X86 operand (Imm or Reg) to be moved or pushed *)
      let x86_op = match ll_op with
        | Null -> Imm (Lit 0L)
        | Const c -> Imm (Lit c)
        (* Gid address will be computed into RAX (see below) *)
        | Gid g -> Reg Rax  (* use RAX as intermediate register *)
        | Id u -> lookup ctxt.layout u
      in

      (* Append Movq or Pushq to head so that params with larger i get moved or pushed first *)
      let ret = if i < 6 then
        (Movq, [x86_op; arg_loc i]) :: ret
      else
        (Pushq, [x86_op]) :: ret
      in

      (* For Gid, address needs to be computed with LEA *)
      let ret = match ll_op with
        | Gid g -> (compile_operand ctxt (Reg Rax) ll_op) :: ret
        | _ -> ret
      in

      (* Handle param on the right (to be moved or pushed before the current one) *)
      pushing_params ret (i + 1)
    )
  ) in
  let res = pushing_params [] 0  (* pushing first param is the last inst, so first param on the top *) in

  (* Call the function *)
  let f_gid = match f with
    | Gid gid -> gid
    | _ -> failwith "compile_call: function is not Gid"
  in
  let res = res @ [(Callq, [Imm (Lbl (Platform.mangle f_gid))])] in

  (* Store return value if needed *)
  let res = match ret_ty with
    | Void -> res
    | I1 | I8 | I64 | Ptr _ -> res @ [(Movq, [Reg Rax; lookup ctxt.layout ret_uid])]
    | _ -> failwith "compile_call: invalid ret_ty"
  in

  (* Pop parameters *)
  let res = (
    if param_count > 6 then
      res @ [(Addq, [Imm (Lit (Int64.of_int ((param_count - 6) * 8))); Reg Rsp])]
    else
      res
  ) in

  (* Final result *)
  res

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls: (tid * ty) list) (t: Ll.ty) : int =
  match t with
  | I1 | I64 | Ptr _ -> 8
  | Struct tys -> List.fold_left (fun ret ty -> ret + (size_ty tdecls ty)) 0 tys
  | Array (n, ty) -> n * (size_ty tdecls ty)
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)
  | Void | I8 | Fun (_, _) -> 0


let rec resolve_named_t (tdecls: (tid * ty) list) (t: Ll.ty) : Ll.ty =
  match t with
  | Namedt tid -> resolve_named_t tdecls (lookup tdecls tid)
  | _ -> t


(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt: ctxt) (uid: uid) (op: Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  (* Helper *)
  let size_ty_int64 (ty: ty) = Int64.of_int (size_ty ctxt.tdecls ty) in

  (* Decode t and put base address to RAX *)
  let t_ptr, base_addr = op in
  let t = match t_ptr with
    | Ptr ty -> ty
    | _ -> failwith "compile_gep: t_ptr is not Ptr"
  in
  let res: ins list = [
      compile_operand ctxt (Reg Rax) base_addr            (* RAX = base_addr      *)
  ] in

  (* Compute the first index *)
  let idx, path_from_1 = (
    match path with
    | [] -> failwith "compile_gep: path is empty"
    | h :: tl -> h, tl
  ) in
  let res = (
    match idx with
    (* If offset is Const 0, no need to modify RAX *)
    | Const 0L -> res
    | _ -> res @  [ compile_operand ctxt (Reg Rcx) idx    (* RCX = idx            *)
                  ; (Imulq, [Imm (Lit (size_ty_int64 t)); Reg Rcx])
                                                          (* RCX *= sizeof t      *)
                  ; (Addq, [Reg Rcx; Reg Rax])            (* RAX += RCX           *)
                  ]
  ) in

  (* Walk through t and path together *)
  let rec walk_through (ret: ins list) (t: ty) (path: Ll.operand list) : ins list = (
    match path with
    | [] -> ret
    | idx :: remaining_path -> (
      match t with

      (* Handle alias *)
      | Namedt tid -> walk_through ret (lookup ctxt.tdecls tid) path

      (* Handle struct *)
      | Struct elems -> (

        (* Walk into the struct *)
        let next_ret, next_t = (
          match idx with
          (* If offset is Const 0, no need to modify RAX *)
          | Const 0L -> ret (* next_ret *), List.nth elems 0 (* next_t *)
          | Const c -> (
            let rec sum_sizes (ret: int64) (i: int64) (elems: ty list) : int64 =
              if i = 0L then ret else
              match elems with
              | [] -> failwith "compile_gep: offset out-of-bound for Struct t"
              | elem :: tl -> sum_sizes (Int64.add ret (size_ty_int64 elem))
                                        (Int64.pred i)
                                        tl
            in
            let offset = sum_sizes 0L c elems in
            ret @ [(Addq, [Imm (Lit offset); Reg Rax])],  (* RAX += sum of sizes  *)
            List.nth elems (Int64.to_int c) (* next_t *)
          )
          | _ -> failwith "compile_gep: offset not Const for Struct t"
        ) in
        walk_through next_ret next_t remaining_path
      )

      (* Handle array *)
      | Array (n, elem) -> (
        let next_ret, next_t = (
          match idx with
          (* If offset is Const 0, no need to modify RAX *)
          | Const 0L -> ret (* next_ret *), elem (* next_t *)
          | _ -> (
            ret @ [ compile_operand ctxt (Reg Rcx) idx    (* RCX += idx           *)
                  ; (Imulq, [Imm (Lit (size_ty_int64 elem)); Reg Rcx])
                                                          (* RCX *= sizeof elem   *)
                  ; (Addq, [Reg Rcx; Reg Rax])            (* RAX += RCX           *)
                  ] (* next_ret *),
            elem (* next_t *)
          )
        ) in
        walk_through next_ret next_t remaining_path
      )

      (* Invalid t *)
      | _ -> failwith "compile_gep: invalid path for not Struct or Array type"

    ) (* end of idx :: remaining_path *)
  ) (* end of walk_through *) in
  let res = walk_through res t path_from_1 in

  (* Store result to uid *)
  res @ [(Movq, [Reg Rax; lookup ctxt.layout uid])]


(* compiling instructions  -------------------------------------------------- *)

let compile_binop (ctxt: ctxt) (uid: uid) (bop, ty, op1, op2) : X86.ins list =
  (* Use caller-saved register: RAX, RCX (sarq/shlq/shrq can only use RCX as AMT) *)
  [ compile_operand ctxt (Reg Rax) op1
  ; compile_operand ctxt (Reg Rcx) op2
  ; (compile_bop bop, [Reg Rcx; Reg Rax])  (* result in RAX *)
  ; (Movq, [Reg Rax; lookup ctxt.layout uid])  (* store RAX to the stack *)
  ]


let compile_alloca (ctxt: ctxt) (uid: uid) (ty: ty) : X86.ins list =
  let ty_size = size_ty ctxt.tdecls ty in
  (* Enforce 16-byte alignment *)
  [ (Subq, [Imm (Lit (Int64.of_int (align_16 ty_size))); Reg Rsp])
  ; (Movq, [Reg Rsp; lookup ctxt.layout uid])
  ]


let compile_load (ctxt: ctxt) (uid: uid) (ty, op) : X86.ins list =
 [ compile_operand ctxt (Reg Rax) op
 ; (Movq, [Ind2 Rax; Reg Rax])
 ; (Movq, [Reg Rax; lookup ctxt.layout uid])
 ]

let compile_store (ctxt:ctxt) (uid:uid) (ty, op1, op2) : X86.ins list =
 [ compile_operand ctxt (Reg Rax) op1
 ; compile_operand ctxt (Reg Rcx) op2
 ; (Movq, [Reg Rax; Ind2 Rcx])
 ]

let compile_icmp (ctxt:ctxt) (uid:uid) (cnd, ty, op1, op2) : X86.ins list =
	[ compile_operand ctxt (Reg Rax) op1
	; compile_operand ctxt (Reg Rcx) op2
	; (Cmpq, [Reg Rcx; Reg Rax])  (* flags <- op1 - op2 *)
	; (Movq, [Imm (Lit 0L); Reg Rax]) (* does not change flags *)
	; (Set (compile_cnd cnd), [Reg Rax])
	; (Movq, [Reg Rax; lookup ctxt.layout uid])
	]

let compile_bitcast (ctxt: ctxt) (uid: uid) (t1, op, t2) : X86.ins list =
 [ compile_operand ctxt (Reg Rax) op
 ; (Movq, [Reg Rax; lookup ctxt.layout uid])
 ]

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt: ctxt) ((uid: uid), (i: Ll.insn)) : X86.ins list =
  match i with
  | Binop (bop, ty, op1, op2) -> compile_binop ctxt uid (bop, ty, op1, op2)
  | Alloca ty -> compile_alloca ctxt uid ty
  | Load (ty, op) -> compile_load ctxt uid (ty, op)
  | Store (ty, op1, op2) -> compile_store ctxt uid (ty, op1, op2)
  | Icmp (cnd, ty, op1, op2) -> compile_icmp ctxt uid (cnd, ty, op1, op2)
  | Call (ret_ty, f, params) -> compile_call ctxt uid (ret_ty, f, params)
  | Bitcast (t1, op, t2) -> compile_bitcast ctxt uid (t1, op, t2)
  | Gep (ty, op, path) -> compile_gep ctxt uid (ty, op) path


(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn: string) (l: string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_ret (ctxt: ctxt) (ty, optional_op) : ins list =
	let ret = [ Movq, [Reg Rbp; Reg Rsp]
            ; Popq, [Reg Rbp]
            ; (Retq, [])
            ] in
    match optional_op with
    | Some op -> (compile_operand ctxt (Reg Rax) op) :: ret
    | None -> ret

let compile_br (ctxt: ctxt) (fn: string) (l) : ins list=
	[(Jmp, [Imm (Lbl (mk_lbl fn l))])]

let compile_cbr (ctxt: ctxt) (fn: string) (op, l1, l2) =
	[ compile_operand ctxt (Reg Rax) op
	; (Cmpq, [Imm (Lit 1L); Reg Rax])
	; (J Eq, [Imm (Lbl (mk_lbl fn l1))])
	; (Jmp, [Imm (Lbl (mk_lbl fn l2))])
	]

let compile_terminator (fn: string) (ctxt: ctxt) ((_: uid), (t: Ll.terminator)) : ins list =
  match t with
  | Ret (ty, optional_op) -> compile_ret ctxt (ty, optional_op)
  | Br l -> compile_br ctxt fn (l)
	| Cbr (op, l1,l2) -> compile_cbr ctxt fn (op, l1, l2)


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn: string) (ctxt: ctxt) (blk: Ll.block) : ins list =
  let fold_insn (ret: ins list) ((uid: uid), (insn: insn)) : ins list =
    ret @ (compile_insn ctxt (uid, insn))
  in
  (List.fold_left fold_insn [] blk.insns) @ (compile_terminator fn ctxt blk.term)

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let stack_layout (args: uid list) ((block, lbled_blocks): cfg) : layout =
  (* LLVM lite does not allow locals to hold structured data, only 8-bytes data *)
  let mk_slot : unit -> X86.operand = (
      let offset = ref 0L in
      fun () -> offset := (Int64.sub !offset 8L) (* offset -= 8 *); (Ind3 (Lit !offset, Rbp))
  ) in

  (* Fold left functions *)
  let fold_uid (ret: layout) (u: uid) : layout = (u, mk_slot ()) :: ret in
  let fold_uid_insn_tuple (ret: layout) ((u, _): (uid * insn)) : layout = fold_uid ret u in
  let fold_uid_terminator_tuple (ret: layout) ((u, _): (uid * terminator)) : layout = fold_uid ret u in
  let fold_block (ret: layout) (b) = (
    let t = List.fold_left fold_uid_insn_tuple ret b.insns in
    fold_uid_terminator_tuple t b.term
  ) in
  let fold_lbl_block (ret: layout) (_, b) = fold_block ret b in

  (* Process args *)
  let res = List.fold_left fold_uid [] args in

  (* Process block *)
  let res = fold_block res block in

  (* Process lbled_blocks *)
  let res = List.fold_left fold_lbl_block res lbled_blocks in

  (* Final result *)
  List.rev res

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls: (tid * ty) list) (name: string) ({ f_ty; f_param; f_cfg }: fdecl) : prog =
  let layout = stack_layout f_param f_cfg in
  let ctxt = { tdecls = tdecls; layout = layout } in
  let first_block, lbled_block_list = f_cfg in

  (* Compile function entry *)
  let entry: X86.ins list = [
    Pushq, [Reg Rbp]
  ; Movq, [Reg Rsp; Reg Rbp]
  (* Enforce 16-byte alignment *)
  ; Subq, [Imm (Lit (Int64.of_int (align_16 ((List.length layout) * 8)))); Reg Rsp]
  ] in

  (* Store argument to the stack *)
  let compile_storing_param (i: int) (param: uid) : X86.ins list =
    [ Movq, [arg_loc i; Reg Rax]  (* Movq cannot have two Ind operands *)
    ; Movq, [Reg Rax; lookup layout param]
    ]
  in
  let rec compile_storing_params (ret: X86.ins list) (i: int) (params: uid list) : X86.ins list =
    match params with
    | [] -> ret
    | h :: tl -> compile_storing_params (ret @ (compile_storing_param i h)) (i + 1) tl
  in
  let entry = compile_storing_params entry 0 f_param in

  (* Compile first block *)
  let res: elem list = [
    Asm.gtext (Platform.mangle name) (entry @ (compile_block name ctxt first_block))
  ] in

  (* Compile lbl_blocks *)
  let fold_lbl_block (ret: elem list) ((lbl: lbl), (block: block)) =
    compile_lbl_block name lbl ctxt block :: ret  (* reversed *)
  in
  List.rev (List.fold_left fold_lbl_block res lbled_block_list)



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
