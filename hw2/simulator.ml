(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the
   course web pages, for a detailed explanation of the instuction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instuctions' that take up eight bytes for the purposes of
   layout.
   The symbolic bytes abstract away from the details of how
   instuctions are represented in memory.  Each instuction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instuction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.
   For example, the two-instuction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]
   is represented by the following elements of the mem array (starting
   at address 0x400000):
       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instuction *)
           | InsFrag            (* 2nd - 8th bytes of an instuction *)
           | Byte of char       (* non-instuction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instuction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) ->
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:
     [if !debug_simulator then print_endline @@ string_of_ins u; ...]
*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool =
  fun x -> begin match x with
    | Eq -> fz
    | Neq -> not fz
    | Lt -> fs != fo
    | Le -> (fs != fo) || fz
    | Gt -> not ((fs != fo) || fz)
    | Ge -> fs = fo
  end

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  (* if the address is in the legal address space *)
  if addr >= mem_bot && addr < mem_top then
    (* map it into the location with (addr - lowest) *)
    Some (Int64.to_int (Int64.sub addr mem_bot))
  (* else return None *)
  else None

(* Wrapper function for map_addr *)
let map_addr_or_seg_fault (addr: quad) : int =
  match map_addr addr with
    | Some ret -> ret
    | None -> raise X86lite_segfault

(* Simulates one step of the machine:
    - fetch the instuction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instuction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let get_ind_mem_addr (m: mach) (opd: operand) : int64 =
  match opd with
  | Ind1 Lit l -> l
  | Ind2 r -> m.regs.(rind r)
  | Ind3 (Lit l, r) -> Int64.add m.regs.(rind r) l
  | _ -> invalid_arg "get_opd_mem_addr: expecting Ind operand"

let get_opd_val (m: mach) (opd: operand) : int64 =
  match opd with
  | Imm Lit l -> l
  | Reg r -> m.regs.(rind r)
  | _ -> int64_of_sbytes (Array.to_list (
      Array.sub m.mem (map_addr_or_seg_fault (get_ind_mem_addr m opd)) 8
    ))

let update_reg_or_mem (m: mach) (opd: operand) (new_val: int64) : unit =
  (* debug*) if false then print_endline("new_val = " ^ Int64.to_string new_val);
	match opd with
  | Imm _ -> failwith "update_reg_or_mem: cannot write to Imm"
  | Reg r -> m.regs.(rind r) <- new_val
  | _ -> (
    let mem_addr = get_ind_mem_addr m opd in
    let mem_idx = map_addr_or_seg_fault mem_addr in
    let val_sbytes = Array.of_list (sbytes_of_int64 new_val) in
    Array.blit val_sbytes 0 m.mem mem_idx 8
  )

let update_flags (f: flags) (result: int64) (fo: bool): unit =
	f.fo <- fo;
	f.fs <- (result < 0L);
	f.fz <- (result = 0L)

let arith_inst (m: mach) (op: opcode) (args: operand list): unit =
  let op1: operand = List.nth args 0 in
  let op1_val: int64 = get_opd_val m op1 in
  let dest, result = match op with
    (* Single operand *)
    | Negq -> (op1, Int64_overflow.neg op1_val)
    | Incq -> (op1, Int64_overflow.succ op1_val)
    | Decq -> (op1, Int64_overflow.pred op1_val)
    (* Two operands *)
    | _ -> (
      let op2: operand = List.nth args 1 in
      let op2_val: int64 = get_opd_val m op2 in
      match op with
      | Addq  -> (op2, Int64_overflow.add op2_val op1_val)
      | Subq  -> (op2, Int64_overflow.sub op2_val op1_val)
      | Imulq -> (op2, Int64_overflow.mul op2_val op1_val)
      | _ -> failwith "arith_inst: unexpected match"
      (* here is not reached *)
    )
  in
  update_reg_or_mem m dest result.value;
  (* Set cnd flags based on result *)
	update_flags m.flags result.value result.overflow;
	(* debug *) if false then print_endline("O S Z = "
	                            ^ (if m.flags.fo then "true " else "false ")
	                            ^ (if m.flags.fs then "true " else "false ")
	                            ^ (if m.flags.fz then "true " else "false "))


let logic_inst (m: mach) (op: opcode) (args: operand list): unit =
	let op1: operand = List.nth args 0 in
	let op1_val: int64 = get_opd_val m op1 in
	let dest, result = match op with
		| Notq -> (op1, Int64.lognot op1_val)
		| _ -> (
			let op2: operand = List.nth args 1 in
			let op2_val: int64 = get_opd_val m op2 in
			match op with
			| Andq -> (op2, Int64.logand op2_val op1_val)
			| Orq -> (op2, Int64.logor op2_val op1_val)
			| Xorq -> (op2, Int64.logxor op2_val op1_val)
			| _ -> failwith "logic_inst: unexpected match"
			)
	in
	update_reg_or_mem m dest result;
	(* Set cnd flags based on result *)
	update_flags m.flags result false

let bit_manipulation_inst (m: mach) (op: opcode) (args: operand list): unit =
	match op with
	| Set cc -> let op = List.nth args 0 in
							let op_val = get_opd_val m op in
							let clear_val = Int64.logand op_val 0x00L in
							if interp_cnd m.flags cc
							then update_reg_or_mem m op (Int64.add clear_val 1L)
							else update_reg_or_mem m op (Int64.add clear_val 0L)
	| _ -> let amt = List.nth args 0 in
				 let amt_val = Int64.to_int (get_opd_val m amt) in
				 let dest = List.nth args 1 in
				 let dest_val = get_opd_val m dest in
				 match op with
				 | Sarq -> let result = Int64.shift_right dest_val amt_val in
									 update_reg_or_mem m dest result;
									 if amt_val = 0 then () else update_flags m.flags result false
				 | Shlq -> let result = Int64.shift_left dest_val amt_val in
									 update_reg_or_mem m dest result;
									 if amt_val = 0 then () else update_flags m.flags result true
				 | Shrq -> let result = Int64.shift_right_logical dest_val amt_val in
									 update_reg_or_mem m dest result;
									 if amt_val = 0 then () else update_flags m.flags result (result < 0L)

let data_move_inst (m: mach) (op: opcode) (args: operand list) : unit =
	match op with
	| Leaq -> let ind_addr = get_ind_mem_addr m (List.nth args 0) in
            update_reg_or_mem m (List.nth args 1) ind_addr;
	| Movq -> let src_val = get_opd_val m (List.nth args 0) in
            update_reg_or_mem m (List.nth args 1) src_val
	| Pushq -> let src_val = get_opd_val m (List.nth args 0) in
             m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
             update_reg_or_mem m (Ind2 Rsp) src_val;
	| Popq -> let mem_val = get_opd_val m (Ind2 Rsp) in
            update_reg_or_mem m (List.nth args 0) mem_val;
            m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L;
	| _ -> failwith "data_move_inst: unexpected op"
	(* here is not reached *)

let ctrl_cond_inst (m: mach) (op: opcode) (args: operand list): unit =
	match op with
	| Retq -> data_move_inst m Popq [Reg Rip];
	| _ -> (
	  let op1: operand = List.nth args 0 in
    let op1_val: int64 = get_opd_val m op1 in
    match op with
    | Jmp -> 	m.regs.(rind Rip) <- op1_val;
    | Callq -> data_move_inst m Pushq [Reg Rip];
               m.regs.(rind Rip) <- op1_val;
    | J cc -> if interp_cnd m.flags cc
              then m.regs.(rind Rip) <- op1_val
    | _ -> let op2 = List.nth args 1 in
           let op2_val = get_opd_val m op2 in
           match op with
          | Cmpq -> let result = Int64_overflow.sub op2_val op1_val in
                    m.flags.fo <- result.overflow;
                    m.flags.fs <- (result.value < 0L);
                    m.flags.fz <- (result.value = 0L);
          | _ -> failwith "ctrl_cond_inst: unexpected op"
	)

let step (m:mach) : unit =
	let rip_val = m.regs.(rind Rip) in
  let inst = m.mem.(map_addr_or_seg_fault rip_val) in
  m.regs.(rind Rip) <- Int64.add rip_val 8L;
	match inst with
  | InsB0 (op, args) -> (
    match op with
     | Negq | Addq | Subq | Imulq | Incq | Decq -> arith_inst m op args
     | Notq | Andq | Orq | Xorq -> logic_inst m op args
     | Sarq | Shlq | Shrq | Set _ -> bit_manipulation_inst m op args
     | Leaq | Movq | Pushq | Popq -> data_move_inst m op args
     | Cmpq | Jmp | Callq | Retq | J _ -> ctrl_cond_inst m op args
    )
  | _ -> failwith "Here is the problem"


(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the
   machine halts. *)
let run (m:mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl


(* Separate text and data segments and order them into two list.
   Input: p - a program
   Output: list of text segments, list of data segments
 *)
let separate_segments (p: prog) : (prog * prog) =
  (* Tail recursion implementation *)
  let rec separate_segments_impl (text_list: prog) (data_list: prog) (p: prog) : (prog * prog) =
    match p with
      | h :: t -> (
        match h.asm with
          | Text _ -> separate_segments_impl (h :: text_list) data_list t
          | Data _ -> separate_segments_impl text_list (h :: data_list) t
        )
      | [] -> (text_list, data_list)
  in
  match separate_segments_impl [] [] p with
    text_list, data_list -> (List.rev text_list), (List.rev data_list)


(* Calculate addresses of labels and return an associative list.
   Input: start - start address of the text segment
          p     - concatenated text-data segments in order
   Output: (a list of (label: lbl, address: quad), data segment start address)
   Side-effect: raise Redefined_sym if duplicates found.
 *)
let calc_label_addresses (start: quad) (p: prog) : ((lbl * quad) list * quad) =
  (* Tail recursion implementation *)
  let rec calc_label_addresses_impl (ret: (lbl * quad) list) (data_start : quad)
                                    (start: quad) (p: prog) : ((lbl * quad) list * quad) =
    match p with
      | [] -> (ret, data_start)
      | h :: t -> (
        if List.exists (fun (l, _) -> (l = h.lbl)) ret then
          raise (Redefined_sym h.lbl)
        else
          let asm_len: quad = Int64.mul 8L (Int64.of_int (
            match h.asm with
              | Data l -> List.length l
              | Text l -> List.length l
                                            ))
          in (
            match h.asm with
              | Data _ -> calc_label_addresses_impl ((h.lbl, start) :: ret) data_start
                                                    (Int64.add start asm_len) t
              | Text _ -> calc_label_addresses_impl ((h.lbl, start) :: ret) (Int64.add data_start asm_len)
                                                    (Int64.add start asm_len) t
          )
      )
  in let lookup, data_start = (calc_label_addresses_impl [] start start p) in
  (List.rev lookup, data_start)


(* Loop up a label or raise exception if not found *)
let lookup_label_or_raise_exception (label: lbl) (lookup: (lbl * quad) list) : quad =
  match List.assoc_opt label lookup with
    | Some addr -> addr
    | None -> raise (Undefined_sym label)


(* Replace label in a single operand *)
let replace_labels_in_operand (op: operand) (lookup: (lbl * quad) list) : operand =
  match op with
    | Imm (Lbl l) -> Imm (Lit (lookup_label_or_raise_exception l lookup))
    | Ind1 (Lbl l) -> Ind1 (Lit (lookup_label_or_raise_exception l lookup))
    | Ind3 (Lbl l, r) -> Ind3 (Lit (lookup_label_or_raise_exception l lookup), r)
    | other -> other


(* Replace label in a single instruction *)
let replace_labels_in_ins (op, args) (lookup: (lbl * quad) list) : ins =
  let replace_labels_in_operand_fold_left (ret: operand list) (arg: operand) : operand list (* reversed *) =
    (replace_labels_in_operand arg lookup) :: ret
  in
  (op, (List.rev (List.fold_left replace_labels_in_operand_fold_left [] args)))


(* Replace label in a single data *)
let replace_labels_in_data (d: data) (lookup: (lbl * quad) list) : data =
  match d with
    | Quad (Lbl l) -> Quad (Lit (lookup_label_or_raise_exception l lookup))
    | other -> other


(* Generic function to assemble a list of text/data elems *)
let assemble_generic_elems (replace_labels_fun: 'a -> (lbl * quad) list -> 'a)
                           (sbytes_fun: 'a -> sbyte list)
                           (asm_dispatch_fun: asm -> 'a list)
                           (el: elem list)
                           (lookup: (lbl * quad) list) : sbyte list =
  let assemble_generic_fold_left (ret: sbyte list) (x: 'a) : sbyte list =
    ret @ (sbytes_fun (replace_labels_fun x lookup))
  in
  let rec assemble_generic_elem_impl (ret : sbyte list) (el: elem list) : sbyte list =
    match el with
      | [] -> ret
      | e :: t -> assemble_generic_elem_impl (ret @ List.fold_left assemble_generic_fold_left [] (asm_dispatch_fun e.asm)) t
  in
  assemble_generic_elem_impl [] el


(* Assemble a list of text segments *)
let assemble_text_elems (tl: elem list) (lookup: (lbl * quad) list) : sbyte list =
  assemble_generic_elems
    replace_labels_in_ins
    sbytes_of_ins
    (fun asm -> match asm with
      | Text is -> is
      | _ -> invalid_arg "assemble_text_elems: tried to assemble a data elem!"
    )
    tl
    lookup

(* Assemble a list of data segments *)
let assemble_data_elems (dl: elem list) (lookup: (lbl * quad) list) : sbyte list =
  assemble_generic_elems
    replace_labels_in_data
    sbytes_of_data
    (fun asm -> match asm with
      | Data ds -> ds
      | _ -> invalid_arg "assemble_data_elems: tried to assemble a text elem!"
    )
    dl
    lookup


(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator
   - resolve the labels to concrete addresses and 'patch' the instuctions to
     replace Lbl values with the corresponding Imm values.
   - the text segment starts at the lowest address
   - the data segment starts after the text segment
  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
  let (text_elems, data_elems) = separate_segments p in
  let (lookup, data_start) = calc_label_addresses mem_bot (text_elems @ data_elems) in
  {  entry = lookup_label_or_raise_exception "main" lookup
   ; text_pos = mem_bot
   ; data_pos = data_start
   ; text_seg = assemble_text_elems text_elems lookup
   ; data_seg = assemble_data_elems data_elems lookup
  }

(* Convert an object file into an executable machine state.
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the
      appropriate locations
    - create the initial register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory
      - the other registers are initialized to 0
    - the condition code flags start as 'false'
  Hint: The Array.make, Array.blit, and Array.of_list library functions
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
  let m = {
    flags = { fo = false; fs = false; fz = false };
    regs = Array.make nregs 0L;
    mem = Array.make (Int64.to_int (Int64.sub mem_top mem_bot)) (Byte '\x00')
  } in
  let last_word_addr = (Int64.sub mem_top 8L) in
  Array.blit (Array.of_list text_seg) 0 m.mem (map_addr_or_seg_fault text_pos) (List.length text_seg);
  Array.blit (Array.of_list data_seg) 0 m.mem (map_addr_or_seg_fault data_pos) (List.length data_seg);
  Array.blit (Array.of_list (sbytes_of_int64 exit_addr)) 0 m.mem (map_addr_or_seg_fault last_word_addr) 8;
  m.regs.((rind Rip)) <- entry;
  m.regs.((rind Rsp)) <- last_word_addr;
  m