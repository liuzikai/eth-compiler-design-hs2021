(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
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
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
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
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

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

(* Serialize an instruction to sbytes *)
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
 if addr >= mem_bot && addr <= mem_top then
  (* map it into the location with (int addr - int lowest) *)
  Some ((Int64.to_int addr) - (Int64.to_int mem_bot))
 (* else None *)
 else None

(* Wrapper function for map_addr *)
let map_addr_or_seg_fault (addr: quad) : int =
  match map_addr addr with
    | Some ret -> ret
    | None -> raise X86lite_segfault

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let get_src_dest (args: operand list) (index: int) (m: mach): int64 =
	(*let x = List.nth args index in
		begin match x with
		| Imm i | Ind1 i -> begin match i with
												| Lit l -> l
												end
		| Reg r | Ind2 r -> m.regs.(rind r)
		| Ind3 (Lit l, r)  -> Int64.add (m.regs.(rind r)) l
		| _ -> failwith "problem get_src_dest"
		end*)
	failwith "get unimplemented"

let update_src_dest (args: operand list) (index: int) (new_value: int64) (m: mach): unit =
	failwith "update unimplemented"

let arith_instr (m: mach) (op: opcode) (args: operand list) : unit =
	(*begin match op with
	| Negq -> let dest = get_src_dest args 0 m in
							let new_dest = Int64_overflow.neg dest in
								update_src_dest args 0 new_dest.value m
	| Addq -> x
	| Subq -> x
	| Imulq -> x
	| Incq -> x
	| Decq -> x
	end*)
	failwith "arith_instr unimplemented"

let logic_instr (m: mach) (op: opcode) (args: operand list) : unit =
	(*begin match op with
	| Notq -> let dest = get_src_dest args 0 m in
							let new_dest = Int64.lognot dest in
								update_src_dest args 0 new_dest m
	| Andq -> x
	| Orq -> x
	| Xorq -> x
	end*)
	failwith "logic_instr unimplemented"

let bit_manipulation_instr (m: mach) (op: opcode) (args: operand list) : unit =
	(*begin match op with
	| Sarq -> x
	| Shlq -> x
	| Shrq -> x
	| Set _ -> x
	end*)
	failwith "bit_manipulation_instr unimplemented"

let data_move_instr (m: mach) (op: opcode) (args: operand list) : unit =
	(*begin match op with
	| Leaq -> x
	| Movq -> x
	| Pushq -> x
	| Popq -> x
	end*)
	failwith "data_move_instr unimplemented"

let ctrl_cond_instr (m: mach) (op: opcode) (args: operand list) : unit =
	(*begin match op with
	| Cmpq -> x
	| Jmp -> x
	| Callq -> x
	| Retq -> x
	| J _ -> x
	end*)
	failwith "ctrl_cond_instr unimplemented"

let step (m:mach) : unit =
	let fetch_instr = m.regs.(rind Rip) in
		let instr_addr = map_addr_or_seg_fault fetch_instr in
			let sbyte_instr = m.mem.(instr_addr) in
				begin match sbyte_instr with
				| InsB0 (op,args) -> begin match op with
														 | Negq | Addq | Subq | Imulq | Incq | Decq -> arith_instr m op args;
																															m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
														 | Notq | Andq | Orq | Xorq -> logic_instr m op args;
																													m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
														 | Sarq | Shlq | Shrq | Set _ -> bit_manipulation_instr m op args;
																														m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
														 | Leaq | Movq | Pushq | Popq -> data_move_instr m op args;
																														m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
														 | Cmpq | Jmp | Callq | Retq | J _ -> ctrl_cond_instr m op args;
																																 m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
														end
				| InsFrag -> m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 1L
  			| Byte b -> m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 1L
				(*| _ -> failwith "Here is the problem"*)
				end


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
        if List.exists (fun (l, _) : bool -> (l = h.lbl)) ret then
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

   - resolve the labels to concrete addresses and 'patch' the instructions to
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