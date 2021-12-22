open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    let join_facts f1 f2 = match f1, f2 with
      | Const c1, Const c2 -> if Int64.equal c1 c2 then Const c1 else NonConst
      | UndefConst, _ | _, UndefConst -> UndefConst
      | _ -> NonConst

  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow ((u, i): uid * insn) (d: fact) : fact =
  let decode_operand (op: operand) : SymConst.t =
    match op with
    | Null -> SymConst.Const 0L
    | Const c -> SymConst.Const c
    | Gid id | Id id -> try UidM.find id d with Not_found -> SymConst.UndefConst
  in
  match i with
  | Binop (bop, _, op1, op2) -> (
    let v1 = decode_operand op1 in
    let v2 = decode_operand op2 in
    match v1, v2 with
    | SymConst.Const c1, SymConst.Const c2 -> (
      let f = match bop with
      | Add -> Int64.add
      | Sub -> Int64.sub
      | Mul -> Int64.mul
      | Shl -> (fun a b -> Int64.shift_left a (Int64.to_int b))
      | Lshr -> (fun a b -> Int64.shift_right_logical a (Int64.to_int b))
      | Ashr -> (fun a b -> Int64.shift_right a (Int64.to_int b))
      | And -> Int64.logand
      | Or -> Int64.logor
      | Xor -> Int64.logxor
      in
      let res = f c1 c2 in
      UidM.add u (SymConst.Const res) d
    )
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d
  )
  | Icmp (cnd, _, op1, op2) -> (
    let v1 = decode_operand op1 in
    let v2 = decode_operand op2 in
    match v1, v2 with
    | SymConst.Const c1, SymConst.Const c2 -> (
      let cmp = Int64.compare c1 c2 in
      let res = match cnd with
      | Eq -> (cmp = 0)
      | Ne -> (cmp <> 0)
      | Slt -> (cmp < 0)
      | Sle -> (cmp <= 0)
      | Sgt -> (cmp > 0)
      | Sge -> (cmp >= 0)
      in
      UidM.add u (SymConst.Const (if res then 1L else 0L)) d
    )
    | SymConst.UndefConst, _ | _, SymConst.UndefConst -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d
  )
  | Store _ | Call (Void, _, _) -> UidM.add u SymConst.UndefConst d
  | _ -> UidM.add u SymConst.NonConst d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow

    let normalize : fact -> fact =
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  =
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let join (d: fact) (e: fact): fact =
      UidM.merge (fun _ f1 f2 ->
                  match f1, f2 with
                  | Some f1, Some f2 -> Some (SymConst.join_facts f1 f2)
                  | v, None | None, v -> v
                 ) (normalize d) (normalize e)
    let combine (ds:fact list) : fact =
        List.fold_left join UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g: Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right
    (fun (u, _) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper
   functions.                                                                 *)
let run (cg: Graph.t) (cfg: Cfg.t) : Cfg.t =
  let open SymConst in


  let cp_block (l: Ll.lbl) (cfg: Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let cp_operand (c_map: fact) (op: Ll.operand) : Ll.operand =
      match op with
      | Gid id | Id id -> (
        match UidM.find_or UndefConst c_map id with
        | Const c -> Ll.Const c
        | _ -> op
      )
      | _ -> op
    in
    let cp_insn ((uid, i): (uid * insn)) : (uid * insn) =
      let cp_op (op: Ll.operand) : Ll.operand = cp_operand (cb uid) op in
      uid, match i with
      | Binop (bop, ty, op1, op2) -> Binop (bop, ty, cp_op op1, cp_op op2)
      | Alloca _ -> i
      | Load (ty, op) -> Load (ty, cp_op op)
      | Store (ty, op1, op2) -> Store (ty, cp_op op1, cp_op op2)
      | Icmp (cnd, ty, op1, op2) -> Icmp (cnd, ty, cp_op op1, cp_op op2)
      | Call (ty, f, args) -> Call (ty, f, List.map (fun (ty, op) -> ty, cp_op op) args)
      | Bitcast (t1, op, t2) -> Bitcast (t1, cp_op op, t2)
      | Gep (ty, op, args) -> Gep (ty, cp_op op, List.map cp_op args)
    in
    let cp_term ((uid, t): (uid * terminator)) : (uid * terminator) =
      let cp_op (op: Ll.operand) : Ll.operand = cp_operand (cb uid) op in
      uid, match t with
      | Ret (ty, (Some op)) -> Ret (ty, (Some (cp_op op)))
      | Cbr (op, lbl1, lbl2) -> Cbr (cp_op op, lbl1, lbl2)
      | x -> x
    in
    let b' = { insns = List.map cp_insn b.insns
             ; term = cp_term b.term } in
    {cfg with blocks = LblM.add l b' cfg.blocks}
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
