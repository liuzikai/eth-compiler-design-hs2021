(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

    let join_facts f1 f2 = match f1, f2 with
      | Unique, Unique -> Unique
      | MayAlias, _ | _, MayAlias -> MayAlias
      | UndefAlias, t | t, UndefAlias -> t
  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)

(* fun m (k,v) -> UidM.add k v m *)
let insn_flow ((u, i): uid * insn) (d: fact) : fact =
  match i with
  | Alloca _ -> UidM.add u SymPtr.Unique d  (* return ptr *)

  | Load (Ptr (Ptr _), _) -> UidM.add u SymPtr.MayAlias d  (* return ptr *)

  | Call (ret_ty, _ , args) -> (
    let d' = match ret_ty with
    | Ptr _ -> UidM.add u SymPtr.MayAlias d  (* return ptr *)
    | _ -> d
    in
    let fold_arg (lo: fact) ((ty, arg): Ll.ty * Ll.operand) : fact =
      match (ty, arg) with
      | Ptr _, Id id -> UidM.add id SymPtr.MayAlias lo  (* ptr as argument *)
      | Ptr _, Gid gid -> UidM.add gid SymPtr.MayAlias lo  (* ptr as argument *)
      | _ -> lo
    in
    List.fold_left fold_arg d' args
  )

  | Bitcast (from_ty, from_op, to_ty) -> (
    let d' = match (from_ty, from_op) with
    | Ptr _, Id id -> UidM.add id SymPtr.MayAlias d  (* ptr as argument *)
    | Ptr _, Gid gid -> UidM.add gid SymPtr.MayAlias d  (* ptr as argument *)
    | _ -> d
    in match to_ty with
    | Ptr _ -> UidM.add u SymPtr.MayAlias d'  (* return ptr *)
    | _ -> d'
  )

  | Gep (_, op, _) -> (
    let d' = match op with
    | Id id -> UidM.add id SymPtr.MayAlias d  (* ptr as argument *)
    | _ -> d
    in UidM.add u SymPtr.MayAlias d'  (* return ptr *)
  )

  | Store (Ptr _, Id id, _) -> UidM.add id SymPtr.MayAlias d  (* ptr as argument *)

  | _ -> d

(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)
    let join (d: fact) (e: fact): fact =
            UidM.merge (fun _ f1 f2 ->
                        match f1, f2 with
                          | Some f1, Some f2 -> Some (SymPtr.join_facts f1 f2)
                          | v, None | None, v -> v
                       ) d e
    let combine (ds:fact list) : fact =
        List.fold_left join UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

