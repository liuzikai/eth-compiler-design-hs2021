(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)

let dce_block (lb:uid -> Liveness.Fact.t) (* type t = UidS.t *)
              (ab:uid -> Alias.fact) (* type fact = SymPtr.t UidM.t *)
              (b:Ll.block) : Ll.block =
              (* type block = { insns : (uid * insn) list; term : (uid * terminator) } *)
   let new_insns_list = List.filter (fun insn -> match insn with
                                    | (_, Call(_,_,_)) -> true
                                    | (u, Store(_, _, Id id)) -> begin match UidM.find_or Alias.SymPtr.UndefAlias(ab u) id with
                                                                 | Alias.SymPtr.MayAlias -> true
                                                                 | _ -> if UidS.mem id (lb u) then true
                                                                        else false
                                                                 end
                                    | (u, i) -> if UidS.mem u (lb u) then true
                                                else false
                                    ) b.insns in
   {insns = new_insns_list; term = b.term}

let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg
