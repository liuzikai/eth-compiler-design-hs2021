open Datastructures

(* dataflow analysis graph signature ---------------------------------------- *)
(* Interface for dataflow graphs structured in a way to facilitate 
   the general iterative dataflow analysis algorithm.                         

   The AsGraph functor in cfg.ml provides an implementation of this
   DFA_GRAPH signature that converts an LL IR control-flow graph to 
   this representation.

   NOTE: The direction of the analysis is goverened by how preds and
   succs are instantiated and how the corresponding flow function
   is defined.  This module pretends that all information is flowing
   "forward", but e.g. liveness instantiates the graph so that "forward"
   here is "backward" in the control-flow graph.

   This means that for a node n, the output information is explicitly
   represented by the "find_fact" function:
     out[n] = find_fact g n
   The input information for [n] is implicitly represented by:
     in[n] = combine preds[n] (out[n])

*)
module type DFA_GRAPH =
  sig
    module NodeS : SetS
    type node = NodeS.elt

    (* dataflow facts associated with the out-edges of the nodes in 
       this graph *)
    type fact

    (* the abstract type of dataflow graphs *)
    type t
    val preds : t -> node -> NodeS.t
    val succs : t -> node -> NodeS.t
    val nodes : t -> NodeS.t

    (* the flow function:
       given a graph node and input fact, compute the resulting fact on the 
       output edge of the node                                                
    *)
    val flow : t -> node -> fact -> fact

    (* lookup / modify the dataflow annotations associated with a node *)    
    val out : t -> node -> fact
    val add_fact : node -> fact -> t -> t

    (* printing *)
    val to_string : t -> string
    val printer : Format.formatter -> t -> unit
  end

(* abstract dataflow lattice signature -------------------------------------- *)
(* The general algorithm works over a generic lattice of abstract "facts".
    - facts can be combined (this is the 'join' operation)
    - facts can be compared                                                   *)
module type FACT =
  sig
    type t
    val combine : t list -> t
    val compare : t -> t -> int
    val to_string : t -> string
  end


(* generic iterative dataflow solver ---------------------------------------- *)
(* This functor takes two modules:
      Fact  - the implementation of the lattice                                
      Graph - the dataflow anlaysis graph

   It produces a module that has a single function 'solve', which 
   implements the iterative dataflow analysis described in lecture.
      - using a worklist (or workset) nodes 
        [initialized with the set of all nodes]

      - process the worklist until empty:
          . choose a node from the worklist
          . find the node's predecessors and combine their flow facts
          . apply the flow function to the combined input to find the new
            output
          . if the output has changed, update the graph and add the node's
            successors to the worklist                                        

   TASK: complete the [solve] function, which implements the above algorithm.
*)
module Make (Fact : FACT) (Graph : DFA_GRAPH with type fact := Fact.t) =
  struct
    let rec process (new_g: Graph.t) (worklist: Graph.NodeS.elt list): Graph.t =
        match worklist with
        | [] -> new_g
        | _ ->
            match worklist with
            | node :: remain ->
                let n = Graph.NodeS.elements (Graph.preds new_g node) in (* let n = worklist.pop() *)
                let old_out = Graph.out new_g node in (* old_out = out[n] *)
                let preds = fun n -> Graph.out new_g n in
                let preds_n = List.map preds n in (* preds[n] *)
                let combined_in = Fact.combine preds_n in(* let in = combine(preds[n]) *)
                let new_out = Graph.flow new_g node combined_in in(* out[n] = flow[n](in) *)
                if (Fact.compare old_out new_out) <> 0 then(* if(!equal old_out out[n] *)
                    (* for all m in succs[n], w.add(m) *)
                    let succs_n = Graph.NodeS.elements (Graph.succs new_g node) in
                    let add = fun n m -> n @ [m] in
                    let added_w = List.fold_left add remain succs_n in
                    let added_g = Graph.add_fact node new_out new_g in
                    process added_g added_w
                else process new_g remain
            | _ -> failwith "process ends HERE"

    let solve (g:Graph.t) : Graph.t =
        let worklist = Graph.NodeS.elements(Graph.nodes g) in (* let w = new set with all nodes*)
           match worklist with
           | [] -> g
           | _ -> process g worklist
  end

