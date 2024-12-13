Require Import PeanoNat.

(*----------------------------------------------------------------------------*)
(*-------------------------------- DEFINITIONS -------------------------------*)
(*----------------------------------------------------------------------------*)

Inductive flow_graph :=
  | flowgr
    (* The number of vertices in the flow graph, including the root.
     * Nodes are numbered [0, num_nodes); 0 is the root. *)
    (num_nodes : nat)
    (tree_edges: nat -> nat -> Prop)
    (other_edges: nat -> nat -> Prop)
    (start_time: nat -> nat)
    (finish_time: nat -> nat).

Definition flow_graph_is_valid (fg : flow_graph) : Prop := 
  match fg with
  | flowgr num_nodes tree_edges other_edges start_time finish_time
  =>
     (* Each node except the root has exactly one parent. *)
     (forall n : nat, (1 <= n < num_nodes) ->
       (exists p : nat, forall p' : nat,
         tree_edges p' n <-> p = p'))
     /\
     (* The root does not have a parent *)
     (forall p : nat, ~(tree_edges p 0))
     /\
     (* All nodes outside the range [0,num_nodes)
      * are not in the {tree,other}_edges relation *)
     (forall n m : nat, (num_nodes <= n \/ num_nodes <= m) ->
       ~(tree_edges n m) /\ ~(other_edges n m))
     /\
     (* There cannot be both a tree-edge and a non-tree-edge
      * between the same pair of nodes *)
     (forall n m : nat, ~(tree_edges n m /\ other_edges n m))
     /\
     (* For each node n with finish time f,
      * all nodes reachable from n have a finish time < f *)
     (forall p c : nat, (tree_edges p c \/ other_edges p c) -> 
       finish_time c < finish_time p)
     /\
     (* For each node, its start time is less than its finish time *)
     (forall n : nat, start_time n < finish_time n)
     /\
     (* Each start time and finish time is in the range [0, 2*num_nodes) *)
     (forall n : nat, 0 <= start_time n < 2*num_nodes /\
       0 <= finish_time n < 2*num_nodes)
     /\
     (* No duplicate start or finish times *)
     (forall n m : nat, n <> m -> start_time n <> start_time m /\
       start_time n <> finish_time m /\ finish_time n <> finish_time m)
     /\
     (* The root node has start time 0 *)
     (start_time 0) = 0
     /\
     (* The parent of each non-root node has a lower start time *)
     (forall n : nat, (1 <= n < num_nodes) ->
       forall p : nat, tree_edges p n -> start_time p < start_time n)
  end.

Definition node_in_fg
    (fg : flow_graph) (n : nat) : bool :=
  let (num_nodes, _, _, _, _) := fg in Nat.ltb n num_nodes.
  
Inductive reachable_in_tree : flow_graph -> nat -> nat -> Prop :=
  | rit_refl (fg : flow_graph) (n : nat) :
      node_in_fg fg n = true -> reachable_in_tree fg n n
  | rit_edge (fg : flow_graph) (n m : nat) :
      (let (_, e, _, _, _) := fg in e n m) -> reachable_in_tree fg n m
  | rit_trans (fg : flow_graph) (n m k : nat) :
      reachable_in_tree fg n m -> reachable_in_tree fg m k ->
        reachable_in_tree fg n k.

(* The global flow-graph that we work on *)
Variable (num_nodes : nat).
Variable (tree_edges: nat -> nat -> Prop).
Variable (other_edges: nat -> nat -> Prop).
Variable (start_time: nat -> nat).
Variable (finish_time: nat -> nat).
Definition FG : flow_graph :=
  flowgr num_nodes tree_edges other_edges start_time finish_time.

(* there is a tree edge from A to B *)
Notation "A --> B" := (tree_edges A B) (at level 70).

(* there is a non-tree edge from A to B *)
Notation "A ~~> B" := (other_edges A B) (at level 70).

(* there is an edge (either tree or non-tree) from A to B *)
Notation "A ==> B" := (A --> B \/ A ~~> B) (at level 70).

(* there exists a possibly empty path from A to B in the DFS tree *)
Notation "A -*> B" := (reachable_in_tree FG A B) (at level 70).

(* there exists a nonempty path from A to B in the DFS tree *)
Notation "A -+> B" := ((A -*> B) /\ (A <> B)) (at level 70).

(* the start time of A is <= the start time of B *)
Notation "A <:= B" := (start_time A <= start_time B) (at level 70).

(* the start time of A is < the start time of B *)
Notation "A <: B" := (start_time A < start_time B) (at level 70).

(* the start time of A is >= the start time of B *)
Notation "A >:= B" := (start_time A >= start_time B) (at level 70).

(* the start time of A is > the start time of B *)
Notation "A >: B" := (start_time A > start_time B) (at level 70).

(* sdom_candidate A B is a necessary condition for A = sdom(B) *)
Inductive sdom_candidate : nat -> nat -> Prop :=
  | sdc_root : sdom_candidate 0 0 (* sdom(root) := root *)
  | sdc_edge (n m : nat) :
      n --> m -> sdom_candidate n m
  | sdc_trans (n m k : nat) :
      n --> m /\ m >: k /\ sdom_candidate m k ->
        sdom_candidate n k.


Definition sdom_cand_dec : forall n m,
  { sdom_candidate n m } + { ~sdom_candidate n m }.
Admitted. (* ugly... *)

(* Returns the smallest sdom-candidate of n that is >= m.
 * The third argument is to ensure termination. *)
Fixpoint sdom_helper (n m count : nat) : nat :=
  match count with
  | 0 => num_nodes (* unreachable *)
  | S ctr => if sdom_cand_dec n m
             then m
             else sdom_helper n (m+1) ctr
  end.

(* Returns the minimum of all sdom-candidates.
 * Returns 0 for the root node. *)
Definition sdom (n : nat) : nat :=
  sdom_helper n 0 num_nodes.

(* reachable_wo W A B <=> node B is reachable from node A
 * using either tree edges or non-tree edges or both,
 * _without visiting node W_ on the way (and W<>A,B). *)
Inductive reachable_wo : nat -> nat -> nat -> Prop :=
  | rwo_refl (wo n : nat) :
      (node_in_fg FG n = true /\ n <> wo) -> reachable_wo wo n n
  | rwo_edge  (wo n m : nat) :
      (n ==> m /\ n <> wo /\ m <> wo) ->
        reachable_wo wo n m
  | rwo_trans  (wo n m k : nat) :
      reachable_wo wo n m -> reachable_wo wo m k ->
        reachable_wo wo n k.

(* dom A B <=> A dominates B, i.e.,
 * every path from the root to B must go through A. *)
Inductive dom : nat -> nat -> Prop := 
  | is_dom (n m : nat) : ~(reachable_wo n 0 m) -> dom n m.

(* idom A B <=> A is the immediate dominator of B, i.e.,
 * A dominates B and every other dominator of B dominates A. *)
Inductive idom : nat -> nat -> Prop :=
  | is_idom (n m : nat) : (dom n m /\ forall k : nat,
      node_in_fg FG k = true -> dom k m -> dom k n) ->
        idom n m.
