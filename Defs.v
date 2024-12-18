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

(* The global flow-graph that we work on *)
Variable (num_nodes : nat).
Variable (tree_edges: nat -> nat -> Prop).
Variable (other_edges: nat -> nat -> Prop).
Variable (start_time: nat -> nat).
Variable (finish_time: nat -> nat).
Definition FG : flow_graph :=
  flowgr num_nodes tree_edges other_edges start_time finish_time.

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
    (n : nat) : bool :=
  Nat.ltb n num_nodes.

(* there is a tree edge from A to B *)
Notation "A --> B" := (tree_edges A B) (at level 70).

(* there is a non-tree edge from A to B *)
Notation "A ~~> B" := (other_edges A B) (at level 70).
  
Inductive reachable_in_tree : nat -> nat -> Prop :=
  | rit_refl (n : nat) :
      node_in_fg n = true -> reachable_in_tree n n
  | rit_edge (n m : nat) :
      (n --> m) -> reachable_in_tree n m
  | rit_trans (n m k : nat) :
      reachable_in_tree n m -> reachable_in_tree m k ->
        reachable_in_tree n k.

(* there is an edge (either tree or non-tree) from A to B *)
Notation "A ==> B" := (A --> B \/ A ~~> B) (at level 70).

(* there exists a possibly empty path from A to B in the DFS tree *)
Notation "A -*> B" := (reachable_in_tree A B) (at level 70).

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

(* is_sdom_of A B <=> A is the semidominator of B,
 * or A and B are both the root node. *)
Inductive is_sdom_of : nat -> nat -> Prop :=
  | is_sdom (n m : nat) : (sdom_candidate n m /\
      forall c, sdom_candidate c m -> n <:= c) ->
        is_sdom_of n m.

(* reachable_wo W A B <=> node B is reachable from node A
 * using either tree edges or non-tree edges or both,
 * _without visiting node W_ on the way (and W<>A,B). *)
Inductive reachable_wo : nat -> nat -> nat -> Prop :=
  | rwo_refl (wo n : nat) :
      (node_in_fg n = true /\ n <> wo) -> reachable_wo wo n n
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

(* is_idom_of A B <=> A is the immediate dominator of B, i.e.,
 * A dominates B and every other dominator of B dominates A. *)
Inductive is_idom_of : nat -> nat -> Prop :=
  | is_idom (n m : nat) : (dom n m /\ forall k : nat,
      node_in_fg k = true -> dom k m -> dom k n) ->
        is_idom_of n m.

(* Each node in the flowgraph has exactly one semidominator *)
Theorem sdom_unique : forall n : nat, node_in_fg n = true -> (exists sd : nat, forall sd' : nat, sd = sd' <-> is_sdom_of sd' n).
Proof. Admitted.

(* Each node in the flowgraph has exactly one immediate dominator *)
Theorem LT_Theorem1_Part1 : forall n : nat, node_in_fg n = true -> (exists id : nat, forall id' : nat, id = id' <-> is_idom_of id' n).
Proof. Admitted.

(* The immediate dominator function *)
Definition idom : nat -> nat. Admitted.
Axiom idom_function : forall n : nat, is_idom_of (idom n) n.

(* The semidominator function *)
Definition sdom : nat -> nat. Admitted.
Axiom sdom_function : forall n : nat, is_sdom_of (idom n) n.

(* If v, w are vertices of G such that v <:= w, then any
 * path from v to w contains some common ancestor of
 * v and w in the DFS tree. *)
Theorem LT_Lemma1 : True (* TODO *).
Proof. Admitted.

Theorem LT_Lemma2 : forall w : nat, (node_in_fg w = true /\ w <> 0) -> idom w -+> w.
Proof. Admitted.

Theorem LT_Lemma3 : forall w : nat, (node_in_fg w = true /\ w <> 0) -> sdom w -+> w.
Proof. Admitted.

Theorem LT_Lemma4 : forall w : nat, (node_in_fg w = true /\ w <> 0) -> idom w -*> sdom w.
Proof. Admitted.

Theorem LT_Lemma5 : forall v w : nat, (node_in_fg v = true /\ node_in_fg w = true /\ v -*> w) -> (v -*> idom w \/ idom w -*> idom v).
Proof. Admitted.


Theorem LT_Theorem1_Part2 : True (* TODO *).
Proof. Admitted.

Theorem LT_Theorem2 :
  forall w : nat, node_in_fg w = true ->
    (
      (w <> 0 /\ (forall u, (node_in_fg u = true /\ sdom w -+> u /\ u -*> w) -> sdom u >:= sdom w)
    ) -> idom w = sdom w).
Proof. Admitted.

Theorem LT_Theorem3 : True (* TODO *).
Proof. Admitted.

Theorem LT_Theorem4 : True (* TODO *).
Proof. Admitted.


Theorem LT_Corollary1 : True (* TODO *).
Proof. Admitted.
