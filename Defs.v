Require Import PeanoNat.

Section Dominators.

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

(* This node exists within the flow graph *)
Definition node_in_fg (n : nat) := n < num_nodes.

(* there is a tree edge from A to B *)
Notation "A --> B" := (tree_edges A B) (at level 70).

(* there is a non-tree edge from A to B *)
Notation "A ~~> B" := (other_edges A B) (at level 70).
  
(* there is an edge (either tree or non-tree) from A to B *)
Notation "A ==> B" := (A --> B \/ A ~~> B) (at level 70).

(* the start time of A is <= the start time of B *)
Notation "A <:= B" := (start_time A <= start_time B) (at level 70).

(* the start time of A is < the start time of B *)
Notation "A <: B" := (start_time A < start_time B) (at level 70).

(* the start time of A is >= the start time of B *)
Notation "A >:= B" := (start_time A >= start_time B) (at level 70).

(* the start time of A is > the start time of B *)
Notation "A >: B" := (start_time A > start_time B) (at level 70).

Inductive path (a b : nat) : Type :=
  | path_refl :
      a = b -> path a b
  | path_prepend (a' : nat) (p' : path a' b) :
      a ==> a' -> path a b.

Fixpoint path_contains (a b k : nat) (p : path a b) : Prop :=
  match p with 
  | path_refl _ _ _ => b = k
  | path_prepend _ _ a' p' _ =>
      a = k \/ path_contains a' b k p'
  end.

Fixpoint path_is_in_tree (a b : nat) (p : path a b) : Prop :=
  match p with 
  | path_refl _ _ _ => True
  | path_prepend _ _ a' p' _ =>
      tree_edges a a' /\ path_is_in_tree a' b p'
  end.

(* there exists a possibly empty path from A to B in the DFS tree *)
Notation "A -*> B" := (exists p : path A B, path_is_in_tree A B p) (at level 70).

(* there exists a nonempty path from A to B in the DFS tree *)
Notation "A -+> B" := ((A -*> B) /\ (A <> B)) (at level 70).

(*
Lemma path_subpath_left :
  forall a a' b : nat, forall p : path a b, path_contains a b a' p -> path a a'.
Proof. Admitted.
*)

(* If a path consists only of tree edges, then any (right-)subpath also
 * consists only of tree edges. *)
Lemma path_subpath_in_tree_right :
  forall a a' b : nat, forall p : path a b, path_contains a b a' p ->
    path_is_in_tree a b p -> exists p' : path a' b, path_is_in_tree a' b p'.
Proof.
  intros.
  induction p as [a b | a b a'' p''].
  { (* Base case: p is path_refl. We use that a = a' = b. *)
    assert (b = a'). { destruct H. trivial. } 
    assert (e' := e).
    rewrite H1 in e'.
    rewrite <- e'.
    exists (path_refl a b e).
    trivial.
  }
  { (* Inductive case: p is path_prepend. *)
    destruct H.
    { (* Case 1: a = a' (the paths a-to-b and a'-to-b are equal). *)
      rewrite <- H.
      exists (path_prepend a b a'' p'' o).
      trivial.
    }
    { (* Case 2: path_contains a'' b a' p''
       * (a' is in remainder of path). *)
      destruct H0.
      apply IHp''; trivial.
    }
  }
Qed.

Definition flow_graph_is_valid (fg : flow_graph) : Prop := 
  match fg with
  | flowgr num_nodes tree_edges other_edges start_time finish_time
  =>
     (* Each node is reachable from the root *)
     (forall n : nat, node_in_fg n ->
        exists p : path 0 n, path_is_in_tree 0 n p)
     /\
     (* Each node except the root has a tree-parent. *)
     (forall n : nat, node_in_fg n -> exists par : nat, par --> n)
     (* NOTE: the rest is commented out because I haven't yet used them
      * in proofs. This way, we don't assume unnecessary stuff. *)
     (*
        (* Parents are unique *)
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
     *)
  end.
Axiom FG_valid: flow_graph_is_valid FG.

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

(* dom A B <=> A dominates B, i.e.,
 * every path from the root to B must go through A, and A<>B. *)
Inductive dom : nat -> nat -> Prop :=
  | is_dom (n m : nat) : n <> m ->
      (forall p : path 0 m, path_contains 0 m n p) -> dom n m.

(* is_idom_of A B <=> A is the immediate dominator of B, i.e.,
 * A dominates B and every other dominator of B dominates A. *)
Inductive is_idom_of : nat -> nat -> Prop :=
  | is_idom (n m : nat) : dom n m -> (forall k : nat,
      node_in_fg k -> dom k m -> dom k n) ->
        is_idom_of n m.

(* Each node w <> r in the flowgraph has exactly one immediate dominator *)
Theorem LT_Theorem1_Part1 :
  forall n : nat, node_in_fg n ->
    (exists id : nat, forall id' : nat, id = id' <-> is_idom_of id' n).
Proof. Admitted.

(* Lengauer, Tarjan:
 * If v, w are vertices of G such that v <:= w, then any
 * path from v to w contains some common ancestor of
 * v and w in the DFS tree. *)
Theorem LT_Lemma1 : 
  forall v w : nat, v <:= w -> forall p : path v w,
    exists m : nat, path_contains v w m p /\ m -*> v /\ m -*> w.
Proof. Admitted.

(* Lengauer, Tarjan:
 * For any vertex w <> r, idom(w) -+> w.
 *)
Theorem LT_Lemma2 :
  forall w idomw : nat, is_idom_of idomw w -> node_in_fg w ->
    w <> 0 -> idomw -+> w.
Proof.
  intros.
  (* Proof idea: all paths from 0 to w must go through idomw.
   * There exists at least one such path that only uses tree edges,
   * as each node is reachable from the root using only tree edges.
   * Therefore, this path must contain a subpath from idomw to w. *)
  assert (exists p : path 0 w, path_is_in_tree 0 w p) as exists_path_0_w.
  { apply FG_valid.
    trivial. }
  destruct exists_path_0_w as [path_0_w tree_path].
  assert (path_contains 0 w idomw path_0_w) as idomw_in_path_0_w.
  { repeat (destruct H as [idomw w]).
    trivial. }
  assert (exists p' : path idomw w, path_is_in_tree idomw w p').
  { apply (path_subpath_in_tree_right 0 idomw w path_0_w).
    apply idomw_in_path_0_w.
    assumption. }
  split.
  { trivial. }
  { destruct H.
    destruct H.
    trivial. }
Qed.

(* Lengauer, Tarjan:
 * For any vertex w <> r, sdom(w) -+> w.
 *)
Theorem LT_Lemma3 :
  forall w sdomw : nat, is_sdom_of sdomw w ->
   (node_in_fg w /\ w <> 0) -> sdomw -+> w.
Proof.
  intros.
  destruct H0.
  (* Part 1: let parw be the tree-parent of w. *)
  destruct FG_valid as [_ has_parent].
  assert (exists par : nat, par --> w) as has_parent'.
  { apply (has_parent w).
    trivial. }
  clear has_parent.
  destruct has_parent' as [parw].
  (* Part 2: Since parw --> w, sdomw <:= parw <: w, so sdomw <: w. Furthermore, there exists a path from sdomw to w of which all intermediate nodes are >: w. *)
  destruct H as [sdomw w].
  destruct H.
  destruct H.

Qed.

(* Lengauer, Tarjan:
 * For any vertex w <> r, idom(w) -*> sdom(w).
 *)
Theorem LT_Lemma4 :
  forall w idomw sdomw : nat, is_idom_of idomw w -> is_sdom_of sdomw w
    -> (node_in_fg w /\ w <> 0) -> idomw -*> sdomw.
Proof. Admitted.

(* Lengauer, Tarjan:
 * Let vertices v,w satisfy v -*> w. Then v -*> idom(w) or idom(w) -*> idom(v).
 *)
Theorem LT_Lemma5 :
  forall v w idomw idomv : nat, is_idom_of idomw w ->
    is_idom_of idomv v -> (node_in_fg v /\ node_in_fg w /\ v -*> w) ->
      (v -*> idomw \/ idomw -*> idomv).
Proof. Admitted.


(* Lengauer, Tarjan:
 * The edges {(idom(w),w) | w in V\{r}} form a directed tree
 * rooted at r, (called the dominator tree of G), such that
 * v dominates w if and only if v is a proper ancestor of w
 * in the dominator tree.
 *
 * XXX: It is probably not necessary to prove this to get the final result!
 *)
Theorem LT_Theorem1_Part2 : True (* XXX *).
Proof. Admitted.

(* Lengauer, Tarjan:
 * Let w <> r. Suppose every u for which sdom(w) -+> u -*> w
 * satisfies sdom(u) >:= sdom(w). Then idom(w) = sdom(w).
 *)
Theorem LT_Theorem2 :
  forall w idomw sdomw : nat, is_idom_of idomw w ->
    is_sdom_of sdomw w -> node_in_fg w -> w <> 0 ->
      (
        forall u sdomu : nat, is_sdom_of sdomu u ->
          (node_in_fg u /\ sdomw -+> u /\ u -*> w) -> sdomu >:= sdomw
      )
        -> idomw = sdomw.
Proof. Admitted.

(* Lengauer, Tarjan:
 * Let w <> r and let u be a vertex for which sdom(u) is minimum
 * among vertices u satisfying sdom(w) -+> u -*> w.
 * Then sdom(u) <:= sdom(w) and idom(u) = idom(w).
 *)
Theorem LT_Theorem3 :
  forall w u idomu idomw sdomu sdomw : nat, is_sdom_of sdomu u ->
    is_sdom_of sdomw w -> is_idom_of idomu u -> is_idom_of idomw w ->
      w <> 0 -> node_in_fg u -> node_in_fg w ->
        (sdomw -+> u /\ u -*> w) ->
          (forall u' : nat, (sdomw -+> u' /\ u' -*> w) -> u <:= u') ->
    (sdomu <:= sdomw /\ idomu = idomw).
Proof. Admitted.


(* Lengauer, Tarjan:
 * Let w <> r and let u be a vertex for which sdom(u) is minimum
 * among vertices u satisfying sdom(w) -+> u -*> w.
 * Then idom(w) = sdom(w) if sdom(w) = sdom(u), and
 * idom(w) = idom(u) otherwise.
 *)
Theorem LT_Corollary1 :
  forall w u idomu idomw sdomu sdomw: nat, is_idom_of idomu u ->
    is_idom_of idomw w -> is_sdom_of sdomu u -> is_sdom_of sdomw w ->
      w <> 0 -> node_in_fg u -> node_in_fg w ->
        (sdomw -+> u /\ u -*> w) ->
          (forall u' : nat, (sdomw -+> u' /\ u' -*> w) -> u <:= u') ->
    ((sdomw = sdomu -> idomw = sdomw) /\
     (sdomw <> sdomu -> idomw = idomu)).
Proof. Admitted.

Inductive is_minimum_of (n : nat) (P : nat -> Prop) : Prop :=
  | is_min : P n -> (forall n' : nat, P n' -> n <= n') -> is_minimum_of n P.

(* Lengauer, Tarjan:
 * If w is not the root node, then
   sdom w = min(
           {v | v ==> w and v <: w}
             union
           {sdom(u) | u >: w and there is an edge v ==> w such that u -*> v}
          ).
 *)
Theorem LT_Theorem4 :
  forall w sdomw : nat, is_sdom_of sdomw w -> w <> 0 -> node_in_fg w ->
  is_minimum_of (sdomw)
  (
    fun x => (x ==> w /\ x <: w) \/
      (
        exists u v : nat, is_sdom_of x u /\ node_in_fg u /\
          node_in_fg v /\ u >: w /\ v ==> w /\ u -*> v
      )
  )
.
Proof. Admitted.

End Dominators.
