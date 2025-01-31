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

Fixpoint path_contains {a b : nat} (k : nat) (p : path a b) : Prop :=
  match p with 
  | path_refl _ _ _ => b = k
  | path_prepend _ _ a' p' _ =>
      a = k \/ path_contains k p'
  end.

Fixpoint path_is_in_tree {a b : nat} (p : path a b) : Prop :=
  match p with 
  | path_refl _ _ _ => True
  | path_prepend _ _ a' p' _ =>
      tree_edges a a' /\ path_is_in_tree p'
  end.

(* there exists a possibly empty path from A to B in the DFS tree *)
Notation "A -*> B" := (exists p : path A B, path_is_in_tree p) (at level 70).

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
  forall a a' b : nat, forall p : path a b, path_contains a' p ->
    path_is_in_tree p -> exists p' : path a' b, path_is_in_tree p'.
Proof.
  intros.
  induction p as [a b | a b a'' p''].
  { (* Base case: p is path_refl. We use that a = a' = b. *)
    assert (b = a'). { destruct H. auto. } 
    assert (e' := e).
    rewrite H1 in e'. rewrite <- e'.
    exists (path_refl a b e). auto.
  }
  { (* Inductive case: p is path_prepend. *)
    destruct H.
    { (* Case 1: a = a' (the paths a-to-b and a'-to-b are equal). *)
      rewrite <- H.
      exists (path_prepend a b a'' p'' o). auto.
    }
    { (* Case 2: path_contains a'' b a' p''
       * (a' is in remainder of path). *)
      destruct H0. apply IHp''; auto.
    }
  }
Qed.

Definition flow_graph_is_valid (fg : flow_graph) : Prop := 
  match fg with
  | flowgr num_nodes tree_edges other_edges start_time finish_time
  =>
     (* Each node is reachable from the root *)
     (forall n : nat, node_in_fg n ->
        exists p : path 0 n, path_is_in_tree p)
     /\
     (* Each node except the root has a tree-parent, which is a different node and has a lower starting time. *)
     (forall n : nat, node_in_fg n -> exists par : nat, par --> n /\ par <> n /\ par <: n)
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
Axiom FG_valid : flow_graph_is_valid FG.

Axiom FG_valid_no_self_loops : forall n m : nat, n ==> m -> n <> m.

Lemma ancestor_lower_start_time : forall n m : nat , n -*> m -> n <:= m.
  (* Proof is trivial; by induction *)
Proof. Admitted.

(*
(* sdom_candidate A B is a necessary condition for A = sdom(B) *)
Inductive sdom_candidate : nat -> nat -> Prop :=
  | sdc_root : sdom_candidate 0 0 (* sdom(root) := root *)
  | sdc_edge (n m : nat) :
      n --> m -> sdom_candidate n m
  | sdc_trans (n m k : nat) :
      n --> m /\ m >: k /\ sdom_candidate m k ->
        sdom_candidate n k.
*)

(* sdom_candidate A B <=> A <> B and there exists a path from A to B
 * and for all nodes x on the path, if x <> A and x <> B then x >: B. *)
Definition sdom_candidate_OLD (n m : nat) : Prop :=
  n <> m /\ exists p : path n m, forall x : nat, path_contains x p -> x <> n -> x <> m -> x >: m.

Fixpoint is_sdom_path_helper {n m : nat} (p : path n m) : Prop :=
  match p with
  | path_refl _ _ _ => True
  | path_prepend _ _ n' p' _ => n >: m /\ is_sdom_path_helper p'
  end.

Definition is_sdom_path {n m : nat} (p : path n m) : Prop :=
  match p with
  | path_refl _ _ _ => True
  | path_prepend _ _ n' p' _ => is_sdom_path_helper p'
  end.

Definition sdom_candidate (n m : nat) : Prop :=
  exists p : path n m, is_sdom_path p.

(* is_sdom_of A B <=> A is the (start-time)-minimum node 
 * of all sdom_candidates of B *)
Definition is_sdom_of (n m : nat) : Prop :=
  m <> 0 /\ (sdom_candidate n m /\ forall c, sdom_candidate c m -> n <:= c).

(* dom A B <=> A dominates B, i.e.,
 * every path from the root to B must go through A, and A<>B. *)
Inductive dom : nat -> nat -> Prop :=
  | is_dom (n m : nat) : n <> m ->
      (forall p : path 0 m, path_contains n p) -> dom n m.

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
    exists m : nat, path_contains m p /\ m -*> v /\ m -*> w.
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
  assert (exists p : path 0 w, path_is_in_tree p) as [path_0_w tree_path].
  { apply FG_valid. auto. }
  assert (path_contains idomw path_0_w) as idomw_in_path_0_w.
  { repeat (destruct H as [idomw w]). auto. }
  assert (exists p' : path idomw w, path_is_in_tree p').
  { apply (path_subpath_in_tree_right 0 idomw w path_0_w).
    apply idomw_in_path_0_w.
    assumption. }
  split.
  { auto. }
  { destruct H. destruct H. auto. }
Qed.

(* Lengauer, Tarjan:
 * For any vertex w <> r, sdom(w) -+> w.
 *)
Theorem LT_Lemma3 :
  forall w sdomw : nat, is_sdom_of sdomw w ->
   (node_in_fg w /\ w <> 0) -> sdomw -+> w.
Proof.
  intros. destruct H0.
  (* Part 1: let parw be the tree-parent of w. *)
  destruct FG_valid as [_ has_parent].
  assert (exists par : nat, par --> w /\ par <> w /\ par <: w)
    as has_parent' by (apply (has_parent w); auto).
  destruct has_parent' as [parw].
  destruct H2 as [parw_to_w [parw_neq_w parw_lt_w]].
  (* Part 2: Since parw --> w, sdomw <:= parw <: w, so sdomw <: w.
   * Furthermore, there exists a path [path_sdomw_w] from sdomw to w
   * of which all intermediate nodes are >: w. *)
  destruct H.
  destruct H2.
  destruct H2 as [path_sdomw_w path_sdom_path].
  assert (sdomw <: w).
  {
    apply (Nat.le_lt_trans
      (start_time sdomw) (start_time parw) (start_time w)).
    { 
      apply H3.
      assert (e1 : w=w) by reflexivity.
      assert (e2 : parw ==> w) by (left; auto).
      exists (path_prepend parw w w (path_refl w w e1) e2).
      simpl. auto.
    }
    { auto. }
  }
  (* Part 3: by Lemma 1, the path from sdomw to w must contain a common ancestor [anc] of sdomw and w. *)
  assert (exists m : nat, path_contains m path_sdomw_w /\ m -*> sdomw /\ m -*> w) as ex_anc.
  {
    apply (LT_Lemma1 sdomw w).
    apply Nat.lt_le_incl. auto.
  }
  destruct ex_anc as [anc anc_comm_anc].
  destruct anc_comm_anc as [path_cts_anc [anc_to_sdomw anc_to_w]].
  (* Part 4: prove that [sdomw = anc], from which the final goal follows.
   * How we do it: we use the path [path_sdomw_w], of which it is known that all strictly intermediate nodes are >: w. As [anc] is an ancestor of [w], by tree properties, we have anc <:= w. Thus, anc cannot be equal to any of the intermediate nodes. Thus, anc must be either equal to sdomw or to w. anc can also not be equal to w because it is known that anc <:= sdomw <: w. Hence, the only possibility left is anc = sdomw. *)
  assert (sdomw = anc).
  {
    destruct path_sdomw_w as [ | sdomw' path_sdomw'_w o].
    { destruct path_cts_anc. auto. }
    {
      destruct path_cts_anc as [ | anc_in_subpath].
      { auto. }
      {
        (* In this case we have a contradiction, and we prove it
         * by induction on the subpath from sdomw' to w! *)
        exfalso.
        clear path_sdom_path o.
        induction path_sdomw'_w as [sdomw' w | a b a' path_a'_b IH a_to_a'].
        { (* Base case: anc <> w as anc <:= sdomw <: w; contradiction. *)
          assert (anc <: w).
          {
            apply (Nat.le_lt_trans
              (start_time anc) (start_time sdomw) (start_time w)).
            { apply (ancestor_lower_start_time anc sdomw). auto. }
            { auto. }
          }
          destruct anc_in_subpath.
          assert (~ w <: w) by apply (Nat.lt_irrefl (start_time w)).
          auto.
        }
        { (* Inductive step: *)
          apply IH.
          auto. auto. auto. auto. auto. auto. auto. auto. (* will fix later *)
          {
            admit.
          }
          auto.
        }
      }
    }


    (*
    (* clear H H3 anc_to_sdomw. (* so they're not included in IH *) *)
    induction path_sdomw_w as [ | a b a' p' IH].
    { destruct path_cts_anc. auto. }
    {
      destruct path_cts_anc as [ | p'_cts_anc].
      { auto. }
      {
        (* Now we have a path [a ==> a' =*> b] with a subpath [p' : path a' b]. [path_sdom_path] states that all intermediate nodes of the whole path (so including a') are >: b. But [p'_cts_anc] states that [anc] is a node of p'. As a <: b, this is a contradiction. We use the induction hypothesis to prove that a' = anc, which eventually gives a contradiction with path_sdom_path. *)
        assert (a' = anc) as a'_anc.
        {
          apply IH.
          { auto. }
          { auto. }
          { auto. }
          {
            intros.
            apply path_sdom_path.
            { simpl. auto. }
            {
              admit. (* x <> a : XXX*)
            }
            { auto. }
          }
          { auto. }
          { auto. }
        }
        assert (a' >: b).
        {
          apply path_sdom_path.
          {
            simpl.
            right.
            rewrite <- a'_anc in p'_cts_anc.
            auto.
          }
          {
            symmetry.
            apply FG_valid_no_self_loops.
            auto.
          }
          {
            admit. (* XXX *)
          }
        }
        admit. (* easy, by contradiction *)
      }
    }
     *)
  }
  split.
  { rewrite H4. auto. }
  {
    red.
    intros.
    apply (f_equal start_time) in H5.
    apply (Nat.lt_neq) in H2.
    auto.
  }
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
