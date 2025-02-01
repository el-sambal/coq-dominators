Require Import PeanoNat.

Section Dominators.

(* The number of vertices in the flow graph, including the root.
 * Nodes are numbered [0, num_nodes); 0 is the root. *)
Variable (num_nodes : nat).

(* The edges of the depth first search tree (DFS tree). *)
Variable (tree_edges: nat -> nat -> Prop).

(* The edges in the flow graph that are not part of the DFS tree. *)
Variable (other_edges: nat -> nat -> Prop).

(* Maps vertices to their start time, as marked by DFS. *)
Variable (start_time: nat -> nat).

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

(* If a path consists only of tree edges, then any (right-)subpath also
 * consists only of tree edges. *)
Lemma path_subpath_in_tree_right :
  forall a a' b : nat, forall p : path a b, path_contains a' p ->
    path_is_in_tree p -> exists p' : path a' b, path_is_in_tree p'.
Proof.
  intros.
  induction p as [a b | a b a'' p''].
  - (* Base case: p is path_refl. We use that a = a' = b. *)
    assert (b = a') by (destruct H; auto).  
    assert (e' := e).
    rewrite H1 in e'. rewrite <- e'.
    exists (path_refl a b e). auto.
  - (* Inductive case: p is path_prepend. *)
    destruct H.
    + (* Case 1: a = a' (the paths a-to-b and a'-to-b are equal). *)
      rewrite <- H. exists (path_prepend a b a'' p'' o). auto.
    + (* Case 2: path_contains a'' b a' p''
       * (a' is in remainder of path). *)
      destruct H0. apply IHp''; auto.
Qed.

Axiom FG_valid__path_from_root : forall n : nat, node_in_fg n ->
  exists p : path 0 n, path_is_in_tree p.
Axiom FG_valid__node_has_par : forall n : nat, node_in_fg n ->
  exists par : nat, par --> n.
Axiom FG_valid__par_earlier : forall n par : nat, par --> n -> par <: n.

(* Lemma 1 from Lengauer, Tarjan:
 *  "If v, w are vertices of G such that v <:= w, then any
 *   Path from v to w contains some common ancestor of
 *   V and w in the DFS tree."
 *
 * This lemma is presented without proof in Lengauer and Tarjan's paper.
 * As it is a true fact for DFS trees in general, we take it as an axiom.
 ***)
Axiom LT_Lemma1 : 
  forall v w : nat, v <:= w -> forall p : path v w,
    exists m : nat, path_contains m p /\ m -*> v /\ m -*> w.

(* Simple helper lemma. *)
Lemma ancestor_lower_start_time : forall n m : nat , n -*> m -> n <:= m.
Proof.
  intros.
  destruct H as [p].
  induction p.
  - apply Nat.eq_le_incl.
    apply (f_equal start_time). auto.
  - simpl in H. 
    destruct H.
    apply Nat.lt_le_incl.
    apply (Nat.lt_le_trans (start_time a) (start_time a') (start_time b)).
    + apply FG_valid__par_earlier. auto.
    + apply IHp. auto.
Qed.

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

(* We define [sdom_candidate n m] to be true if and only if there exists a path
 * [n ~~> v_1 ~~> ... ~~> v_n ~~> m] such that [v_i >: m] for all [i] in [1..=m]. *)
Definition sdom_candidate (n m : nat) : Prop :=
  exists p : path n m, is_sdom_path p.

(* We define [is_sdom_of A B] to be true if and only if [A] is the [<:]-minimum
 * node of all [sdom_candidate]s of [B] *)
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


(* Lemma 2 of the paper of Lengauer and Tarjan states the following:
 *
 *  "For any vertex [w <> r], [idom(w) -+> w]."
 *)
Theorem LT_Lemma2 :
  forall w idomw : nat, is_idom_of idomw w -> node_in_fg w ->
    w <> 0 -> idomw -+> w.
Proof.
  intros.
  (* Proof idea: all paths from [0] to [w] must go through [idomw].
   * There exists at least one such path that only uses tree edges,
   * as each node is reachable from the root using only tree edges.
   * Therefore, this path must contain a subpath from [idomw] to [w]. *)
  assert (exists p : path 0 w, path_is_in_tree p) as [path_0_w tree_path]
    by (apply FG_valid__path_from_root; auto).
  assert (path_contains idomw path_0_w) as idomw_in_path_0_w
    by ( repeat (destruct H as [idomw w]); auto ).
  assert (exists p' : path idomw w, path_is_in_tree p'). {
    apply (path_subpath_in_tree_right 0 idomw w path_0_w).
    apply idomw_in_path_0_w.
    assumption.
  }
  split.
  - auto.
  - destruct H. destruct H. auto.
Qed.

Lemma LT_Lemma3_Helper :
  forall n m s : nat, forall p : path n m,
    is_sdom_path_helper p -> s <: m -> ~ path_contains s p.
Proof.
  intros. red. intros.
  induction p.
  - simpl in H1. apply (f_equal start_time) in H1.
    apply (Nat.lt_neq) in H0.
    symmetry in H1. contradiction.
  -
    simpl in H1. simpl in H. destruct H. apply IHp.
    + auto.
    + auto.
    + destruct H1.
      * rewrite <- H1 in H0.
        assert (a <:= b) by
          (apply (Nat.lt_le_incl (start_time a) (start_time b)); auto).
        assert (~ a >: b) by (apply (Nat.le_ngt (start_time a) (start_time b)); auto).
        contradiction.
      * auto.
Qed.

(* Lemma 3 of the paper of Lengauer and Tarjan states the following:
 *
 *  "For any vertex [w <> r], [sdom(w) -+> w]."
 *)
Theorem LT_Lemma3 :
  forall w sdomw : nat, is_sdom_of sdomw w ->
   (node_in_fg w /\ w <> 0) -> sdomw -+> w.
Proof.
  intros. destruct H0.
  (* Part 1: let [parw] be the tree-parent of [w]. *)
  assert (exists par : nat, par --> w)
    as [parw] by (apply (FG_valid__node_has_par w); auto).
  (* Part 2: Since [parw --> w], [sdomw <:= parw <: w], so [sdomw <: w].
   * Furthermore, there exists a path [path_sdomw_w] from [sdomw] to [w]
   * of which all intermediate nodes are [>: w]. *)
  destruct H as [H [[path_sdomw_w path_sdom_path] sdomw_minimal_cand]].
  assert (sdomw <: w).
  {
    apply (Nat.le_lt_trans
      (start_time sdomw) (start_time parw) (start_time w)).
    - apply sdomw_minimal_cand. assert (e1 : w=w) by reflexivity.
      assert (e2 : parw ==> w) by (left; auto).
      exists (path_prepend parw w w (path_refl w w e1) e2). simpl. auto.
    - apply FG_valid__par_earlier. auto.
  }
  (* Part 3: by Lemma 1 of the paper of Lengauer and Tarjan, the path from
   * [sdomw] to [w] must contain a common ancestor [anc] of [sdomw] and [w]. *)
  assert (exists m : nat, path_contains m path_sdomw_w /\
      m -*> sdomw /\ m -*> w) as ex_anc. {
    apply (LT_Lemma1 sdomw w).
    apply Nat.lt_le_incl. auto.
  }
  destruct ex_anc as [anc anc_comm_anc].
  destruct anc_comm_anc as [path_cts_anc [anc_to_sdomw anc_to_w]].
  (* Part 4: prove that [sdomw = anc], from which the final goal follows.
   * How we do it: we use the path [path_sdomw_w], of which it is known that
   * all strictly intermediate nodes are [>: w]. As [anc] is an ancestor of [w],
   * by tree properties, we have [anc <:= w]. Thus, [anc] cannot be equal to
   * any of the intermediate nodes. Thus, [anc] must be either equal to [sdomw]
   * or to [w]. [anc] can also not be equal to [w] because it is known that
   * [anc <:= sdomw <: w]. Hence, the only possibility left is [anc = sdomw].
   * The proof makes use of induction, which is delegated to the helper lemma [LT_Lemma3_Helper]. *)
  assert (sdomw = anc). {
    destruct path_sdomw_w as [ | sdomw' path_sdomw'_w o].
    - destruct path_cts_anc. auto.
    - destruct path_cts_anc.
      + auto.
      + assert (~ path_contains anc path_sdomw'_w). {
          apply LT_Lemma3_Helper.
          - auto. 
          - assert (anc <: w). {
              apply (Nat.le_lt_trans
                (start_time anc) (start_time sdomw) (start_time w)).
              * apply (ancestor_lower_start_time anc sdomw). auto.
              * auto. 
            }
            auto.
        }
        contradiction.
  }
  split.
  - rewrite H4. auto.
  - red. intros. apply (f_equal start_time) in H5.
    apply (Nat.lt_neq) in H3. auto.
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
