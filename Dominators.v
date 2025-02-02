Require Import PeanoNat.
Require Import Classical_Pred_Type.

Section Dominators.

(* The number of vertices in the flow graph, including the root.
 * Nodes are numbered [0, num_nodes); 0 is the root. *)
Variable (num_nodes : nat).

(* The edges of the depth first search tree (DFS tree). *)
Variable (tree_edges: nat -> nat -> Prop).

(* The edges in the flow graph that are not part of the DFS tree. *)
Variable (other_edges: nat -> nat -> Prop).

(* This node exists within the flow graph *)
Definition node_in_fg (n : nat) := n < num_nodes.

(* there is a tree edge from [A] to [B] *)
Notation "A --> B" := (tree_edges A B) (at level 70).

(* there is a non-tree edge from [A] to [B] *)
Notation "A ~~> B" := (other_edges A B) (at level 70).
  
(* there is an edge (either tree or non-tree) from [A] to [B] *)
Notation "A ==> B" := (A --> B \/ A ~~> B) (at level 70).

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

(* there exists a possibly empty path from [A] to [B] in the DFS tree *)
Notation "A -*> B" :=
  (exists p : path A B, path_is_in_tree p) (at level 70).

(* there exists a nonempty path from [A] to [B] in the DFS tree *)
Notation "A -+> B" := ((A -*> B) /\ (A <> B)) (at level 70).

(* If a path consists only of tree edges, then any (right-)subpath also
 * consists only of tree edges. *)
Lemma path_subpath_in_tree_right :
  forall a a' b : nat, forall p : path a b, path_contains a' p ->
    path_is_in_tree p -> exists p' : path a' b, path_is_in_tree p'.
Proof.
  intros.
  induction p as [a b | a b a'' p''].
  - (* Base case: [p] is [path_refl]. We use that [a = a' = b]. *)
    assert (b = a') by (destruct H; auto).  
    assert (e' := e).
    rewrite H1 in e'. rewrite <- e'.
    exists (path_refl a b e). auto.
  - (* Inductive case: p is path_prepend. *)
    destruct H.
    + (* Case 1: [a = a'] (paths [a]-to-[b] and [a']-to-[b] are equal). *)
      rewrite <- H. exists (path_prepend a b a'' p'' o). auto.
    + (* Case 2: [path_contains a'' b a' p'']
       * ([a'] is in remainder of path). *)
      destruct H0. apply IHp''; auto.
Qed.

Axiom FG_valid__path_from_root : forall n : nat, node_in_fg n ->
  exists p : path 0 n, path_is_in_tree p.
Axiom FG_valid__node_has_par : forall n : nat, node_in_fg n ->
  exists par : nat, par --> n.
Axiom FG_valid__par_earlier : forall n par : nat, par --> n -> par < n.

(* Lemma 1 from Lengauer, Tarjan:
 *  "If [v], [w] are vertices of G such that [v <:= w], then any
 *   Path from [v] to [w] contains some common ancestor of
 *   [v] and [w] in the DFS tree."
 *
 * This lemma is presented without proof in Lengauer and Tarjan's paper.
 * As it is a true fact for DFS trees in general, we take it as an axiom.
 ***)
Axiom LT_Lemma1 : 
  forall v w : nat, v <= w -> forall p : path v w,
    exists m : nat, path_contains m p /\ m -*> v /\ m -*> w.

(* Simple helper lemmas. *)
Lemma ancestor_lower_start_time : forall n m : nat , n -*> m -> n <= m.
Proof.
  intros n m [p]. induction p.
  - apply Nat.eq_le_incl. auto.
  - destruct H. apply Nat.lt_le_incl.
    apply (Nat.lt_le_trans _ a' _).
    + apply FG_valid__par_earlier. auto.
    + apply IHp. auto.
Qed.

Lemma strict_ancestor_lower_start_time :
  forall n m : nat , n -+> m -> n < m.
Proof.
  intros n m [[p Hp] e]. destruct p.
  - contradiction.
  - destruct Hp.
    apply (Nat.lt_le_trans _ a' _).
    + apply FG_valid__par_earlier. auto.
    + apply ancestor_lower_start_time. exists p. auto.
Qed.

Fixpoint is_sdom_path_helper {n m : nat} (p : path n m) : Prop :=
  match p with
  | path_refl _ _ _ => True
  | path_prepend _ _ n' p' _ => n > m /\ is_sdom_path_helper p'
  end.

Definition is_sdom_path {n m : nat} (p : path n m) : Prop :=
  match p with
  | path_refl _ _ _ => True
  | path_prepend _ _ n' p' _ => is_sdom_path_helper p'
  end.

(* We define [sdom_candidate n m] to be true if and only if there
 * exists a path [n ~~> v_1 ~~> ... ~~> v_n ~~> m] such that
 * [v_i >: m] for all [i] in [1..=m]. *)
Definition sdom_candidate (n m : nat) : Prop :=
  exists p : path n m, is_sdom_path p.

(* We define [is_sdom_of A B] to be true if [A] is the [<:]-minimum
 * node of all [sdom_candidate]s of [B] *)
Definition is_sdom_of (n m : nat) : Prop :=
  m <> 0 /\ (sdom_candidate n m /\ forall c, sdom_candidate c m -> n <= c).

(* We define [dom A B] to be true if [A] dominates [B], i.e.,
 * every path from the root to [B] must go through [A], and [A <> B]. *)
Inductive dom : nat -> nat -> Prop :=
  | is_dom (n m : nat) : n <> m ->
      (forall p : path 0 m, path_contains n p) -> dom n m.

(* We define [is_idom_of A B] to be true if [A] is the
 * immediate dominator of [B], i.e.,
 * [A] dominates [B] and every other dominator of [B] dominates [A]. *)
Inductive is_idom_of : nat -> nat -> Prop :=
  | is_idom (n m : nat) : dom n m -> (forall k : nat,
      node_in_fg k -> dom k m -> dom k n) ->
        is_idom_of n m.

(* Each node [w <> r] in the flowgraph has exactly one imm. dominator *)
Theorem LT_Theorem1_Part1 :
  forall n : nat, node_in_fg n ->
    (exists id : nat, forall id' : nat, id = id' <-> is_idom_of id' n).
Proof. Admitted.

Theorem LT_Lemma2_Helper :
  forall w domw : nat, dom domw w -> node_in_fg w ->
    w <> 0 -> domw -+> w.
Proof.
  intros.
  (* Proof idea: all paths from [0] to [w] must go through [domw].
   * There exists at least one such path that only uses tree edges,
   * as each node is reachable from the root using only tree edges.
   * Therefore, this path must contain a subpath from [domw] to [w]. *)
  assert (exists p : path 0 w, path_is_in_tree p) as [path_0_w tree_path]
    by (apply FG_valid__path_from_root; auto).
  assert (path_contains domw path_0_w) as idomw_in_path_0_w
    by ( repeat (destruct H as [domw w]); auto ).
  assert (exists p' : path domw w, path_is_in_tree p'). {
    apply (path_subpath_in_tree_right 0 domw w path_0_w).
    apply idomw_in_path_0_w.
    assumption.
  }
  split.
  - auto.
  - destruct H. auto.
Qed.

(* Lemma 2 of the paper of Lengauer and Tarjan states the following:
 *
 *  "For any vertex [w <> r], [idom(w) -+> w]."
 *)
Theorem LT_Lemma2 :
  forall w idomw : nat, is_idom_of idomw w -> node_in_fg w ->
    w <> 0 -> idomw -+> w.
Proof.
  (* Whereas the paper states the result only for _immediate_ dominators,
   * it turns out that this is an unnecessary assumption. We prove the more
   * general version of the lemma in [LT_Lemma2_Helper]; our current proof
   * is thereby reduced to simply using that lemma. *)
  intros. destruct H.
  apply LT_Lemma2_Helper; auto.
Qed.

Lemma sdom_path_helper_property :
  forall n m s : nat, forall p : path n m,
    is_sdom_path_helper p -> path_contains s p -> s >= m.
Proof.
  intros.
  induction p.
  - simpl in H0. apply Nat.eq_le_incl. auto.
  - simpl in H. destruct H. simpl in H0.
    destruct H0.
    + rewrite <- H0. apply Nat.lt_le_incl. auto.
    + apply IHp; auto.
Qed.

Lemma LT_Lemma3_Helper :
  forall n m s : nat, forall p : path n m,
    is_sdom_path_helper p -> s < m -> ~ path_contains s p.
Proof.
  intros. red. intros.
  assert (s >= m) by (apply (sdom_path_helper_property n m s p); auto).
  assert (~ s >= m) by (apply Nat.lt_nge; auto).
  contradiction.
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
  assert (sdomw < w).
  {
    apply (Nat.le_lt_trans sdomw parw w).
    - apply sdomw_minimal_cand. assert (e1 : w=w) by reflexivity.
      assert (e2 : parw ==> w) by (left; auto).
      exists (path_prepend parw w w (path_refl w w e1) e2). simpl. auto.
    - apply FG_valid__par_earlier. auto.
  }
  (* Part 3: by Lemma 1 of the paper of Lengauer and Tarjan, the path from
   * [sdomw] to [w] contains a common ancestor [anc] of [sdomw] and [w]. *)
  assert (exists m : nat, path_contains m path_sdomw_w /\
      m -*> sdomw /\ m -*> w) as ex_anc. {
    apply (LT_Lemma1 sdomw w).
    apply Nat.lt_le_incl. auto.
  }
  destruct ex_anc as [anc anc_comm_anc].
  destruct anc_comm_anc as [path_cts_anc [anc_to_sdomw anc_to_w]].
  (* Part 4: prove that [sdomw = anc], from which the final goal follows.
   * How we do it: we use the path [path_sdomw_w], of which it is known that
   * all strictly intermed. nodes are [>: w]. As [anc] is an ancestor of [w],
   * by tree properties, we have [anc <:= w]. Thus, [anc] cannot be equal to
   * any of the intermed. nodes. Thus, [anc] must be either equal to [sdomw]
   * or to [w]. [anc] can also not be equal to [w] because it is known that
   * [anc <:= sdomw <: w]. Hence, the only possibility left is [anc = sdomw].
   * The proof makes use of induction, which is
   * delegated to the helper lemma [LT_Lemma3_Helper]. *)
  assert (sdomw = anc). {
    destruct path_sdomw_w as [ | sdomw' path_sdomw'_w o].
    - destruct path_cts_anc. auto.
    - destruct path_cts_anc.
      + auto.
      + assert (~ path_contains anc path_sdomw'_w). {
          apply LT_Lemma3_Helper.
          - auto. 
          - assert (anc < w). {
              apply (Nat.le_lt_trans anc sdomw w).
              * apply (ancestor_lower_start_time anc sdomw). auto.
              * auto. 
            }
            auto.
        }
        contradiction.
  }
  split.
  - rewrite H4. auto.
  - red. intros.
    apply (Nat.lt_neq) in H3. auto.
Qed.

(* Casts a path of type [path n m] to the equivalent path of
 * type [path n' m'] if it is given that [n = n'] and [m = m']. 
 * (This is just to please Coq's type system...) *)
Definition path_cast {n n' m m' : nat} (e1: n = n')
  (e2 : m = m') (p : path n m) : path n' m'.
  rewrite e1 in p.
  rewrite e2 in p.
  auto. Show Proof.
Defined.

(* The [path_contains] property is preserved under [path_cast]. *)
Lemma path_cast_preserves_path_contains :
  forall {n n' m m' s: nat} (e1: n = n') (e2 : m = m') (p : path n m),
    path_contains s (path_cast e1 e2 p) -> path_contains s p.
Proof.
  intros.
  rewrite <- e1 in H.
  rewrite <- e2 in H.
  auto.
Qed.

(* Path concatenation *)
Fixpoint path_concat {n n' m : nat}
    (p1 : path n n') (p2 : path n' m) : path n m :=
  match p1 with
  | path_refl _ _ e => path_cast (eq_sym e) eq_refl p2
  | path_prepend _ _ n'' p1' e =>
      path_prepend n m n'' (path_concat p1' p2) e
  end.

(* path concatenation *)
Notation "A +++ B" := (path_concat A B) (at level 50).

(* If a property is true of all nodes in some path [p1] and
 * also of all nodes in some path [p2], then it is true of all
 * nodes in the concatenation of [p1] and [p2]. *)
Lemma path_concat_preserves_path_contains :
  forall n n' m : nat, forall p1 : path n n', forall p2 : path n' m,
    forall P : nat -> Prop,
      (forall x : nat, path_contains x p1 -> P x) ->
      (forall x : nat, path_contains x p2 -> P x) ->
      (forall x : nat, path_contains x (p1 +++ p2) -> P x).
Proof.
  intros.
  induction p1.
  - simpl in H1.
    apply H0.
    apply (path_cast_preserves_path_contains (eq_sym e) eq_refl p2).
    auto.
  - simpl in H1.
    destruct H1.
    + apply (H x). simpl. left. auto.
    + apply (IHp1 p2).
      * intros. apply (H x0). right. auto.
      * auto.
      * auto.
Qed.

(* Lemma 4 of the paper of Lengauer and Tarjan states the following:
 *
 *  "For any vertex w <> r, idom(w) -*> sdom(w)."
 *)
Theorem LT_Lemma4 :
  forall w idomw sdomw : nat, node_in_fg w -> node_in_fg idomw ->
    node_in_fg sdomw -> is_idom_of idomw w -> is_sdom_of sdomw w
      -> (node_in_fg w /\ w <> 0) -> idomw -*> sdomw.
Proof.
  intros w idomw sdomw infg1 infg2 infg3 H1 H2 [H3 H4].
  (* We construct the path [p1] as the DFS tree path from [0] to [w]. *)
  assert (ex_p1 : exists p1: path 0 w, forall n : nat,
      path_contains n p1 -> n -*> sdomw \/ n <= w). {
    specialize FG_valid__path_from_root with (n := w).
    intros H'. apply H' in H3. clear H' H4.
    destruct H3 as [p Hp]. exists p. intros. right.
    apply ancestor_lower_start_time.
    apply (path_subpath_in_tree_right 0 n w p); auto.
  }
  destruct ex_p1 as [p1 Hp1].
  (* We construct the path [p2] as the path that is the concatenation
   * of the DFS tree path from [0] to [sdomw] and the path from
   * [sdomw] to [w] for which all intermediate nodes are [>: w]
   * (such a path exists by definition because [sdomw] is
   * the semidomimator of [w]). *)
  assert (ex_p2 : exists p2 : path 0 w, forall n : nat,
      path_contains n p2 -> n -*> sdomw \/ n >= w). {
    assert (ex_p_sd : 0 -*> sdomw)
      by (apply FG_valid__path_from_root; auto).
    destruct ex_p_sd as [p2a]. assert (H2' := H2).
    destruct H2' as [H2a [[p2b Hp2] H2c]].
    exists (p2a +++ p2b).
    apply path_concat_preserves_path_contains.
    - intros. left.
      apply (path_subpath_in_tree_right 0 x sdomw p2a); auto.
    - intros.
      destruct p2b.
      + assert (sdomw <> w). {
          apply Nat.lt_neq.
          apply strict_ancestor_lower_start_time.
          apply LT_Lemma3; auto.
        }
        assert (e' := e).
        contradiction.
      + simpl in Hp2.
        destruct H0.
        * left. exists (path_refl x sdomw (eq_sym H0)). simpl. auto.
        * right. apply (sdom_path_helper_property a' w _ p2b); auto.
  }
  destruct ex_p2 as [p2 Hp2].
  (* Now we constructed two paths from [0] to [w].
   * The path [p1] has the property that all its vertices
   * are either an ancestor of [sdomw] or are [<:= sdomw].
   * The path [p2] has the property that all its vertices
   * are either an ancestor of [sdomw] or are [>:= sdomw].
   * As [idomw] by definition is a vertex of all paths from [0] to [w],
   * we find that either [idomw -*> sdomw], in which the goal is proven, or
   * [start_time idomw = start_time w], which contradicts [LT_Lemma2].*)
  specialize Hp1 with (n := idomw).
  specialize Hp2 with (n := idomw).
  assert (H1' := H1).
  destruct H1 as [idomw w Hi _].
  destruct Hi as [idomw w _ Hi].
  assert (Hlhs : idomw -*> sdomw \/ idomw <= w)
    by (apply Hp1; specialize Hi with (p := p1); auto).
  assert (Hrhs : idomw -*> sdomw \/ idomw >= w)
    by (apply Hp2; specialize Hi with (p := p2); auto).
  destruct Hlhs.
  - auto.
  - destruct Hrhs.
    + auto.
    + assert (idomw = w)
        by (apply (Nat.le_antisymm); auto).
      assert (idomw <> w). {
        apply Nat.lt_neq.
        apply strict_ancestor_lower_start_time.
        apply LT_Lemma2; auto.
      }
      contradiction.
Qed.

Lemma tree_path_start_times_between_start_end {n m: nat} :
  forall (p : path n m) (s : nat), path_is_in_tree p ->
    path_contains s p -> (n <= s /\ s <= m).
Proof.
  induction p.
  - intros. simpl in H0.
    split; apply Nat.eq_le_incl
      ; ((rewrite e || rewrite H0); auto).
  - intros. simpl in H0.
    destruct H0.
    + split.
      * apply Nat.eq_le_incl. auto.
      * rewrite <- H0.
        specialize IHp with (s := a').
        apply (Nat.le_trans _ a' _).
        -- apply Nat.lt_le_incl.
           apply FG_valid__par_earlier.
           simpl in H. destruct H as [H _]. auto.
        -- apply IHp.
           ++ simpl in H. destruct H as [_ H]. auto.
           ++ destruct p; simpl; auto.
    + simpl in H. split.
      * apply (Nat.le_trans _ a' _).
        -- apply Nat.lt_le_incl.
           apply FG_valid__par_earlier.
           destruct H as [H _]. auto.
        -- destruct H. apply IHp; auto.
      * destruct H. apply IHp; auto.
Qed.

Lemma all_neq_not_path_contains {a b : nat} (p : path a b) (el : nat) :
  (forall s : nat, path_contains s p -> s <> el) ->
    ~ path_contains el p.
Proof.
  intros.
  induction p.
  - apply H. simpl. auto.
  - simpl. red. intros H0.
    destruct H0.
    + simpl in H.
      assert (a <> el) by (apply H;  auto).
      contradiction.
    + simpl in H.
      assert (~ path_contains el p) by
        (apply IHp; intros; apply H; auto).
      contradiction.
Qed.

Lemma not_path_contains_all_neq {a b : nat} (p : path a b) (el : nat) :
  ~ path_contains el p ->
    (forall s : nat, path_contains s p -> s <> el).
Proof. 
  intros H s H0.
  induction p.
  - simpl in H0. simpl in H.
    rewrite <- H0. auto.
  - simpl in H0. simpl in H.
    destruct H0.
    + rewrite H0 in H.
      red. intros. red in H.
      apply H. auto.
    + apply IHp.
      * red. intros. red in H.
        apply H. auto.
      * auto.
Qed.

(* Helper lemma for the real lemma 5 from Lengauer and Tarjan's paper. *)
Lemma LT_Lemma5_Helper : forall v w idomv idomw : nat,
  node_in_fg v -> node_in_fg idomv -> node_in_fg w -> node_in_fg idomw ->
    is_idom_of idomv v -> is_idom_of idomw w ->
      v -*> w -> idomv -+> idomw -> idomw -+> v -> False.
Proof.
  intros v w idomv idomw ifg1 ifg2 ifg3 ifg4 idom1 idom2 H1 H2 H3.
  assert (ex_p1 : exists p1 : path 0 v, ~ path_contains idomw p1). {
    apply not_all_ex_not.
    red. intros.
    assert (dom idomw v) by (split; try (apply H3); auto).
    (* If [dom idomw v], then we must have [dom idomw idomv],
     * because [idomv] is dominated by all other dominators of [v]
     * by definition. Consider now the DFS tree path from [0] to [idomv];
     * it contains only vertices that are [<:= idomv], and it must
     * contain [idomw], which is [>: idomv]. This is a contradiction. *)
    destruct idom1 as [idomv v Hv1 Hv2].
    specialize Hv2 with (k := idomw).
    assert (Hwv : dom idomw idomv) by (apply Hv2; auto).
    clear Hv2.
    assert (ex_p' : 0 -*> idomv) by (apply FG_valid__path_from_root; auto).
    destruct ex_p' as [p' Hp'].
    assert (Hwv' := Hwv).
    destruct Hwv as [idomw idomv _ Hwv].
    specialize Hwv with (p := p').
    assert (idomw <= idomv) by
      (apply (tree_path_start_times_between_start_end p' idomw); auto).
    assert (idomw > idomv). {
      apply strict_ancestor_lower_start_time.
      auto.
    }
    assert (~ idomw <= idomv) by (apply Nat.lt_nge; auto).
    contradiction.
  }
  (* Now we concatenate this path ([p1]) with the tree path from [v] to [w]
   * ([p2]). This yields a path from [0] to [w] that does not include
   * [idomw], which is again a contradiction. *)
  destruct ex_p1 as [p1 Hp1].
  destruct H1 as [p2 Hp2].
  assert (~ path_contains idomw (p1 +++ p2)). {
    apply all_neq_not_path_contains.
    apply path_concat_preserves_path_contains.
    - apply not_path_contains_all_neq. auto.
    - intros. red. intros H0. rewrite H0 in H. clear H0.
      apply strict_ancestor_lower_start_time in H3.
      apply Nat.lt_nge in H3.
      assert (v <= idomw) by
        (apply (tree_path_start_times_between_start_end p2); auto).
      contradiction.
  }
  destruct idom2 as [idomw w Hi2 _].
  destruct Hi2 as [idomw w _ Hi2].
  specialize Hi2 with (p := p1 +++ p2).
  contradiction.
Qed.

Lemma path_subpath_in_tree_general {a b : nat} (p : path a b) (n m : nat) :
  path_contains n p -> path_contains m p -> n -*> m \/ m -*> n.
Proof.
Admitted.

Lemma start_time_lt_nge : forall n m : nat, n < m <-> ~ m <= n.
Proof. Admitted.

(* Lemma 5 of the paper of Lengauer and Tarjan states the following:
 *
 *  "Let vertices v,w satisfy v -*> w.
 *   Then v -*> idom(w) or idom(w) -*> idom(v)."
 *
 * We make the additional assumption that [w <> 0], which is implicit in
 * the paper. This has to be assumed, because the root has no dominator,
 * so the statement would be ill-defined if this assumption wasn't made.
 *)
Theorem LT_Lemma5 :
  forall v w idomv idomw : nat, w <> 0 -> is_idom_of idomw w ->
    is_idom_of idomv v -> (node_in_fg v /\ node_in_fg w /\ v -*> w) ->
      (v -*> idomw \/ idomw -*> idomv).
Proof.
  intros v w idomv idomw H1 H2 H3 H4.
  destruct H4 as [H4a [H4b H4c]].
  (*
  (* Proof idea: [idomw] must lie on the tree path from [0] to [w].
     The nodes [v] and hence [idomv] also lie on this tree path.
     So we do case analysis:
     we have that either [v -*> idomw] (proves goal) or [idomw -+> v], in which case we have that either [idomw -*> idomv] (proves goal) or [idomv -+> idomw]. In this latter case, where [idomv -+> idomw -+> v], we need to do additional work, but let's get there first.
    *)
  destruct H4c as [p Hp].
  assert (path_contains v p). {
    destruct p.
    - simpl. symmetry. auto.
    - simpl. left. reflexivity.
  }
  assert (path_contains idomw p). {
    (* A dominator of [w] is contained in any path from [0] to [w]. *)
    destruct H2 as [idomw w H2a H2c].
    destruct H2a as [idomw w H2a H2b].
    specialize H2b with (p := p).
  }
  assert (disj1 : v -*> idomw \/ idomw -+> v). {
    apply (path_subpath_in_tree_general p).
    - destruct 
  }
  *)

  assert (Ha : idomv -+> idomw) by admit.
  assert (Hb : idomw -+> v) by admit.
  (* Now that we know [idomv -+> idomw] and [idomw -+> v],
   * we work toward a contradiction. *)


  

Admitted.

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
          (node_in_fg u /\ sdomw -+> u /\ u -*> w) -> sdomu >= sdomw
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
          (forall u' : nat, (sdomw -+> u' /\ u' -*> w) -> u <= u') ->
    (sdomu <= sdomw /\ idomu = idomw).
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
          (forall u' : nat, (sdomw -+> u' /\ u' -*> w) -> u <= u') ->
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
    fun x => (x ==> w /\ x < w) \/
      (
        exists u v : nat, is_sdom_of x u /\ node_in_fg u /\
          node_in_fg v /\ u > w /\ v ==> w /\ u -*> v
      )
  )
.
Proof. Admitted.

End Dominators.
