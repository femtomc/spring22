(** * Correctness of Binary Search Trees (BSTs) *)

(* This week we'll continue proving the correctness of a binary search tree implementation.
 * BSTs are a famous data structure for finite sets, allowing fast (log-time)
 * lookup, insertion, and deletion of items. (We omit the rebalancing heuristics
 * needed to achieve worst-case log-time operations, but you will prove the
 * correctness of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* As usual, a set of spoiler-containing hints to help you along when you 
 * get stuck with certain pset questions has been provided at the bottom of 
 * the signature file! *)

Require Import Frap Datatypes Pset4Sig.
Require Import Compare_dec.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

Module Impl.
  (* Trees are an inductive structure, where [Leaf] doesn't have any items,
   * whereas [Node] has an item and two subtrees. Note that a [tree] can
   * contain nodes in arbitrary order, so not all [tree]s are valid binary
   * search trees. *)

  (* (* Imported from Sig file: *)
  Inductive tree :=
  | Leaf (* an empty tree *)
  | Node (d : t) (l r : tree).
   *)
  (* Then a singleton is just a node without subtrees. *)
  Definition Singleton (v: t) := Node v Leaf Leaf.

  (* [bst] relates a well-formed binary search tree to the set of elements it
     contains. Note that invalid trees with misordered elements are not valid
     representations of any set. All operations on a binary tree are specified
     in terms of how they affect the set that the tree represents. That
     set is encoded as function that takes a [t] and returns the proposition "[t]
     is in this set". *)
  Fixpoint bst (tr : tree) (s : t -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node d l r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)
  Fixpoint member (a: t) (tr: tree) : bool :=
    match tr with
    | Leaf => false
    | Node v lt rt =>
      match compare a v with
      | Lt => member a lt
      | Eq => true
      | Gt => member a rt
      end
    end.

  (* Here is a typical insertion routine for BSTs.
   * From a given value, we recursively compare the value with items in
   * the tree from the root, until we find a leaf whose place the new value can take. *)
  Fixpoint insert (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Singleton a
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (insert a lt) rt
      | Eq => tr
      | Gt => Node v lt (insert a rt)
      end
    end.

  (* Helper functions for [delete] below. The *main task* in this pset
     is to understand, specify, and prove these helpers. *)
  Fixpoint rightmost (tr: tree) : option t :=
    match tr with
    | Leaf => None
    | Node v _ rt =>
      match rightmost rt with
      | None => Some v
      | r => r
      end
    end.

  Definition is_leaf (tr : tree) : bool :=
    match tr with Leaf => true | _ => false end.

  Fixpoint delete_rightmost (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      if is_leaf rt
      then lt
      else Node v lt (delete_rightmost rt)
    end.

  Definition merge_ordered lt rt :=
    match rightmost lt with
    | Some rv => Node rv (delete_rightmost lt) rt
    | None => rt
    end.

  (* [delete] searches for an element by its value and removes it if it is found.
     Removing an element from a leaf is degenerate (nothing to do), and
     removing the value from a node with no other children (both Leaf) can be done
     by replacing the node itself with a Leaf. Deleting a non-leaf node is
     substantially trickier because the type of [tree] does not allow for a Node
     with two subtrees but no value -- merging two trees is nontrivial. The
     implementation here removes the value anyway and then moves the rightmost
     node of the left subtree up to replace the removed value. This is equivalent
     to using rotations to move the value to be removed into leaf position and
     removing it there. *)
  Fixpoint delete (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (delete a lt) rt
      | Eq => merge_ordered lt rt
      | Gt => Node v lt (delete a rt)
      end
    end.

  (* Here is a lemma that you will almost definitely want to use. *)
  Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
  Proof.
    induct tr; simplify.
    { rewrite <- H0. apply H with (x:=x). }
    rewrite H0 in H.
    propositional.
    { apply IHtr1 with (P:=(fun x : t => (fun d => P x /\ x < d) d));
        propositional; cycle 1.
      { rewrite H0; trivial. }
      { rewrite <-H0; trivial. } }
    { apply IHtr2 with (P:=(fun x : t => (fun d => P x /\ d < x) d));
      propositional; cycle 2.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
  Qed.

  (* You may want to call these tactics to use the previous lemma. *)
  (* They are just a means to save some typing of [apply ... with]. *)
  Ltac use_bst_iff known_bst :=
    lazymatch type of known_bst with
    | bst ?tree2 ?set2 =>
      lazymatch goal with
      | |- bst ?tree1 ?set1 =>
        apply bst_iff with (P:=set2) (Q := set1);
        lazymatch goal with
        |- bst tree2 set2 => apply known_bst
        | _ => idtac
        end
      end
    end.

  Ltac use_bst_iff_assumption :=
    match goal with
    | H : bst ?t _ |- bst ?t _ =>
      use_bst_iff H
    end.

  (* If you are comfortable with it, [eapply bst_iff] followed by careful
   * application of other [bst] facts (e.g., inductive hypotheses) can
   * save typing in some places where this tactic does not apply, though
   * keep in mind that forcing an incorrect choice for a ?unification
   * variable can make the goal false. *)

  (* It may also be useful to know that you can switch to proving [False] by
   * calling [exfalso]. This, for example, enables you to apply lemmas that end in
   * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

  (* Other tactics used in our solution: apply, apply with, apply with in
   * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
     linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

  (* Warm-up exercise: rebalancing rotations *)

  (* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
     The AA-tree rebalancing algorithm applies these only if the annotations of relevant
     subtrees are in violation of a performance-critical invariant, but the rotations
     themselves are correct regardless. (These are straight from
     https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)

  (* Each one can be written as a simple non-recursive definition
     containing two "match" expressions that returns the original
     tree in cases where the expected structure is not present. *)

  (* HINT 1 (see Pset4Sig.v) *)
  Definition rotate (T : tree) : tree :=
    match T with
    | Node t L R =>
      match L with
      | Node l A B => Node l A (Node t B R)
      | _ => T
      end
    | _ => T
    end.

  Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
    cases T; propositional.
    cases T1; propositional.
    simplify; propositional;
      use_bst_iff_assumption; propositional; linear_arithmetic.
  Qed.

  (* There is a hint in the signature file that completely gives away the proofs
   * of these rotations. We recommend you study that code after completing this
   * exercise to see how we did it, maybe picking up a trick or two to use below. *)

  Lemma bst_insert : forall tr s a, bst tr s ->
bst (insert a tr) (fun x => s x \/ x = a).
  Proof.
    intros.
    induct tr; propositional; simplify; propositional.
    apply H in H0. assumption. linear_arithmetic.
    apply H in H0. assumption. linear_arithmetic.
    cases (compare a d); simplify; propositional.
    eapply bst_iff. apply IHtr1. apply H.
    propositional; linear_arithmetic.
    eapply bst_iff.
    apply H2. propositional.
    linear_arithmetic.
    eapply bst_iff.
    apply H.
    propositional.
    linear_arithmetic.
    eapply bst_iff.
    apply H2.
    propositional.
    linear_arithmetic.
    eapply bst_iff.
    apply H.
    propositional.
    linear_arithmetic.
    eapply bst_iff.
    apply IHtr2.
    apply H2.
    propositional.
    linear_arithmetic.
  Qed.

  (* To prove [bst_delete], you will need to write specifications for its helper
     functions, find suitable statements for proving correctness by induction, and use
     proofs of some helper functions in proofs of other helper functions. The hints
     in the signature file provide examples and guidance but no longer ready-to-prove
     lemma statements. For time-planning purposes: you are not halfway done yet.
     (The Sig file also has a rough point allocation between problems.)

     It is up to you whether to use one lemma per function, multiple lemmas per
     function, or (when applicable) one lemma per multiple functions. However,
     the lemmas you prove about one function need to specify everything a caller
     would need to know about this function. *)

  (* This is cheeky, but helpful *)
  Lemma rightmost_none_implies_leaf :
    forall tr, rightmost tr = None -> tr = Leaf.
  Proof.
    induct tr; propositional; simplify.
    cases (rightmost tr2); simplify.
    equality.
    equality.
  Qed.

  Lemma rightmost_prop :
    forall tr P n, bst tr P
              -> (rightmost tr = Some n)
              -> P n.
  Proof.
    intros.
    induct tr.
    simplify.
    equality.
    simplify.
    cases (rightmost tr2).
    destruct H.
    destruct H1.
    eapply IHtr2 in H2.
    apply H2.
    assumption.
    destruct H.
    destruct H1.
    equality.
  Qed.

  Lemma rightmost_max :
    forall tr P n, bst tr P
              -> (rightmost tr = Some n)
              -> bst tr (fun x : t => P x /\ x <= n).
  Proof.
    intros.
    induct tr; propositional; simplify.
    equality. propositional.
    cases (rightmost tr2); simplify.
    apply IHtr2 with (n := n) in H3.
    eapply rightmost_prop with (n := n0) in H3.
    destruct H3.
    destruct H2.
    linear_arithmetic.
    assumption.
    assumption.
    assert (d = n).
    equality.
    linear_arithmetic.
    cases (rightmost tr2); simplify.
    eapply IHtr2 with (n := n) in H3.
    apply rightmost_prop with (n := n0) in H3.
    eapply bst_iff.
    apply H.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    eapply bst_iff.
    apply H.
    propositional.
    assert (x < n).
    equality.
    linear_arithmetic.
    cases (rightmost tr2); simplify.
    eapply IHtr2 in H3.
    eapply bst_iff.
    apply H3.
    propositional.
    apply H5.
    assumption.
    assumption.
    apply rightmost_none_implies_leaf in Heq; simplify.
    rewrite Heq.
    simplify.
    propositional.
    assert (d = n) by equality.
    linear_arithmetic.
  Qed.

  Lemma delete_rightmost_prop :
    forall tr P n , bst tr P
               -> (rightmost tr = Some n)
               -> bst (delete_rightmost tr) (fun x : t => P x /\ x < n).
  Proof.
    intros.
    induct tr; simplify; propositional.
    equality.
    cases (is_leaf tr2); simplify.
    cases (rightmost tr2); simplify.
    cases tr2; simplify.
    equality.
    equality.
    eapply bst_iff.
    apply H.
    propositional.
    assert ( d = n ) by equality.
    linear_arithmetic.
    assert ( d = n ) by equality.
    linear_arithmetic.
    propositional.
    cases (rightmost tr2); simplify.
    eapply rightmost_prop in H3.
    apply H3.
    equality.
    apply rightmost_none_implies_leaf in Heq0.
    rewrite Heq0 in Heq; simplify.
    equality.
    cases (rightmost tr2); simplify.
    eapply bst_iff.
    apply H.
    propositional.
    eapply rightmost_prop with (n := n0) in H3.
    destruct H3.
    assert (n0 = n) by equality.
    rewrite H6 in H3.
    linear_arithmetic.
    assumption.
    apply rightmost_none_implies_leaf in Heq0.
    rewrite Heq0 in Heq.
    simplify.
    equality.
    cases (rightmost tr2); simplify.
    eapply IHtr2 in H3.
    eapply bst_iff.
    apply H3.
    propositional.
    apply H5.
    assumption.
    assumption.
    apply rightmost_none_implies_leaf in Heq0.
    rewrite Heq0 in Heq.
    simplify.
    equality.
  Qed.

  Lemma rightmost_merge_ordered :
    forall tr2 tr1 n , rightmost tr2 = Some n
               -> rightmost (merge_ordered tr1 tr2) = Some n.
  Proof.
    induct tr2; simplify; try equality; propositional.
    cases tr1; simplify.
    cases (rightmost tr2_2); simplify; try equality.
    unfold merge_ordered.
    cases (rightmost (Node d0 tr1_1 tr1_2)); simplify.
    cases (rightmost tr2_2); simplify; try equality.
    cases (rightmost tr2_2); simplify; try equality.
  Qed.

  Lemma merge_ordered_prop :
    forall tr1 tr2 P n, bst (merge_ordered tr1 tr2) P
                 -> (rightmost tr2 = Some n)
                 -> bst (merge_ordered tr1 tr2) (fun x : t => P x /\ x <= n).
  Proof.
    intros.
    induct tr2; simplify; try equality; propositional.
    cases (rightmost tr2_2); simplify.
    eapply rightmost_max in H.
    apply H.
    apply rightmost_merge_ordered; simplify.
    rewrite Heq.
    assumption.
    eapply rightmost_max.
    assumption.
    eapply rightmost_merge_ordered.
    apply rightmost_none_implies_leaf in Heq.
    rewrite Heq.
    cases tr2_1; simplify.
    equality.
    equality.
  Qed.

  Lemma partial_bst_iff :
    forall tr P n, bst tr (fun x : t => P x /\ x < n)
              -> (forall x, P x /\ n < x -> False)
              -> bst tr (fun x : t => P x /\ x <> n).
  Proof.
    intros.
    eapply bst_iff.
    apply H.
    propositional.
    linear_arithmetic.
    cases (compare x n).
    assumption.
    apply H3 in e.
    equality.
    assert (P x /\ n < x).
    equality.
    apply H0 in H1.
    equality.
  Qed.

  Lemma member_has_prop :
    forall tr P x, bst tr P -> member x tr = true -> P x.
  Proof.
    intros.
    induct tr; simplify; propositional; try equality.
    cases (compare x d); simplify; propositional.
    eapply IHtr1 in H.
    apply H.
    assumption.
    equality.
    eapply IHtr2 in H3.
    apply H3.
    equality.
  Qed.

  (* I believe this is the correct lemma, but I was unable to prove this completely. *)
  Lemma merge_ordered_less_than :
    forall tr1 tr2 P a, bst tr1 (fun x : t => P x /\ x < a)
                      -> bst tr2 (fun x : t => P x /\ a < x)
                      -> bst (merge_ordered tr1 tr2) (fun x : t => P x /\ x <> a).
  Proof.
    intros.
    induct tr2; unfold merge_ordered; cases (rightmost tr1); simplify; propositional; try equality.
    apply rightmost_prop with (n := n) in H.
    equality.
    equality.
    apply rightmost_prop with (n := n) in H.
    linear_arithmetic.
    equality.
    apply rightmost_max with (n := n) in H as Hn0.
    apply delete_rightmost_prop with (n := n) in H as Hn1.
    eapply partial_bst_iff in H as Hn.
    eapply delete_rightmost_prop with (n := n) in Hn.
    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    propositional.
    apply rightmost_prop with (n := n) in H as Hn.
    destruct Hn.
    admit.

    equality.
    eapply rightmost_none_implies_leaf in Heq.
    rewrite Heq in H.
    simplify.
    unfold not in H.
    cases (compare x a); simplify.
    eapply H.
    split.
    apply H2.
    apply l.
    eapply H3.
    assumption.
    eapply H0.
    split.
    apply H2.
    linear_arithmetic.
    apply rightmost_prop with (n := n) in H as Hn.
    equality.
    equality.
    apply rightmost_prop with (n := n) in H as Hn.
    linear_arithmetic.
    equality.
    apply rightmost_max with (n := n) in H.
    apply delete_rightmost_prop with (n := n) in H as Hn.
    eapply bst_iff.
    apply Hn.
    propositional.
    linear_arithmetic.
    cases (compare x a); simplify.
    linear_arithmetic.
    linear_arithmetic.
    apply rightmost_prop with (n := n) in H.
    linear_arithmetic.
    equality.
    linear_arithmetic.
    equality.
    equality.
    linear_arithmetic.
    apply rightmost_prop with (n := n) in H.
    linear_arithmetic.
    equality.

    apply rightmost_max with (n := n) in H.
    eapply bst_iff.
    apply H1.
    propositional.
    linear_arithmetic.
    apply rightmost_prop with (n := n) in H.
    linear_arithmetic.
    equality.
    cases (compare a n); simplify.
    apply rightmost_prop with (n := n) in H.
    linear_arithmetic.
    equality.
    linear_arithmetic.
    cases (compare a x); simplify.
    linear_arithmetic.
    linear_arithmetic.
    admit.
    equality.

    admit.
    linear_arithmetic.
    eapply rightmost_none_implies_leaf in Heq.
    rewrite Heq in H.
    simplify.
    unfold not in H.
    eapply bst_iff.
    apply H1.
    propositional.
    linear_arithmetic.
    cases (compare x a); simplify.
    assert (P x /\ x < a).
    equality.
    apply H in H5.
    equality.
    apply H7 in e.
    equality.
    linear_arithmetic.
    eapply bst_iff.
    apply H4.
    propositional.
    linear_arithmetic.
    eapply rightmost_none_implies_leaf in Heq.
    rewrite Heq in H.
    simplify.
    unfold not in H.
    cases (compare x a); simplify.
    assert (P x /\ x < a).
    equality.
    apply H in H5.
    equality.
    apply H7 in e.
    equality.
    linear_arithmetic.
  Admitted.


  (* HINT 2-5 (see Pset4Sig.v) *)
  Lemma bst_delete : forall tr s a, bst tr s ->
bst (delete a tr) (fun x => s x /\ x <> a).
  Proof.
    intros.
    induct tr; propositional; simplify; propositional.
    apply H in H1. assumption.
    cases (compare a d); propositional; simplify; propositional.
    linear_arithmetic.
    eapply IHtr1 in H.
    eapply bst_iff.
    apply H.
    propositional.
    eapply bst_iff.
    apply H2.
    propositional.
    linear_arithmetic.
    eapply merge_ordered_less_than.
    rewrite <- e in H.
    apply H.
    rewrite <- e in H2.
    apply H2.
    linear_arithmetic.
    eapply bst_iff.
    apply H.
    propositional.
    linear_arithmetic.
    eapply IHtr2 in H2.
    eapply bst_iff.
    apply H2.
    propositional.
  Qed.

(* Great job! Now you have proven all tree-structure-manipulating operations
     necessary to implement a balanced binary search tree. Rebalancing heuristics
     that achieve worst-case-logarithmic running time maintain annotations on
     nodes of the tree (and decide to rebalance based on these). The implementation
     here omits them, but as the rotation operations are correct regardless of
     the annotations, any way of calling them from heuristic code would result in a
     functionally correct binary tree. *)
End Impl.

Module ImplCorrect : Pset4Sig.S := Impl.

(* Authors:
 * Joonwon Choi
 * Adam Chlipala
 * Benjamin Sherman
 * Andres Erbsen
 * Amanda Liu
 *)
