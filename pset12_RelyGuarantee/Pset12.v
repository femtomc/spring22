(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 12 *)

Require Import Frap Pset12Sig.

Module Impl.

Ltac existT_subst :=
   repeat match goal with
   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H
     end; subst.

(* Part 1: read Pset12Sig.v and answer the questions below. This task is
 * ungraded, but we are assigning it in hope it helps you complete the
 * following parts.

(these are duplicative with past psets:)

- Which syntactic construct can be used to implement sequencing of two commands?

- Which step rules allow a sequenced program to make progress?

- Which step rule is used when a loop terminates?

- Which step rule is used when a loop continues?

- Why is there no step rule for Fail?

(these are about the programming language in this pset:)

- Which syntactic construct is used to spawn new threads?

- Which step rules allow a multi-threaded program to make progress?

- How can threads in this language communicate with each other?

- What do the steps that are factored out into the astep inductive have in common?

(these are about the program logic:)

- Which rule of the program logic handles astep commands?

- What is the meaning of the "rely" argument [R]?

- What would [R] be for a program that can run in any environment?

- What would [R] be for a program that can only run alone?

- Which constructors of [hoare_triple] change [R]? Do they make it more or less permissive?

- What is the meaning of the "guarantee" argument [G]?

- Which cases of [hoare_triple] require you to prove [G]?

- What would [G] be for a program that can run in any environment?

- What would [G] be for a program that can only run alone?

(these are about program logic tactics:)

- What syntactic forms of commands does [step] handle?

- What syntactic forms of commands does [fork] handle?

- What are the six arguments to the tactic [fork]? Classify them into two groups of three, and then (differently) classify them into three pairs.

- What syntactic forms of commands does [atomic] handle?

- What is the argument to the tactic [atomic]?
 *)

(* Part 2: prove a program *)

(* Pset12Example.v contains an example verification of a non-trivial program.
 * You can use it as a reference when trying to figure out what the rules,
 * lemmas, and tactics here do, but you are not required to understand it.
 * The program in this file is much simpler. *)

(* Verify that this program manages to increase the counter value. *)
Lemma ht_increment : forall init,
  hoare_triple
    (fun h => h $! 0 = init)
    (fun _ _ => False)
    (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
        || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
    )
    (fun _ _ => True)
    (fun _ h => h $! 0 > init).
Proof.
  simp.
  fork (fun h => h $! 0 >= init)
    (fun h h' => h = h' \/ h' $! 0 > init)
    (fun (_ : unit) h => h $! 0 > init)
    (fun h => h $! 0 >= init)
    (fun h h' => h = h' \/ h' $! 0 > init)
    (fun (_ : unit) h => h $! 0 > init).
  eapply HtBind.
  eapply HtAtomic.
  simp.
  simp.
  instantiate (1 := (fun n h' => n >= init)).
  simp.
  simp.
  simp.
  eapply HtAtomic.
  simp.
  simp.
  simp.
  eapply HtBind.
  eapply HtAtomic.
  simp.
  simp.
  instantiate (1 := (fun n h' => n >= init)).
  simp.
  simp.
  simp.
  eapply HtAtomic.
  simp.
  simp.
  simp.
  simp.
  simp.
  simp.
  simp.
  simp.
Qed.

(* Part 3: prove soundness of the program logic *)

(* Now it remains to prove that having a [hoare_triple] actually means
 * that execution will proceed safely, and if the program terminates then the
 * postcondition will be satisfied. *)

(* If non-negligible time has passed since you read the sig file, please
 * review the definitions of [trsys_of] and [notAboutToFail] now. *)

(* Then, feel free to just skim the next lemmas, right until the final
 * theorem you are asked to prove. *)

(* Here are a few more lemmas that you may find helpful: *)

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
  hoare_triple P R c G Q
  -> (forall h, P' h -> P h)
  -> stableP P' R
  -> hoare_triple P' R c G Q.
Proof. eauto. Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
  hoare_triple P R c G Q
  -> (forall v h, Q v h -> Q' v h)
  -> (forall h h', G h h' -> G' h h')
  -> hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
  stableP P R
  -> (forall h, P h -> Q v h)
  -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma stableP_self : forall h R, stableP (fun h' => R^* h h') R.
Proof. simp. eauto using trc_trans. Qed.

Lemma stableP_star : forall R h h', R^* h h' ->
                               forall P, stableP P R -> P h -> P h'.
Proof. induct 1; simplify; eauto. eapply IHtrc; eauto. Qed.

Lemma stableP_weakenR : forall P R, stableP P R -> forall R' : hrel,
    (forall h1 h2, R' h1 h2 -> R h1 h2) -> stableP P R'.
Proof. simp; eauto. Qed.

Local Hint Resolve stableP_self : core.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r,
  stable P Q R -> stableP (Q r) R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableQ : core.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R,
  stable P Q R -> stableP P R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableP : core.

Lemma trc_imply :forall t R (s s' : t), R^* s s' ->
                                   forall (R':_->_->Prop), (forall s s', R s s' -> R' s s') ->
                                                 R'^* s s'.
Proof. induct 1; simplify; eauto. Qed.

Local Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Local Hint Constructors notAboutToFail : core.

Lemma progress :
  forall (t : Set) P (c : cmd t) R G Q,
  hoare_triple P R c G Q ->
  forall h, P h -> notAboutToFail c.
Proof.
  induct 1; simplify.
  eapply NatfBind.
  eauto.
  eapply NatfPar.
  eauto.
  eauto.
  equality.
  eapply NatfReturn.
  eauto.
  eauto.
  eauto.
Qed.

Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
  hoare_triple P R c G Q -> forall h,
    P h -> forall h' c', step (h, c) (h', c') -> G^* h h'.
Proof.
  induct 1; simplify.
  invert H3.
  existT_subst.
  eauto.
  existT_subst.
  eauto.
  invert H5.
  existT_subst.
  eapply trc_imply.
  eapply IHhoare_triple1.
  eapply H2.
  eauto.
  eauto.
  eauto.
  existT_subst.
  eapply trc_imply.
  eapply IHhoare_triple2.
  eapply H3.
  eauto.
  eauto.
  eauto.
  eauto.
  invert H1.
  invert H3.
  existT_subst.
  eauto.
  invert H3.
  existT_subst.
  eauto.
  eapply trc_imply.
  eapply IHhoare_triple.
  eauto.
  eauto.
  eauto.
Qed.

Lemma preservation :
  forall (t : Set) P (c : cmd t) R G Q,
  hoare_triple P R c G Q ->
  forall h, P h -> forall h' c', step (h, c) (h', c') ->
                      hoare_triple (fun h'' => R^* h' h'') R c' G Q.
Proof.
  induct 1; simp.

  (*bind case*)
  invert H3.
  simp.
  eapply HtBind.
  eapply IHhoare_triple.
  eauto.
  eauto.
  apply H0.
  simp.
  eapply HtStrengthen.
  apply H0.
  simp.
  (* had a tough time figuring out this case in return *)
  admit.
  eauto.

  (*par case*)
  invert H5.
  simp.
  eapply HtPar.
  eapply IHhoare_triple1.
  eauto.
  eauto.
  eapply H0.
  eauto.
  simp.
  eapply trc_imply.
  eauto.
  eauto.
  simp.
  assert ( (G1) ^* h h').
  eapply guarantee.
  apply H.
  eauto.
  eauto.
  apply always_stableP in H0.
  eapply stableP_star.
  apply H5.
  eapply stableP_weakenR.
  apply H0.
  simp.
  eapply stableP_star.
  apply H6.
  eapply stableP_weakenR.
  eauto.
  simp.
  eauto.
  simp.
  eapply HtPar.
  apply H.
  eapply IHhoare_triple2.
  eauto.
  eauto.
  eauto.
  assert ( (G2) ^* h h').
  eapply guarantee.
  apply H0.
  eauto.
  eauto.
  simp.
  apply always_stableP in H.
  eapply stableP_star.
  apply H6.
  eapply stableP_weakenR.
  apply H.
  simp.
  eapply stableP_star.
  apply H5.
  eapply stableP_weakenR.
  apply H.
  simp.
  eauto.
  simp.
  eapply trc_imply.
  eauto.
  eauto.

  (*return case -- atomics*)
  invert H1.
  invert H3.
  simp.
  eapply HtWeakenFancy.
  eapply HtReturn.
  eauto.
  simp.
  eapply stable_stableQ in H1.
  eapply stableP_star.
  apply H4.
  apply H1.
  eapply H0.
  eauto.
  eauto.
  eauto.
  eapply HtWeakenFancy.
  eapply HtReturn.
  eauto.
  simp.
  eapply stable_stableQ in H1.
  eapply stableP_star.
  apply H4.
  apply H1.
  eapply H0.
  eauto.
  eauto.
  eauto.

  (*loop case*)
  invert H3.
  simp.
  step.
  eapply HtStrengthen.
  eapply H.
  simp.
  eapply stableP_star.
  eauto.
  eapply always_stableP.
  eapply H.
  eauto.
  eauto.
  cases r; simp.
  eapply HtWeakenFancy.
  eapply HtReturn.
  eapply H1.
  simp.
  eauto.
  eauto.


  eapply HtConsequence.
  eapply IHhoare_triple.
  eauto.
  eauto.
  simp.
  eapply trc_imply.
  eapply H7.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Admitted.

(* HINT 1-6 (see Pset12Sig.v) *)
Theorem hoare_triple_sound :
  forall (t : Set) P (c : cmd t) Q,
  hoare_triple P
    (fun _ _ => False)
    c
    (fun _ _ => True)
    Q -> forall h, P h -> invariantFor (trsys_of h c)
                     (fun st => notAboutToFail (snd st)).
Proof.
  simp.
  apply invariant_weaken with
    (fun st => exists P, hoare_triple
              P
              (fun _ _ : heap => False)
              (snd st)
              (fun _ _ : heap => True)
              Q /\ P (fst st)).

  2: {
    simp.
    eapply progress.
    eauto.
    eauto.
  }

  eapply invariant_induction.
  simp.
  eauto.
  simp.
  cases s; simp.
  cases s'; simp.
  assert (hoare_triple
            (fun h : heap => (fun _ _ : heap => False) ^* f0 h)
            (fun _ _ : heap => False)
            c1
            (fun _ _ : heap => True)
            Q).
  eapply HtStrengthen.
  eapply preservation.
  apply H1.
  apply H4.
  apply H2.
  simp.
  simp.
  assert ((fun h : heap => (fun _ _ : heap => False) ^* f0 h) f0).
  eauto.
  eauto.
Qed.
End Impl.

Module ImplCorrect : Pset12Sig.S := Impl.
