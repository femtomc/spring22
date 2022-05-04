(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 11 *)

Require Import Frap Pset11Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset11Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Coq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog. Admitted.

(* FILL IN explanation here *)

(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset11Sig.v and briefly describing how it would
   reject it: *)

(* FILL IN explanation here *)

(* The two questions above are not graded, but we hope they help you understand
   the material better! *)

Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1.
  eauto.
  intros.
  admit.
  intros.
  right.
  left.
  eauto.
  intros.
  right.
  left.
  eauto.
  intros.
  right.
  assert (~a0 \in l0).
  eapply notin_from_order.
  equality.
  eapply H in H0.
  admit.
  intros.
  right.
  left.
  assert (a0 \in l).
  sets.
  eapply StepUnlock in H2.
  eauto.
Admitted.

Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1. intros; try sets.
  intros.
  eapply GcBind in H0.
  eapply who_has_the_lock'' in H0.
  first_order.
  invert H0.
  left.
  eauto.
  right.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  intros.
  sets.
  intros.
  assert (a0 \in l).
  sets.
  left.
  eapply StepUnlock in H.
  eauto.
  Unshelve.
  eauto.
Qed.

Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1; intros; try sets.
  eapply who_has_the_lock' in H.
  first_order.
  apply StepThread with (cs1 := []) (cs2 := progOf l0) in H.
  left.
  simplify.
  admit.
  right.
  eauto.
  admit.
Admitted.

Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  intros.
  invert H.
  sets.
  apply who_has_the_lock with
    (l := locksOf (x :: l))
    (h := h) in H0.
  first_order.
  admit.
  eauto.
  eauto.
Admitted.

Theorem if_no_locks_held_then_progress : forall h p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> locksOf p = {}
      -> Forall (fun l_c => finished (snd l_c)) p
        \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  induct 1; intros; try sets.
  cases x; simplify.
  assert (locksOf l = {}).
  sets.
  assert (s = {}).
  sets.
  rewrite H3.
  first_order.
  admit.
  eapply step_cat in H4.
  right.
  replace ({  } \cup ({  } \cup locksOf l)) with (locksOf l) by sets.
  eauto.
Admitted.

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
   reduces to proving this lemma — the only one in this Pset!  See hints at the bottom
   of the signature file if you get stuck, and of course come to office hours if you
   have any questions or need help. *)

Module Impl.
(* HINT 1-5 (see Pset11Sig.v) *)   
Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  intros.
  excluded_middle (exists a, a \in locksOf p); simplify.
  invert H0.
  eapply if_lock_held_then_progress in H.
  destruct H.
  assert (Forall finished (progOf p)).
  eapply finished_progOf.
  equality.
  equality.
  assert (exists h_l_p' : heap * locks * prog, step (h, locksOf p, progOf p) h_l_p').
  eapply H.
  equality.
  apply H1.
  assert (x < x + 1).
  linear_arithmetic.
  apply H0.
  unfold not in H0.
  eapply if_no_locks_held_then_progress in H.
  destruct H.
  assert (Forall finished (progOf p)).
  eapply finished_progOf.
  equality.
  equality.
  assert (exists h_l_p' : heap * locks * prog, step (h, locksOf p, progOf p) h_l_p').
  eapply H.
  equality.
  remember (locksOf p).
  sets.
  eapply H0.
  first_order.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset11Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
End Impl.

Module ImplCorrect : Pset11Sig.S := Impl.

(* Authors:
   Adam Chlipala,
   Peng Wang,
   Samuel Gruetter *)
