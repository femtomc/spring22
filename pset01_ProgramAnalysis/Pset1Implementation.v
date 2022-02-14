(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 1 *)

(* Welcome to 6.822!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
    simplify; equality.
  Qed.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
    simplify.
    cases b.
    simplify; equality.
    simplify; equality.
  Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Definition And (x y : bool) : bool :=
    match (x, y) with
    | (true, true) => true
    | (_, _) => false
    end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
    simplify. equality.
  Qed.

  Theorem And_false_true : And false true = false.
  Proof.
    simplify. equality.
  Qed.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    induct x.
    simplify. equality.
    simplify. induct y. simplify. equality. equality.
  Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
    induct x.
    equality.
    equality.
  Qed.

  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
    match p with
    | Done => initState
    | AddThen n p' => run p' (initState + n)
    | MulThen n p' => run p' (initState * n)
    | DivThen n p' => run p' (initState / n)
    | VidThen n p' => run p' (n / initState)
    | SetToThen n p' => run p' n
    end.

  Theorem run_Example1 : run Done 0 = 0.
  Proof.
    equality.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
    equality.
  Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.
    equality.
  Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
    match p with
    | Done => 0
    | AddThen _ p' => 1 + numInstructions p'
    | MulThen _ p' => 1 + numInstructions p'
    | DivThen _ p' => 1 + numInstructions p'
    | VidThen _ p' => 1 + numInstructions p'
    | SetToThen _ p' => 1 + numInstructions p'
    end.

  Theorem numInstructions_Example :
       numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
    equality.
  Qed.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
    match p1 with
    | Done => p2
    | AddThen n p' => AddThen n (concatProg p' p2)
    | MulThen n p' => MulThen n (concatProg p' p2)
    | DivThen n p' => DivThen n (concatProg p' p2)
    | VidThen n p' => VidThen n (concatProg p' p2)
    | SetToThen n p' => SetToThen n (concatProg p' p2)
    end.

  Theorem concatProg_Example :
       concatProg (AddThen 1 Done) (MulThen 2 Done)
       = AddThen 1 (MulThen 2 Done).
  Proof.
    equality.
  Qed.

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                             = numInstructions p1 + numInstructions p2.
  Proof.
    simplify.
    induct p1.
    simplify. equality. simplify.
    equality. simplify. equality. simplify. equality. simplify. equality. simplify. equality.
  Qed.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
    run (concatProg p1 p2) initState =
    run p2 (run p1 initState).
  Proof.
    simplify. induct p1.
    simplify. equality. simplify. equality. simplify. equality. simplify. equality.
    simplify. equality. simplify. equality.
  Qed.

  (* Read this definition and understand how division by zero is handled. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n + state)
    | MulThen n p => runPortable p (n * state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. induct n.
         simplify. equality. simplify.
         replace (S (n + 1)) with (S (S n)).
         equality. linear_arithmetic.
  Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify.
         replace (n + 1) with (S n).
         equality. linear_arithmetic.
  Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof.
    induct p.
    simplify. equality.
    simplify.
    apply IHp.
    replace (s0 + n) with (n + s0).
    assumption.
    linear_arithmetic.
    simplify.
    replace (s0 * n) with (n * s0).
    eapply IHp.
    assumption.
    linear_arithmetic.
    simplify.
    cases n. simplify.
    equality. simplify.
    apply IHp.
    assumption.
    simplify.
    cases s0.
    simplify.
    equality.
    simplify.
    apply IHp.
    assumption.
    simplify.
    apply IHp.
    assumption.
  Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

  (* HINT 1 (see Pset1Signature.v) *)

  (* The idea here is to use a boolean nz as an overapproximation
of the runtime state. The nz says "this is 0" or "this is positive".*)
  Fixpoint validate' (p : Prog) (nz : bool) : bool :=
    match (p, nz) with
    | (Done, _) => true
    | (AddThen 0 p', f) => validate' p' f
    | (AddThen n p', f) => validate' p' true
    | (MulThen 0 p', f) => validate' p' false
    | (MulThen n p', f) => validate' p' f
    | (DivThen 0 p', f) => false
    | (DivThen 1 p', f) => validate' p' f
    | (DivThen n p', f) => validate' p' false
    | (VidThen n p', false) => false
    | (VidThen n p', true) => validate' p' false
    | (SetToThen 0 p', f) => validate' p' false
    | (SetToThen n p', f) => validate' p' true
    end.

  Definition validate (p : Prog) : bool := validate' p false.

  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate2 : validate goodProgram2 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate3 : validate goodProgram3 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate4 : validate goodProgram4 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate5 : validate goodProgram5 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate6 : validate goodProgram6 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validate7 : validate goodProgram7 = true.
  Proof.
    simplify.
    equality.
  Qed.

  Example validateb1 : validate badProgram1 = false.
  Proof.
    simplify.
    equality.
  Qed.

  Example validateb2 : validate badProgram2 = false.
  Proof.
    simplify.
    equality.
  Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)

  Definition badProgram3 := AddThen 1 (MulThen 0 (VidThen 10 Done)).
  Example validateb3 : validate badProgram3 = false.
  Proof.
    simplify.
    equality.
  Qed.

  (* HINTs 2-6 (see Pset1Signature.v)  *)

  (* Finally, before diving into the Coq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch:

    The key thing here is to use the auxiliary function validate' (which uses a boolean flag
    to represent if the state is 0 or positive). Conservative usage of validate' requires that validate
    is defined by (validate p := validate' p false) because (a priori) we don't know what the initial state
    will be.

    However, we can pose (validate'_sound) first as a lemma, and utilize assumptions about the state
    as part of pre-conditions in the lemma:

    (
      Lemma validate'_sound : forall p s, (validate' p false = true -> runPortable p s = (true, run p s)) /\
                                  (validate' p true = true /\ s <> 0 -> runPortable p s = (true, run p s)).
    )

    Here, the basic interpretation is that (forall p s), if (validate' p false = true) then we know (even conservatively!)
    that (runPortable p s = (true, run p s)). Now, in the second case, if we know (validate' p true = true) --
    e.g. the case where the flag indicates that the state at this stage of execution is non-zero,
    we cannot prove anything for all (s), we have to have the additional fact that s <> 0
    (an easier way to see: if we have (validate' p true = true) and (initState = 0), we can't say anything about (runPortable p s))

    The way that validate'_sound should go is by induction on p.
    (There's a useful lemma below (validate'_false_implies_true) which I use throughout -- this basically states
    that, if (validate p = true), it's true for all initial states)

    Throughout the structural induction proof, the inductive hypothesis tends to look the same:

    (
      IHp : forall s : nat,
          (validate' p false = true -> runPortable p s = (true, run p s))
      /\ (validate' p true = true /\ s <> 0 -> runPortable p s = (true, run p s))
    )

    This is because the inductive data type of programs "wraps" the instantiated (p : Prog, from context). So proving the inductive goal
    (e.g. AddThen n p) provides an inductive hypothesis like the above.

    All structural cases in the induction will likely also support usage of the (cases n) tactic. This is again due to how we defined our programs.
    (cases n) will split into (0) and (S _). In certain inductive cases, (0) will lead to contradictions -- which is great, because it allows
    us to immediately prove sub-goals. In (DivThen n p), (cases n) also supports the (1) case (which is a "no-op" under validate').

    The only time the (cases s) tactic (where s is the state) is required is in (VidThen n p). Again, (0) will lead to a contradiction, (1) is a "no-op".

    One general way to characterize proving each inductive case:
    the strategy of (simplify, cases n || cases s, rewrite with IHp, equality, linear_arithmetic) mostly works.

    When (validate'_sound) goes through, (validate'_sound) can be used to
    trivially prove (validate_sound) (by unfolding (validate)).

   **)

  Lemma validate'_false_implies_true : forall p, validate' p false = true -> validate' p true = true.
  Proof.
    induct p.
    simplify.
    equality.
    simplify.
    cases n.
    eapply IHp.
    assumption.
    assumption.
    simplify.
    cases n.
    assumption.
    apply IHp in H.
    assumption.
    simplify.
    cases n.
    equality.
    cases n.
    eapply IHp.
    assumption.
    assumption.
    simplify.
    equality.
    simplify.
    cases n.
    assumption.
    assumption.
  Qed.

  Lemma validate'_sound : forall p s, (validate' p false = true -> runPortable p s = (true, run p s)) /\
                                 (validate' p true = true /\ s <> 0 -> runPortable p s = (true, run p s)).
  Proof.
    induct p.
    - simplify. equality.
    - intros.
      split.
      simplify.
      cases n.
      eapply IHp in H.
      replace (0 + s) with (s + 0).
      apply H.
      replace (s + 0) with (0 + s).
      equality.
      linear_arithmetic.
      replace (S n + s) with (s + S n).
      eapply IHp.
      split.
      assumption.
      linear_arithmetic.
      linear_arithmetic.
      simplify.
      cases n.
      eapply IHp in H.
      replace (s + 0) with (s).
      assumption.
      linear_arithmetic.
      replace (s + S n) with (S n + s).
      eapply IHp.
      split.
      apply H.
      linear_arithmetic.
      linear_arithmetic.
    - simplify.
      split.
      cases n.
      replace (s * 0) with (0 * s).
      eapply IHp.
      linear_arithmetic.
      replace (s * S n) with (S n * s).
      eapply IHp.
      linear_arithmetic.
      cases n.
      intros.
      replace (0 * s) with (s * 0).
      destruct H.
      eapply IHp in H.
      apply H.
      linear_arithmetic.
      intros.
      destruct H.
      replace (s * S n) with (S n * s).
      eapply IHp.
      split.
      assumption.
      linear_arithmetic.
      linear_arithmetic.
    - split.
      simplify.
      cases n.
      simplify.
      equality.
      simplify.
      cases n.
      eapply IHp in H.
      apply H.
      eapply IHp in H.
      apply H.
      simplify.
      cases n.
      simplify.
      equality.
      simplify.
      cases n.
      eapply IHp.
      split.
      destruct H.
      assumption.
      destruct H.
      replace (s / 1) with (s).
      assumption.
      rewrite Nat.div_1_r.
      equality.
      destruct H.
      eapply IHp in H.
      apply H.
    - simplify.
      split.
      equality.
      cases s.
      simplify.
      destruct H.
      equality.
      simplify.
      destruct H.
      eapply IHp in H.
      apply H.
    - split.
      simplify.
      cases n.
      eapply IHp in H.
      apply H.
      remember (S n).
      eapply IHp.
      split.
      assumption.
      linear_arithmetic.
      simplify.
      cases n.
      destruct H.
      eapply IHp in H.
      apply H.
      eapply IHp.
      split.
      destruct H.
      assumption.
      linear_arithmetic.
  Qed.

  (* Now you're ready to write the proof in Coq: *)
  Lemma validate_sound : forall p, validate p = true ->
forall s, runPortable p s = (true, run p s).
  Proof.
    intros.
    unfold validate in H.
    eapply validate'_sound in H.
    apply H.
  Qed.

(* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
