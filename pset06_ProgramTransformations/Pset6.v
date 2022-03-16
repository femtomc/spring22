(*|
=============================================================
 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 6
=============================================================
|*)

(* IMPORTANT: please be sure to update the FRAP library version you are using for
 * this pset, as we made a relevant improvement recently!
 * 'git submodule update; make -C frap lib' at the root of this repo should do
 * it. *)

Require Import Pset6Sig.

(*|
Modern compilers achieve excellent performance by leveraging a wide variety of
program transformations.  For example, GCC (the GNU C compiler) version 10.2
produces the *exact same* assembly code for the following two programs (if you
want to see for yourself, try it on https://godbolt.org!):

1. Recursive version with accumulator, naive division and modulo, no function
   inlining, multiple returns, redundant ``+ 1``, not tail-recursive::

      static unsigned int affine(unsigned int n,
                                 unsigned int slope,
                                 unsigned int offset) {
          return n * slope + offset;
      }

      unsigned int collatz1(unsigned int start) {
          if (start == 1)
            return 0;
          else if (start % 2 == 0)
            return collatz1(start / 2) + 1;
          else
            return collatz1(affine(start, 3, 1)) + 1;
      }

2. Single loop, inlined function, bitwise arithmetic::

      unsigned int collatz2(unsigned int start) {
          unsigned int flight = 0;
          while (start != 1) {
              flight++;
              if ((start & 1) == 0) {
                  start = start >> 1;
              } else {
                  start = start * 2 + start + 1;
              }
          }
          return flight;
      }

The way GCC achieves this is by applying a sequence of transformation passes on
the code: you can see the output of each intermediate pass (all ~320 of them)
using ``gcc -O3 -fdump-tree-all -fdump-rtl-all -c collatz1.c``.  For instance,
the ``ssa`` pass puts the code into a form similar to the three-address code
that we saw in class, the ``tailr1`` passes convert the recursive function to a
loop, etc.

Students interested in an introduction to the magic of modern compiler
optimizations might enjoy Matt Godbolt's 2017 talk at CPPCon, *What Has My
Compiler Done for Me Lately? Unbolting the Compiler's Lid*
(https://www.youtube.com/watch?v=bSkpMdDe4g4).

In this lab, we'll see how formal methods can help us reason about the
correctness of these optimization passes, focusing on a few commonly used
optimizations.

*A few notes of caution*:

- Many of the proofs in this lab can be a bit long to complete fully manually:
  we encourage you to try your hand at simple automation.  However, make sure
  that your whole file compiles in a reasonable amount of time (at most a minute
  or two).

- When decomposed into the right sequence of lemmas, most of the theorems in
  this pset have relatively short proofs.  The best way to find these lemmas is
  to approach each problem cautiously, trying to work an understanding of the
  proof before diving into long series of `invert`, `econstructor`, etc.  In
  general, it's also a good idea to admit lemmas until you are sure that they
  allow you to prove the complete theorem, then go back and prove the lemmas —
  but do take the time to convince yourself that your lemmas make sense, so that
  you don't waste time using incorrect lemmas.

- We have included plenty of hints below in the HINTS section of the 
  signature file.
|*)

Module Impl.

(*|
Language definition
===================

We'll start with a variant of FRAP's usual imperative language, with a few
twists: first, we'll generalize the `Plus` constructor, allowing a number of
binary operators.  Second, we'll add function calls (for simplicity, all
functions take two arguments, and they assign their results to variables).
|*)

Inductive BinopName :=
| LogAnd
| Eq
| ShiftLeft
| ShiftRight
| Times
| Divide
| Plus
| Minus
| Modulo.

Inductive expr: Set :=
| Const (n: nat)
| Var (x: var)
| Binop (b: BinopName) (e1 e2: expr).

Inductive cmd :=
| Skip
| Assign (x: var) (e: expr)
| AssignCall (x: var) (f: string) (e1 e2: expr)
| Sequence (c1 c2: cmd)
| If (e: expr) (thn els: cmd)
| While (e: expr) (body: cmd).

(*|
Defining a few notations will make things more readable (you don't need to
understand how these notations work):
|*)

Declare Scope expr.
Delimit Scope expr with expr.

Coercion Const : nat >-> expr.
Coercion Var : var >-> expr.

Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.

Notation "x <- e" :=
  (Assign x e%expr)
    (at level 75).
Notation "x <- 'call1' f e1" :=
  (AssignCall x f e1%expr (Const 0))
    (at level 75, f at level 0, e1 at level 0).
Notation "x <- 'call2' f e1 e2" :=
  (AssignCall x f e1%expr e2%expr)
    (at level 75, f at level 0, e1 at level 0, e2 at level 0).
Infix ";;" :=
  Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%expr then_ else_)
    (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%expr body)
    (at level 75).

(*|
Here are a few example programs:
|*)

Example Times3Plus1Body :=
  ("n" <- "n" * 3 + 1).

Example FactBody :=
  ("f" <- 1;;
   while "n" loop
         "f" <- "f" * "n";;
   "n" <- "n" - 1
                 done).

Example FactRecBody :=
  (when "n" == 1 then
     "f" <- 1
   else
     "f" <- call1 "fact_r" ("n" - 1);;
     "f" <- "f" * "n"
                   done).

Example FactTailRecBody :=
  (when "n" == 1 then
     "f" <- "acc"
   else
     "f" <- call2 "fact_tr" ("n" - 1) ("acc" * "n")
                 done).

Example CollatzBody :=
  (when ("start" == 1) then
     Skip
   else when ("start" mod 2 == 0) then
     "start" <- "start" / 2
   else
     (* `call1 f arg` is short for `call2 f arg 0` *)
     "start" <- call1 "times3plus1" ("start" + 0)
                     done;;
     "flight" <- call2 "collatz" "start" ("flight" + 1)
                      done).

(*|
The coercions defined in the previous section make programs easier to write by
allowing to write `x` for `Var x` and `n` for `Const n`, but they can be
confusing when reading programs or proving properties, so the following line
turns them off:
|*)

Set Printing Coercions.

(*|
Semantics
=========

Our first step is to give a meaning to these new constructs.  Let's start with
an interpreter for binary operators:
|*)

Fixpoint interp_binop (b: BinopName) (n1 n2: nat) {struct b} :=
  match b with
  | LogAnd => Nat.land n1 n2
  | Eq => if (n1 ==n n2) then 1 else 0
  | Plus => n1 + n2
  | Minus => n1 - n2
  | Times => n1 * n2
  | Divide => n1 / n2
  | ShiftLeft => Nat.shiftl n1 n2
  | ShiftRight => Nat.shiftr n1 n2
  | Modulo => Nat.modulo n1 n2
  end.

(*|
For expressions, we'll use an interpreter to implement the following rules::

              n1 = n2
           ------------
            ⟦n2⟧ᵥ = n1

    (x ↦ a) ∈ v         x ∉ v
   --------------     ----------
      ⟦x⟧ᵥ = a         ⟦x⟧ᵥ = 0

            ⟦e1⟧ᵥ = a1
            ⟦e2⟧ᵥ = a2
      a = interp_binop b a1 a2
   -----------------------------
       ⟦Binop b e1 e2⟧ᵥ = a

..
|*)

Definition valuation := fmap var nat.

Fixpoint interp_arith (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

(*|
For commands, we'll use an inductive `Prop` to define big-step semantics.
This is an opportunity to show that compiler proofs can work with a variety
of semantics styles, since we focused on small-step semantics in lecture.
The rules for `Assign`, `While`, `If`, and `Skip` are the same as usual; for
example::

                 ⟦e⟧ᵥ = a
   ----------------------------------- EvalAssign
    (v, Assign x e) ↓ᵩ (v $+ (x, a))

    (c1, v) ↓ᵩ v'   (c2, v') ↓ᵩ v''
   ----------------------------------- EvalSequence
       (v, Sequence c1 c2) ↓ᵩ v''

Notice the subscript φ: this indicates that we have an environment of functions.
This environment of functions gives the body of each function, the names of its
arguments, and the name of its return value.  For example, to say that the
function "collatz" has body `CollatzBody`, takes arguments "start" and "flight",
and writes its result to "out", we would write::

   phi = $0 $+ ("collatz", (("start", "flight"), "out", CollatzBody))

and to say that function "factorial" has body `FactBody`, takes argument "n",
and writes its result to "f", we might write the following (every function takes
two parameters, so we use "" as the name of the second argument of "factorial").

   phi = $0 $+ ("factorial", (("n", ""), "f", FactBody))

We need an additional rule `EvalAssignCall` for function calls::

            (f ↦ ((x1, x2), y, body)) ∈ φ
               ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
       (body, ($0 $+ (x1, a1) $+ (x2, a2))) ↓ᵩ v'
                     (y ↦ a) ∈ v'
    ------------------------------------------------
      (AssignCall x f e1 e2, v) ↓ᵩ (v $+ (x, a))

A few notes:

- This rule passes arguments by value: that is, the function's arguments are
  evaluated in the current valuation ``v``: ``⟦e⟧ᵥ = a``.

- The function environment ``phi`` (represented as φ above) maps function names
  (strings) to function signatures and function bodies:
  ``(f ↦ ((x1, x2), y, body)) ∈ φ``.

- Functions return their output in variables indicated by their signatures:
  ``(y ↦ a) ∈ v1``.

- Functions do not have access to the contexts of their callers: ``body`` runs
  in a clean environment.

Here is how it looks in Coq:
|*)

Definition environment := fmap string ((var * var) * var * cmd).

Inductive eval (phi: environment): valuation -> cmd -> valuation -> Prop :=
| EvalSkip: forall v,
    eval phi v Skip v
| EvalAssign: forall v x e a,
    interp_arith e v = a ->
    eval phi v (Assign x e) (v $+ (x, a))
| EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a v v',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 v = a1 ->
    interp_arith e2 v = a2 ->
    eval phi ($0 $+ (x1, a1) $+ (x2, a2)) body v' ->
    v' $? y = Some a ->
    eval phi v (AssignCall x f e1 e2) (v $+ (x, a))
| EvalSequence: forall v c1 v1 c2 v2,
    eval phi v c1 v1 ->
    eval phi v1 c2 v2 ->
    eval phi v (Sequence c1 c2) v2
| EvalIfTrue: forall v e thn els v' c,
    interp_arith e v = c ->
    c <> 0 ->
    eval phi v thn v' ->
    eval phi v (If e thn els) v'
| EvalIfFalse: forall v e thn els v',
    interp_arith e v = 0 ->
    eval phi v els v' ->
    eval phi v (If e thn els) v'
| EvalWhileTrue: forall v e body v' v'' c,
    interp_arith e v = c ->
    c <> 0 ->
    eval phi v body v' ->
    eval phi v' (While e body) v'' ->
    eval phi v (While e body) v''
| EvalWhileFalse: forall v e body,
    interp_arith e v = 0 ->
    eval phi v (While e body) v.

Ltac eval_intro :=
  let eval_intro_solve :=
      simplify;
      lazymatch goal with
      | [  |- eval _ _ _ _ ] => idtac
      | _ => equality
      end in
  lazymatch goal with
  | [  |- eval _ _ Skip _ ] =>
    apply EvalSkip
  | [  |- eval _ _ (Assign _ _) _ ] =>
    eapply EvalAssign
  | [  |- eval _ _ (AssignCall _ _ _ _) _ ] =>
    eapply EvalAssignCall
  | [  |- eval _ _ (Sequence _ _) _ ] =>
    eapply EvalSequence
  | [  |- eval _ _ (While _ _) _ ] =>
    (eapply EvalWhileTrue + eapply EvalWhileFalse); eval_intro_solve
  | [  |- eval _ _ (If _ _ _) _ ] =>
    (eapply EvalIfTrue + eapply EvalIfFalse); eval_intro_solve
  | [  |- eval _ _ ?cmd _ ] =>
    unfold cmd at -1 || unfold cmd
  | [  |- interp_arith _ _ = _ _ ] => econstructor
  | _ => progress simplify || equality
  end.

Lemma WhileTrue_inv : forall phi v e body v'' c,
    interp_arith e v = c ->
    c <> 0 ->
    eval phi v (While e body) v'' ->
    exists v',
      eval phi v body v' /\
      eval phi v' (While e body) v''.
Proof. simplify; invert H1; eauto || equality. Qed.

Lemma WhileFalse_inv : forall phi v e body v',
    interp_arith e v = 0 ->
    eval phi v (While e body) v' ->
    v = v'.
Proof. simplify; invert H0; eauto || equality. Qed.

Ltac eval_elim :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => invert H
  | [ H: interp_arith _ _ = _ _ |- _ ] => invert H
  | [ H: eval _ _ Skip _ |- _ ] => invert H
  | [ H: eval _ _ (Assign _ _) _ |- _ ] => invert H
  | [ H: eval _ _ (AssignCall _ _ _ _) _ |- _ ] => invert H
  | [ H: eval _ _ (Sequence _ _) _ |- _ ] => invert H
  | [ H: eval _ _ (If _ _ _) _ |- _ ] => invert H
  | [ H: eval _ _ (While _ _) _ |- _ ] =>
    eapply WhileTrue_inv in H;
    [ destruct H as (? & ? & ?) |
      solve [repeat (econstructor || simplify)] |
      equality ]
  | [ H: eval _ _ (While _ _) _ |- _ ] =>
    apply WhileFalse_inv in H;
    [ subst |
      solve [repeat (econstructor || simplify)] ]
  | [ H: context[if ?c then _ else _] |- _ ] => cases c
  | _ => simplify
  end.

(*|
As a sanity check, we can prove that the semantics is deterministic:
|*)

Lemma eval_deterministic_1 : forall phi c v0 v1,
    eval phi v0 c v1
    -> forall v2, eval phi v0 c v2
            -> v1 = v2.
Proof.
  induct 1.
  eval_elim.
  eval_elim.
  equality.
  eval_elim.
  eval_elim.
  equality.
  eval_elim.
  eval_elim.
  rewrite H9 in H.
  invert H.
  eapply IHeval in H14.
  equality.
  eval_elim.
  eval_elim.
  eapply IHeval1 in H5.
  rewrite <- H5 in H7.
  eapply IHeval2 in H7.
  equality.
  eval_elim.
  eval_elim.
  eapply IHeval in H10.
  equality.
  equality.
  eval_elim.
  eval_elim.
  equality.
  eapply IHeval in H8.
  equality.
  eval_elim.
  eval_elim.
  eapply IHeval1 in H3.
  rewrite <- H3 in H4.
  eapply IHeval2 in H4.
  equality.
  eval_elim.
  invert H0.
  equality.
  equality.
Qed.

Lemma eval_deterministic : forall phi c v0 v1 v2,
    eval phi v0 c v1
    -> eval phi v0 c v2
    -> v1 = v2.
Proof.
  intros.
  eapply eval_deterministic_1.
  apply H.
  assumption.
Qed.

(*|
Now let's check that our semantics compute the right values.  The `eval_intro`
tactic below may be useful for the following proofs.  You do not need to
understand its implementation; what matters is that it attempts to construct a
proof of `eval`, and it chooses between `EvalWhileTrue` and `EvalWhileFalse` and
between `EvalIfTrue` and `EvalIfFalse` by attempting to satisfy all the premises
of each of them.  It stops if it cannot conclusively decide which case applies.
|*)

(*|
To call functions, we need to specify their signatures:
|*)

Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
Notation Fact_signature := (("n", ""), "f", FactBody).
Notation FactRec_signature := (("n", ""), "f", FactRecBody).
Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

(*|
And to make goals more readable, we'll define a shorthand
`eval_returns phi v cmd outVar result`, which means “running `cmd` in
environment `phi` with valuation `v` returns `result` in `outVar`”:
|*)

Definition eval_returns phi v cmd outVar result :=
  exists v', eval phi v cmd v' /\ v' $? outVar = Some result.

(*|
Here are a few examples of execution:
|*)

Example TwoPlusTwoIsFour :
  eval_returns $0 $0 ("out" <- 2 + 2) "out" 4.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Example EvalVars :
  eval_returns
    $0 $0
    ("x" <- 1 + 1;;
     "x" <- "x" + "x" + "y")
    "x" 4.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Example EvalSimpleArith :
  eval_returns
    $0 $0
    ("out" <- ((((14 >> 1) + 8 / 4 / 2) * (7 - 2)) << 1) + 2 == 82)
    "out" 1.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Example EvalTimes3Plus1: forall n,
    eval_returns $0 ($0 $+ ("n", n)) Times3Plus1Body "n" (3 * n + 1).
Proof.
  eexists; propositional; repeat eval_intro.
  f_equal; linear_arithmetic.
Qed.

Lemma EvalFact6:
  eval_returns $0 ($0 $+ ("n", 3)) FactBody "f" 6.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Notation Fact_env :=
  ($0
    $+ ("fact", Fact_signature)
    $+ ("fact_r", FactRec_signature)
    $+ ("fact_tr", FactTailRec_signature)).

Lemma EvalFactRec6:
  eval_returns Fact_env ($0 $+ ("n", 3)) FactRecBody "f"6.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Lemma EvalFactTailRec6:
  eval_returns Fact_env ($0 $+ ("n", 3) $+ ("acc", 1)) FactTailRecBody "f" 6.
Proof.
  eexists; propositional; repeat eval_intro.
Qed.

Notation Collatz_env :=
  ($0
    $+ ("collatz", Collatz_signature)
    $+ ("times3plus1", TimesThreePlus1_signature)).

Lemma collatz_result:
  eval_returns Collatz_env ($0 $+ ("flight", 0) $+ ("start", 10)) CollatzBody "flight" 6.
Proof.
  (* This proof is larger, so `eval_intro` will take a bit longer (a few seconds): *)
  eexists; propositional; repeat eval_intro.
Qed.

(*|
Arithmetic optimizations
========================

Let's teach our compiler a few arithmetic optimizations.  All these
optimizations will be local, so we'll define them in terms of `interp_binop`:
every optimization will take a binary operator and two optimized expressions,
and it will return an optimized expression, without recursing.

Below, we will discuss four different flavors of arithmetic optimizations.  You
do not have to implement and prove all of them; instead, you just need to
implement the first one (constant folding) and one of the next three; you are
free to pick which one.

Here are the optimizations:

1. Folding constant subexpressions using properties of `+`, `*`, `/`
2. Precomputing constant subexpressions
3. Rewriting `*`, `/`, `mod` of powers of 2
4. Rewriting `*` as a sum of shifts

Options 4 is quite a bit more challenging than the others… but also quite
interesting!

To make sure that our optimizations are reasonable, we'll introduce a very
simple cost model; it gives us an estimate of the time it takes to run an
operation:
|*)

Fixpoint arith_cost (e: expr) : nat :=
  match e with
  | Binop b e1 e2 =>
    match b with
    | LogAnd | Eq | ShiftLeft | ShiftRight | Plus | Minus => 1
    | Times => 8
    | Divide | Modulo => 16
    end + arith_cost e1 + arith_cost e2
  | _ => 0
  end.

(*|
Constant folding
----------------

We'll start by applying the following rules:

- `n + 0 → n`
- `n * 0 → 0`
- `n / 1 → n`

This set is not complete in any sense; in addition to these three rewrites, we
encourage you to add extras and see how robust your proofs are to the changes.
Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_fold (b: BinopName) (e1 e2: expr) : expr :=
  match b with
  | Plus => match (e1, e2) with
           | (e, Const 0) => e
           | (Const 0, e) => e
           | (Const n, Const n0) => Const (n + n0)
           | (_, _) => Binop Plus e1 e2
           end
  | Times => match (e1, e2) with
            | (_, Const 0) => Const 0
            | (Const 0, _) => Const 0
            | (e1', e2') => Binop Times e1' e2'
            end
  | Divide => match (e1, e2) with
             | (e, Const 1) => e
             | (_, _) => Binop Divide e1 e2
             end
  | _ => Binop b e1 e2
  end.

Arguments opt_binop_fold !_ !_ !_ /. (* Coq magic *)

Example opt_binop_fold_test1 :
  opt_binop_fold Plus "x" 0 = "x".
Proof.
  eval_intro.
  equality.
Qed.

Lemma opt_binop_fold_sound : forall b e1 e2 v,
    interp_arith (opt_binop_fold b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
  eval_intro.
  induct b; simplify; try equality.
  cases e1.
  cases e2.
  cases n.
  cases n0; simplify; try equality.
  simplify.
  cases n.
  cases n0.
  simplify.
  equality.
  cases n0; simplify; try equality; try linear_arithmetic.
  cases n0; simplify; try equality; try linear_arithmetic.
  simplify.
  cases n.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  simplify.
  cases n; simplify; try equality.
  simplify.
  cases (v $? x); simplify; try equality.
  cases e2; simplify; try equality.
  cases n0; simplify; try equality; try linear_arithmetic.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases e2; simplify; try equality.
  cases n; simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  cases (v $? x); simplify; try equality.
  simplify.
  cases e2; simplify; try equality.
  cases n; simplify; try equality.
  linear_arithmetic.
  cases e2; simplify; try equality.
  cases n; simplify; try equality.
  cases n; simplify; try equality.
  replace (opt_binop_fold Divide e1 (Const 1)) with (e1).
  symmetry.
  eapply Nat.div_1_r.
  equality.
  cases e1.
  cases n; simplify; try equality; try linear_arithmetic.
  cases e2.
  cases n; simplify; try equality; try linear_arithmetic.
  simplify.
  cases (v $? x); simplify; try equality.
  simplify.
  equality.
  cases e2.
  simplify.
  cases n0; simplify; try equality; try linear_arithmetic.
  equality.
  simplify.
  equality.
  cases e2.
  cases n; simplify; try equality; try linear_arithmetic.
  equality.
  equality.
  cases e2.
  cases n; simplify; try equality; try linear_arithmetic.
  equality.
  equality.
Qed.

(*|
Precomputation
--------------

This is the first of three options.  If you implement this optimization, you do
not have to implement the next two.

We'll teach the compiler to simplify constant expressions: if an operator has
two constants as arguments, we'll precompute the value.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_precompute (b: BinopName) (e1 e2: expr) : expr :=
  match (e1, e2) with
  | (Const n1, Const n2) =>
    match b with
    | LogAnd => Const (Nat.land n1 n2)
    | Eq => if (n1 ==n n2) then Const 1 else Const 0
    | Plus => Const (n1 + n2)
    | Minus => Const (n1 - n2)
    | Times => Const (n1 * n2)
    | Divide => Const (n1 / n2)
    | ShiftLeft => Const (Nat.shiftl n1 n2)
    | ShiftRight => Const (Nat.shiftr n1 n2)
    | Modulo => Const (Nat.modulo n1 n2)
    end
  | (_, _) => Binop b e1 e2
  end.

Arguments opt_binop_precompute !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_precompute_sound : forall b e1 e2 v,
    interp_arith (opt_binop_precompute b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
  intros.
  cases e1.
  cases e2.
  cases b; simplify; try equality.
  cases (n ==n n0); try equality.
  equality.
  equality.
  equality.
  equality.
Qed.

(*|
Optimizing power-of-2 operations
--------------------------------

This is the second of three options.  If you implement this optimization, you do
not have to implement the other two.

Operations like multiplication, division, and modulo are typically relatively
slow, so we'd like to implement them more efficiently.  We'll use the following
trick:

- `n / 2^k` → `n >> k`
- `n * 2^k` → `n << k`
- `n mod 2^k` → `n & (2^k - 1)`

Here is a function that returns `Some k` if its input is equal to `2^k` and
`None` otherwise:
|*)

Definition log2 (n: nat) :=
  let l := Nat.log2 n in
  if 2 ^ l ==n n then Some l else None.

Lemma log2_sound : forall n l, log2 n = Some l -> n = 2^l.
Proof.
  unfold log2; simplify;
    repeat match goal with
           | [ H: context[if ?c then _ else _] |- _ ] => cases c
           | [ H: Some _ = Some _ |- _ ] => invert H
           end; equality.
Qed.

Lemma log2_complete : forall n, log2 n = None -> forall l, n <> 2^l.
Proof.
  unfold log2, not; simplify;
    replace l with (Nat.log2 n) in *
      by (subst; rewrite Nat.log2_pow2; eauto using Nat.le_0_l).
  match goal with
  | [ H: context[if ?c then _ else _] |- _ ] => cases c
  end; try equality.
Qed.

(*|
Use `log2` to define the transformation above.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_log2 (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_log2 !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_log2_sound : forall b e1 e2 v,
    interp_arith (opt_binop_log2 b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Rewriting multiplications
-------------------------

This is the last of three options.  If you implement this optimization, you do
not have to implement the previous two.

All numbers can be written as sums of powers of two, so we can replace all
mutiplications by sums of bitshifts:

- `n * ∑_k 2^k` → `∑_k n << k`

Here is a function that computes a number's decomposition by returning the
offsets of its nonzero bits:
|*)

Fixpoint log2sp (n: positive) (pos: nat) :=
  match n with
  | xI x => pos :: log2sp x (S pos)
  | xO x => log2sp x (S pos)
  | xH => [pos]
  end.

Definition log2s (n: nat) :=
  match N.of_nat n with
  | N0 => []
  | Npos p => log2sp p 0
  end.

(*|
Computing `log2s 13` returns [0;2;3], because 13 = 2^0 + 2^2 + 2^3.
|*)

Compute log2s 13.

Lemma log2sp_sound : forall p j,
    List.fold_right
      (fun k acc => 2 ^ k + acc)
      0 (log2sp p j) =
    (2 ^ j * N.to_nat (Npos p)).
Proof.
  induct p; simplify.
  3: rewrite ?Nat.add_0_r, ?Nat.mul_1_r; equality.
  all: rewrite IHp, Nat.pow_succ_r by linear_arithmetic.
  all: rewrite ?Pnat.Pos2Nat.inj_xO, ?Pnat.Pos2Nat.inj_xI.
  all: ring.
Qed.

Lemma log2s_sound : forall n,
    List.fold_right (fun k acc => 2^k + acc) 0 (log2s n) = n.
Proof.
  unfold log2s.
  simplify; rewrite <- (Nat2N.id n) at 2.
  destruct (N.of_nat n).
  - simplify; equality.
  - rewrite log2sp_sound, Nat.mul_1_l; equality.
Qed.

(*|
Use `log2s` to define a local optimization that implements the transformation above.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_bitwise (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_bitwise !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_bitwise_sound : forall b e1 e2 v,
    interp_arith (opt_binop_bitwise b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Putting it all together
-----------------------

We're ready to apply our optimizations over the whole AST of an expression:
write a recursive function which, at each `Binop` node of the expression,
applies all optimizations that you implemented and proved (at least
`opt_arith_constprop` and one of the next three).

Mind the order in which the optimizations are applied!
|*)

Fixpoint opt_arith (e: expr) : expr :=
  match e with
  | Const n => Const n
  | Var x => Var x
  | Binop b e1 e2 => match opt_binop_precompute b (opt_arith e1) (opt_arith e2) with
                    | Const n => Const n
                    | Var x => Var x
                    | Binop b' e1' e2' => opt_binop_fold b' e1' e2'
                    end
  end.

Arguments opt_arith !e /. (* Coq magic *)

Example opt_arith_fold_test1 :
  opt_arith (1 + "z" * ("y" * ("x" * (0 + 0 / 1))))%expr =
  (1)%expr.
Proof.
  unfold opt_arith.
  simplify.
  equality.
Qed.

Example opt_arith_precompute_test1:
  opt_arith (("x" + (3 - 3)) / (0 + 1) + ("y" + "y" * 0))%expr =
  ("x" + "y")%expr.
Proof.
  unfold opt_arith.
  simplify.
  equality.
Qed.

Example opt_arith_precompute_test2 :
  opt_arith ((("y" / ("x" * 0 + 7 / 1)) mod (12 - 5)) / (2 * 3))%expr =
  (("y" / 7) mod 7 / 6)%expr.
Proof.
  unfold opt_arith.
  simplify.
  equality.
Qed.

Example opt_arith_log2_test1 :
  opt_arith (("y" * 8) mod 8 / 4)%expr =
  (("y" << 3 & 7) >> 2)%expr.
Proof.
Admitted.

Example opt_arith_log2_test2 :
  opt_arith (("y" * 1 + (4 + 0)) mod 9 / 3)%expr =
  (("y" + 4) mod 9 / 3)%expr.
Proof.
Admitted.

Example opt_arith_bitwise_test1 :
  opt_arith ("y" * 13)%expr =
  ("y" + (("y" << 2) + ("y" << 3)))%expr.
Proof.
Admitted.

Example opt_arith_bitwise_test2 :
  opt_arith ("y" * (3 + 0))%expr =
  ("y" + ("y" << 1))%expr.
Proof.
Admitted.

Lemma opt_arith_sound : forall e v,
    interp_arith (opt_arith e) v =
    interp_arith e v.
Proof.
  induct e; simplify.
  equality.
  cases_any.
  equality.
  equality.
  cases_any.
  assert (interp_arith (opt_binop_precompute b (opt_arith e1) (opt_arith e2)) v = interp_arith (Const n) v).
  simplify.
  rewrite Heq.
  equality.
  simplify.
  rewrite opt_binop_precompute_sound in H.
  rewrite IHe1 in H.
  rewrite IHe2 in H.
  symmetry.
  equality.
  assert (interp_arith (opt_binop_precompute b (opt_arith e1) (opt_arith e2)) v = interp_arith (Var x) v).
  rewrite Heq.
  equality.
  rewrite opt_binop_precompute_sound in H.
  rewrite IHe1 in H.
  rewrite IHe2 in H.
  equality.
  rewrite opt_binop_fold_sound.
  assert (interp_arith (opt_binop_precompute b (opt_arith e1) (opt_arith e2)) v = interp_arith (Binop b0 e3 e4) v).
  rewrite Heq.
  equality.
  rewrite opt_binop_precompute_sound in H.
  rewrite IHe1 in H.
  rewrite IHe2 in H.
  rewrite H.
  equality.
Qed.

(*|
Optional: cost modeling
-----------------------

*This part is completely optional.*

Using the cost model introduced earlier, prove that your optimizer does reduce costs:
|*)

Lemma opt_arith_ok : forall e,
    arith_cost (opt_arith e) <= arith_cost e.
Proof.
Admitted.

(*|
That's it for expression optimizations!  Now, let's see command optimizations.

Command optimizations
=====================

In this part, we'll consider three optimizations.  You do not have to implement
all three; instead, you need to implement the first one and either one of the
last two:

- Simple dead-code elimination, by removing `Skip` nodes
- Constant propagation
- Loop unrolling

Loop unrolling is trickier than constant propagation.  And if you want a
challenge, constant propagation includes an *optional* generalization that makes
it *a lot* harder.

Oh, and if you're not excited about either of these optimizations, feel free to
pick a different one!  Just make sure that you run it by us so we can confirm
that it's reasonably difficult.  Want some ideas?  Check out
https://gcc.gnu.org/onlinedocs/gccint/Tree-SSA-passes.html.

Skip removal
------------

Our first optimization will be a very simple form of dead-code elimination, in
which we remove instances of `Skip`.  The following helper function might be useful: you can use it to check if a given command is a `Skip`: `if is_skip c then … else …` (of course, using a regular `match` works as well!).
|*)

Definition is_skip (c: cmd) : sumbool (c = Skip) (c <> Skip) :=
  ltac:(cases c; econstructor; equality).

Fixpoint opt_unskip (c: cmd) : cmd :=
  match c with
  | Skip => Skip
  | Assign v e => Assign v e
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Sequence c1 c2 => match (opt_unskip c1, opt_unskip c2) with
                     | (Skip, Skip) => Skip
                     | (c1', Skip) => c1'
                     | (Skip, c2') => c2'
                     | (c1', c2') => Sequence c1' c2'
                     end
  | If e1 c1 c2 => If e1 (opt_unskip c1) (opt_unskip c2)
  | While e c1 => While e (opt_unskip c1)
  end.

Example opt_unskip_test1 :
  opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
  Skip.
Proof.
  simplify.
  equality.
Qed.

Example opt_unskip_test2 :
  opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                                             while 0 loop Skip;; Skip done;; Skip) =
  (when 0 then Skip else Skip done;; while 0 loop Skip done).
Proof.
  simplify.
  equality.
Qed.

Lemma opt_unskip_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_unskip c) v'.
Proof.
  induct 1; simplify; try repeat eval_elim; try repeat eval_intro;
    try equality.
  apply H.
  rewrite H0.
  rewrite H1.
  apply H2.
  assumption.
  cases_any.
  cases_any.
  try repeat eval_elim.
  try repeat eval_intro.
  try repeat eval_elim.
  try repeat eval_intro.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  assumption.
  try repeat eval_elim.
  assumption.
  cases_any.
  try repeat eval_elim.
  try repeat eval_intro.
  try repeat eval_elim.
  try repeat eval_intro.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  assumption.
  try repeat eval_intro.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply IHeval2.
  cases_any.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H6.
  apply H13.
  assumption.
  apply H5.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  apply H11.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  apply H11.
  try repeat eval_intro.
  assumption.
  try repeat eval_intro.
  apply H5.
  apply H10.
  apply H11.
  try repeat eval_intro.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H10.
  apply H11.
  apply IHeval2.
  cases_any.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  apply H7.
  apply H5.
  apply H10.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H5.
  apply H8.
  apply H4.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  apply H6.
  try repeat eval_intro.
  assumption.
  try repeat eval_intro.
  apply H4.
  apply H6.
  try repeat eval_intro.
  assumption.
  try repeat eval_elim.
  try repeat eval_intro.
  apply H4.
  apply H6.
  apply IHeval2.
  cases_any; try repeat eval_elim;
    try repeat eval_intro; try assumption.
  apply H5.
  apply H10.
  assumption.
  apply H5.
  apply H10.
  assumption.
  apply H10.
  apply H4.
  assumption.
  apply H9.
  apply H4.
  assumption.
  apply H10.
  eval_intro.
  apply H8.
  apply H9.
  eval_intro.
  assumption.
  apply H10.
  eval_intro.
  assumption.
  apply H9.
  eval_intro.
  apply H7.
  apply H8.
  apply IHeval2.
  apply H7.
  apply IHeval2.
  cases_any; try repeat eval_elim;
    try repeat eval_intro; try assumption.
  apply H5.
  apply H10.
  assumption.
  apply IHeval1.
  apply H4.
  apply H6.
  apply IHeval1.
  eval_intro.
  assumption.
  apply IHeval1.
  eval_intro.
  assumption.
  apply IHeval1.
  apply IHeval2.
  apply IHeval1.
  assumption.
Qed.

(*|
Constant propagation
--------------------

This is the first of two options.  If you implement this optimization, you do
not have to implement the next one.

At the beginning of this pset we looked at constant folding, which uses
properties of arithmetic operations to simplify expressions.  Here, we'll look
at something slightly different: constant propagation.

Constant propagation is a form of static evaluation: it analyzes assignments to
detect cases in which the value being assigned is a constant; when it is, it
propagates it through the rest of the program.  This means that in a program
like `Assign x (Const n);; …`, we'll want to replace all instances of `x` with
`Const n` in `…`.  We'll keep a map `consts` tracking variables that have
constant values and use it to rewrite the program.

The first step is to define constant propagation for arithmetic expressions.
Since there are no assignments in expressions, this is just a matter of
substituting known values recursively:
|*)

Fixpoint opt_arith_constprop (c: expr) (consts: valuation) {struct c} : expr :=
  match c with
  | Const n => Const n
  | Var x => match consts $? x with
            | Some k => Const k
            | None => Var x
            end
  | Binop b e1 e2 => Binop b (opt_arith_constprop e1 consts) (opt_arith_constprop e2 consts)
  end.

(*|
What is the correctness criterion for constant propagation?  The environment of
statically known values, `consts`, needs to be consistent with the dynamic
valuation.  This is what `consts $<= v` means; `$<=` is a notation for the
`includes` function, for which the FRAP library provides many useful lemmas.
You can find these lemmas using `Search`; for example, use `Search "$<=" "$?"`
to find all theorems that mention the operators `$<=` and `$?`.
|*)

Lemma opt_arith_constprop_sound : forall e v consts,
    consts $<= v ->
    interp_arith (opt_arith_constprop e consts) v =
    interp_arith e v.
Proof.
  intros.
  induct e; simplify.
  equality.
  cases (consts $? x); simplify.
  cases (v $? x); simplify.
  apply includes_lookup with (m' := v) in Heq.
  equality.
  equality.
  apply includes_lookup with (m' := v) in Heq.
  equality.
  equality.
  cases (v $? x); simplify.
  equality.
  equality.
  eapply IHe1 in H as H1.
  eapply IHe2 in H as H2.
  rewrite H1.
  rewrite H2.
  equality.
Qed.

(*|
We can now define constant propagation on commands.  Propagating constants
through a program returns a new program, as well as a new set of known
constants.  Think carefully about the following cases:

- Assignments and function calls: these should update the `consts` map.  If the
  value being assigned is a constant, then it should be added to the map;
  otherwise, it should be removed from the map, using the `$-` operator.

- Conditionals: in a fully general implementation, we would want to reconcile
  the information learned along both branches of the `If`.  In this simple
  version, we will not do that: we'll simply reset the `consts` map to `$0`
  after constant-propagating through both branches.

- Loops: Constant-propagating through loops requires tracking the set of
  variables written in the loop.  Instead, we will reset the `consts` map when
  entering the body of a loop and reset it as well after exiting the loop.

In addition to propagating constants, you may be tempted to remove the
corresponding `Assign` node from the AST (replacing it with a `Skip`, for
example).  But in fact, the assignment *should be kept*: it's not safe to remove
the assignment entirely — can you see why?
|*)

Fixpoint _opt_constprop (c: cmd) (consts: valuation) : cmd * valuation :=
  match c with
  | Skip => (Skip, consts)
  | AssignCall x f e1 e2 => (AssignCall x f e1 e2, consts $- x)
  | Assign x e => match (opt_arith_constprop e consts) with
                 | Const k => (Assign x (Const k), consts $+ (x, k))
                 | e' => (Assign x e', consts $- x)
                 end
  | Sequence c1 c2 => let (c1', consts') := _opt_constprop c1 consts in
                     let (c2', consts'') := _opt_constprop c2 consts' in
                     (Sequence c1' c2', consts'')
  | If e c1 c2 => let e' := opt_arith_constprop e consts in
                 let (c1', _) := _opt_constprop c1 consts in
                 let (c2', _) := _opt_constprop c2 consts in
                 (If e' c1' c2', $0)
  | While e c1 => let e' := opt_arith_constprop e $0 in
                 let (c1', _) := _opt_constprop c1 $0 in
                 (While e' c1', $0)
  end.

Definition opt_constprop (c: cmd) : cmd := fst (_opt_constprop c $0).

Arguments opt_constprop !_ /. (* Coq magic *)

Example opt_constprop_test1 :
  opt_constprop FactBody = FactBody.
Proof.
  unfold opt_constprop; simplify.
  unfold FactBody.
  equality.
Qed.

Example opt_constprop_test2 :
  opt_constprop ("x" <- 7;; "y" <- "x";;
                 when "x" mod "w" then
                   "z" <- "x";; "t" <- "z";; while "t" loop "t" <- "t" - 1 done
                 else
                   "z" <- "u" + "x";; "t" <- "z"
                                             done;;
                   "r" <- "z") =
  ("x" <- 7;; "y" <- 7;;
   when 7 mod "w" then
     "z" <- 7;; "t" <- 7;; while "t" loop "t" <- "t" - 1 done
   else
     "z" <- "u" + 7;; "t" <- "z"
                             done;;
     "r" <- "z").
Proof.
  unfold opt_constprop.
  simplify.
  equality.
Qed.

Lemma arith_constprop_in_empty_is_expression : forall e,
    opt_arith_constprop e $0 = e.
Proof.
  induct e; simplify; try equality.
Qed.

Lemma arith_constprop_in_consts_implies_expr_1 : forall e e' consts v n,
    consts $<= v
    -> opt_arith_constprop e consts = e'
    -> interp_arith e  v = n
    -> interp_arith e' v = n.
Proof.
  intros.
  induct e; cases e'; simplify; try equality.
  cases (v $? x); simplify.
  cases (consts $? x); simplify.
  apply includes_lookup with (m' := v) in Heq0.
  equality.
  equality.
  equality.
  cases (consts $? x); simplify.
  apply includes_lookup with (m' := v) in Heq0.
  equality.
  equality.
  equality.
  cases_any.
  cases (v $? x); simplify.
  cases (consts $? x); simplify.
  apply includes_lookup with (m' := v) in Heq0.
  equality.
  equality.
  equality.
  cases (consts $? x); simplify.
  equality.
  equality.
  cases (v $? x); simplify.
  cases (consts $? x); simplify.
  equality.
  equality.
  equality.
  cases (v $? x); simplify.
  cases (consts $? x); simplify.
  equality.
  equality.
  cases (consts $? x); simplify.
  equality.
  equality.
  invert H0.
  rewrite opt_arith_constprop_sound.
  rewrite opt_arith_constprop_sound.
  equality.
  equality.
  equality.
Qed.

Lemma arith_constprop_in_consts_implies_expr_2 : forall e e' consts v n,
    consts $<= v
    -> opt_arith_constprop e consts = e'
    -> interp_arith e' v = n
    -> interp_arith e  v = n.
Proof.
  intros.
  induct e; simplify; try equality.
  cases e'; simplify.
  equality.
  cases (v $? x); simplify.
  equality.
  equality.
  equality.
  cases_any.
  cases (consts $? x); simplify.
  apply includes_lookup with (m' := v) in Heq0.
  rewrite <- H0 in H1.
  simplify.
  equality.
  equality.
  rewrite <- H0 in H1.
  simplify.
  cases (v $? x); simplify.
  equality.
  equality.
  cases (consts $? x).
  apply includes_lookup with (m' := v) in Heq0.
  equality.
  equality.
  rewrite <- H0 in H1.
  simplify.
  cases (v $? x).
  equality.
  equality.
  rewrite <- H0 in H1.
  simplify.
  Search (opt_arith_constprop).
  rewrite opt_arith_constprop_sound in H1.
  rewrite opt_arith_constprop_sound in H1.
  equality.
  equality.
  equality.
Qed.

Lemma arith_constprop_in_consts_implies_nonzero : forall e e' consts v,
    consts $<= v
    -> opt_arith_constprop e consts = e'
    -> interp_arith e  v <> 0
    -> interp_arith e' v <> 0.
Proof.
  intros.
  induct e; cases e'; simplify.
  equality.
  cases_any.
  equality.
  equality.
  equality.
  cases (consts $? x).
  cases (v $? x).
  apply includes_lookup with (m' := v) in Heq.
  equality.
  equality.
  equality.
  equality.
  cases_any.
  cases (consts $? x).
  cases (v $? x).
  equality.
  equality.
  cases (v $? x).
  equality.
  equality.
  cases (consts $? x).
  cases (v $? x).
  equality.
  equality.
  cases (v $? x).
  equality.
  equality.
  cases (consts $? x).
  equality.
  equality.
  equality.
  equality.
  invert H0.
  rewrite opt_arith_constprop_sound.
  rewrite opt_arith_constprop_sound.
  equality.
  equality.
  equality.
Qed.

Lemma arith_constprop_in_empty_equality_implies : forall e1 e2,
    opt_arith_constprop e1 $0 = e2 -> e1 = e2.
Proof.
  generalize arith_constprop_in_empty_is_expression.
  induct e1; simplify; try equality.
Qed.

Lemma arith_constprop_in_consts_implies_const : forall e consts v n,
    consts $<= v
    -> opt_arith_constprop e consts = Const n
    -> interp_arith e v = n.
Proof.
  intros.
  eapply arith_constprop_in_consts_implies_expr_2.
  apply H.
  apply H0.
  equality.
Qed.

Lemma includes_remove_add (consts v: valuation) x n:
  consts $<= v ->
  consts $- x $<= v $+ (x, n).
Proof.
  simplify; apply includes_intro; simplify.
  cases (x ==v k); subst; simplify; try equality.
  eauto using includes_lookup.
Qed.

Lemma _opt_constprop_sound phi : forall c consts v v',
    consts $<= v
    -> eval phi v c v'
    -> eval phi v (fst (_opt_constprop c consts)) v' /\ (snd (_opt_constprop c consts) $<= v').
Proof.
  intros.
  induct c; simplify;
    try eval_elim; try eval_intro;
    try cases_any; simplify; try eval_elim;
    try eval_intro; simplify.
  split; try eval_intro.
  split; try eval_intro.
  apply arith_constprop_in_consts_implies_const with (v := v) in Heq.
  simplify.
  equality.
  equality.
  apply arith_constprop_in_consts_implies_const with (v := v) in Heq.
  rewrite Heq.
  apply includes_add.
  equality.
  equality.
  split; try eval_intro.
  assert (interp_arith (opt_arith_constprop e consts) v = interp_arith (Var x0) v).
  rewrite Heq.
  equality.
  erewrite opt_arith_constprop_sound in H0.
  rewrite H0.
  equality.
  equality.
  apply includes_remove_add.
  equality.
  split; try eval_intro.
  assert (interp_arith (opt_arith_constprop e consts) v = interp_arith (Binop b e0_1 e0_2) v).
  rewrite Heq.
  equality.
  erewrite opt_arith_constprop_sound in H0.
  equality.
  equality.
  apply includes_remove_add.
  equality.
  split; try eval_intro.
  apply H5.
  equality.
  equality.
  apply H10.
  assumption.
  apply includes_remove_add.
  equality.

  split; try eval_intro; try cases_any; try eval_elim; try eval_intro.
  apply IHc1 with (consts := consts) in H4.
  destruct H4.
  rewrite Heq in H0.
  simplify.
  apply H0.
  apply H.
  apply IHc2 with (consts := v0) in H6.
  destruct H6.
  rewrite Heq0 in H0.
  simplify.
  equality.
  apply IHc1 with (consts := consts) in H4.
  destruct H4.
  rewrite Heq in H0.
  rewrite Heq in H1.
  equality.
  equality.
  apply IHc2 with (consts := v0) in H6.
  destruct H6.
  rewrite Heq0 in H1.
  simplify.
  equality.
  apply IHc1 with (consts := consts) in H4.
  destruct H4.
  rewrite Heq in H0.
  rewrite Heq in H1.
  equality.
  equality.

  split; try eval_intro; try cases_any; try eval_elim; try eval_intro.
  remember (opt_arith_constprop e consts).
  assert (interp_arith e0 v <> 0).
  eapply arith_constprop_in_consts_implies_nonzero.
  apply H.
  symmetry.
  apply Heqe0.
  equality.
  eval_intro.
  apply IHc1 with (consts := consts) in H8.
  destruct H8.
  rewrite Heq in H1.
  simplify.
  apply H1.
  equality.
  apply empty_includes.

  split; try eval_intro; try cases_any; try eval_elim; try eval_intro.
  remember (opt_arith_constprop e consts).
  assert (interp_arith e0 v = interp_arith (opt_arith_constprop e consts) v).
  rewrite <- Heqe0.
  equality.
  assert (interp_arith (opt_arith_constprop e consts) v = interp_arith e v).
  eapply opt_arith_constprop_sound.
  equality.
  rewrite H1 in H0.
  subst.
  eval_intro.
  apply IHc2 with (consts := consts) in H7.
  destruct H7.
  rewrite Heq0 in H2.
  simplify.
  equality.
  equality.
  apply empty_includes.

  split.
  invert H0.
  remember (opt_arith_constprop e consts).
  assert (interp_arith (opt_arith_constprop e $0) v = interp_arith e v).
  eapply opt_arith_constprop_sound.
  apply empty_includes.
  assert (interp_arith (opt_arith_constprop e $0) v <> 0).
  rewrite H0.
  equality.
  eval_elim.
  eval_intro.
  apply IHc with (consts := $0) in H6.
  destruct H6.
  rewrite Heq in H0.
  simplify.
  apply H0.
  apply empty_includes.

  remember (opt_arith_constprop e $0).
  eapply IHc with (consts := $0) in H6.
  destruct H6.
  admit.

  assert (interp_arith (opt_arith_constprop e $0) v' = interp_arith e v').
  eapply opt_arith_constprop_sound.
  apply empty_includes.
  eval_intro.
  apply empty_includes.
Admitted.

Lemma opt_constprop_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_constprop c) v'.
Proof.
  intros.
  unfold opt_constprop.
  eapply _opt_constprop_sound.
  apply empty_includes.
  assumption.
Qed.

(*|
Loop unrolling
--------------

This is the second of two options.  If you implement this optimization, you do
not have to implement the previous one.

Reasoning across loop iterations is trickier than reasoning about loop-free
code, so one common optimization in compilers is *loop unrolling*, a process
whereby a loop body is repeated multiple times.  For example, consider the
following snippet::

    for (i = 0; i < len; i++) {
       out[i] = in[i];
    }

an optimizing compiler might replace it with the following::

    for (i = 0; i + 4 <= len; i += 4) { // Unrolled loop
       out[i] = in[i];
       out[i + 1] = in[i + 1];
       out[i + 2] = in[i + 2];
       out[i + 3] = in[i + 3];
    }
    for (; i < len; i++) { // Fix-up
       out[i] = in[i];
    }

In this example, unrolling would enable the compiler to optimize the
assignments, for example by coalescing them into larger memory operations
(“vectorizing”)::

    for (i = 0; i + 4 <= len; i += 4) { // Unrolled loop
       out[i:i+4] = in[i:i+4];
    }
    for (; i < len; i++) { // Fix-up
       out[i] = in[i];
    }

Let's implement a simple form of this optimization.  Since we have `while` loops
instead of `for` loops we'll recognize a slightly different pattern::

   while (counter) loop
     …body…;;
     counter <- counter - 1
   done

And for simplicity, we'll unroll each loop twice, so we'll generate the
following code::

   when (counter mod 2) then
     …body…;;
     counter <- counter - 1
   done
   while (counter) loop
     …body…;;
     counter <- counter - 1
     …body…;;
     counter <- counter - 1
   done

First, let's write a function to make sure that a given program (`body`) does
not write to a variable.  We'll need this to make sure that the loop body
doesn't overwrite the loop variable.
|*)

(* HINT 3-4 (see Pset6Sig.v) *)
Fixpoint read_only (c: cmd) (x0: var) {struct c} : bool.
Admitted.

(*|
With this, we can define the loop-unrolling transformation, in three steps:

First, a function that checks whether a program looks exactly like the
unrollable template above; if it does, this function returns the loop variable
and the body of the loop; otherwise it returns `None`; it does not recurse:
|*)

Definition opt_unroll_match_loop (c: cmd) : option (var * cmd).
Admitted.
Arguments opt_unroll_match_loop : simpl never. (* Coq magic *)

(*|
We recommend that you define a lemma that tells you what must be true about `c`
if `opt_unroll_match_loop c = Some (x, body)` holds.
|*)


(*|
Second, we need a function to generate the unrolled pattern; you can use any
implementation you want for the fix-up phase as long as you're indeed
implementing unrolling (the fix-up phase is the phase that adjusts for the fact
that the loop variable may not be a multiple of 2 at the start of the loop).
This is just a transcription of the C code shown earlier: it takes a loop body
and the variable it iterates on, and it returns a program similar to the
unrolled loop shown above.
|*)

Definition opt_unroll_template_de (x: var) (body: cmd) : cmd.
Admitted.

(*|
Third, we can write the full optimization, which runs `opt_unroll_match_loop` at
all places in the AST and uses `opt_unroll_template_de` when it finds a relevant
place.  For simplicity, you do not have to unroll loops recursively within the
body of an unrolled loop.
|*)

Fixpoint opt_unroll (c: cmd) : cmd.
Admitted.

Example opt_unroll_test1 :
  opt_unroll CollatzBody = CollatzBody.
Proof.
Admitted.

Example opt_unroll_test2 :
  opt_unroll FactBody <> FactBody.
Proof.
Admitted.

(*|
For the proof of correctness, you'll want to prove a number of side lemmas (our
solution has 5!).  To help you get started, here are a few facts on modulo (you
can refer to them using `Mod2.…`, e.g. `Mod2.small`:
|*)

Module Mod2.
Lemma even_not_one n: n mod 2 = 0 -> n <> 1.
Proof. cases n; try cases n; simplify; linear_arithmetic. Qed.

Lemma small n: n mod 2 = 0 \/ n mod 2 = 1.
Proof. pose proof Nat.mod_upper_bound n 2; linear_arithmetic. Qed.

Lemma pm n: n <> 0 -> (n - 1) mod 2 = (n + 1) mod 2.
Proof.
  erewrite <- Nat.mod_add with (b := 1); simplify.
  f_equal. all: linear_arithmetic.
Qed.

Lemma even_pred_odd n: n <> 0 -> n mod 2 = 0 -> (n - 1) mod 2 = 1.
Proof.
  simplify; rewrite pm by assumption.
  rewrite Nat.add_mod by linear_arithmetic.
  replace (n mod 2); equality.
Qed.

Lemma odd_pred_even n: n mod 2 = 1 -> (n - 1) mod 2 = 0.
Proof.
  simplify; rewrite pm by (cases n; simplify; linear_arithmetic).
  rewrite Nat.add_mod by linear_arithmetic.
  replace (n mod 2); equality.
Qed.
End Mod2.

(*|
Good luck with the correctness proof!  Remember to check the hints in the signature file or come to office hours if you run into issues.  To get you started, here is a lemma that lets you use `read_only _ _ _` hypotheses:
|*)

Lemma eval_read_only: forall {phi v v' x c},
    eval phi v c v' ->
    read_only c x = true ->
    v' $? x = v $? x.
Proof.
Admitted.

Lemma opt_unroll_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_unroll c) v'.
Proof.
Admitted.

(*|
Going further
=============

The following are suggestions, if you are interested in exploring further.
Beware that proving correctness for the optimizations below can be quite
time-consuming!

Tail-call elimination
---------------------

Tail-call elimination transforms recursive functions into loops, which saves
stack space and time pushing and popping items on the stack.  You can read more
about tail-call elimination at https://en.wikipedia.org/wiki/Tail_call .

The first step is to check that all calls to a given function are tail calls:
|*)

Axiom may_tco: forall (is_tail: bool) (f: string) (c: cmd), bool.

(*|
Then, we can perform tail-call elimination, under the assumption that calls to
`f` are in fact tail calls:
|*)

Axiom opt_tco : forall (f: string) (x1 x2: var) (c: cmd), cmd.

(*|
The correctness lemma looks roughly like this:
|*)

Axiom opt_tco_sound : forall phi c f x1 x2,
    may_tco true f c = true ->
    forall v v',
      eval phi v c v' ->
      eval phi v (opt_tco f x1 x2 c) (v' $+ ("continue", 0)).

(*|
Function Inlining
-----------------

Inlining reveals optimization opportunities by allowing the compiler to
specialize a function's body to a given call site.

When inlining, the compiler needs to be particularly careful not to overwrite
the caller's variables, nor not to give the inlined function body access to the
caller's variables.
|*)

Axiom opt_inline : forall (phi: environment) (c: cmd), cmd.

(*|
Note that inlining a function will add the (renamed) locals of the function to
the current valuation, so the correctness theorem has to be a bit different:
|*)

Axiom opt_inline_sound : forall phi c v v',
    eval phi v c v' ->
    exists v'',
      eval phi v (opt_inline phi c) v'' /\
      (v' $<= v'').
End Impl.

Module ImplCorrect : Pset6Sig.S := Impl.

(* Authors:
   Clément Pit-Claudel *)
