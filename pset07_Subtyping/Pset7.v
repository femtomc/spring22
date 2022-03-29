(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 7 *)

Require Import Frap.Frap.
Require Import Pset7Sig.

(* The following line forces you to use bullets or braces.  Remove it if you get
   errors like "Expected a single focused goal but 2 goals are focused." and you
   don't want to structure your proofs. *)
Set Implicit Arguments.

Module Impl.
(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type.  Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies.  Instead, here we
 * will prove soundness of *structural* subtyping, whose rules we'll get to
 * shortly.  The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)

| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.

(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.

(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.

Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupleNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Local Hint Constructors subtype : core.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.

(* Expression typing relation stating something _has_ a _ty_pe, not that 
 * the predicate is hasty or in a hurry.*)
Inductive hasty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    hasty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2 ->
    hasty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2) ->
    hasty G e2 t1 ->
    hasty G (App e1 e2) t2
| HtTupleNil : forall G,
    hasty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    hasty G e1 t1 ->
    hasty G e2 t2 ->
    hasty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    hasty G e t' ->
    proj_t t' n t ->
    hasty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type.  We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    hasty G e t' ->
    t' $<: t ->
    hasty G e t
.

(* Before we get started proving properties of our type system, please read
 * Pset7Sig.v and consider the questions below. This task is
 * ungraded, but we are assigning it in hopes it helps you complete the
 * following parts.

 What does it mean for the subtyping order of the arguments in `StFun` to be 
 reversed?


 If t1 $<: t2, what is known about some t3 that is a supertype of t2? And 
 likewise if it's a subtype of t1?


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 hasty G (Abs x e1) t
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `hasty`, and what 
 information do you have about `t`?

 To contrast, how many goals do you expect with the `hasty` definition of
 this pset? Why is this the case? 

 Can you formulate a lemma that consolidates the information present in these 
 branches into one conclusion? (Imagine inverting now is equivalent to an
 "or" generating branches for each constructor; can you rephrase a lemma that
 leads to a conclusion with an "and" instead?)


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 hasty G e (Fun t1 t2)
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `hasty`, and what 
 information do you have about `e`? 

 To contrast, how many goals do you expect with the `hasty` definition 
 of this pset? Why is this the case? 

 Can you formulate a lemma to recover information similar to what inverting
 gave you in FRAP's `hasty` definition?

 *)

Local Hint Constructors value plug step0 step hasty : core.

(* Prove these two basic algebraic properties of subtyping. *)

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  induct t1; simplify; eauto.
Qed.

Local Hint Resolve subtype_refl : core.

Definition P t1 t2 := forall t3, t2 $<: t3 -> t1 $<: t3.

Lemma subtype_trans_aux : forall t1 t2, t1 $<: t2 -> P t1 t2.
Proof.
  induct 1; unfold P; intros; eauto.
  unfold P in IHsubtype1.
  unfold P in IHsubtype2.
  invert H1.
Admitted.

Local Hint Resolve subtype_trans_aux : core.

(* HINT 1 (see Pset7Sig.v) *) 
Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  intros.
  eapply subtype_trans_aux.
  apply H.
Admitted.

Local Hint Resolve subtype_trans : core.

(* BEGIN handy tactic that we suggest for these proofs *)
Ltac tac0 :=
  match goal with
  | [ H : ex _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
  | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
  | [ H : step _ _ |- _ ] => invert H
  | [ H : step0 _ _ |- _ ] => invert1 H
  | [ H : hasty _ _ _ |- _ ] => invert1 H
  | [ H : proj_t _ _ _ |- _ ] => invert1 H
  | [ H : plug _ _ _ |- _ ] => invert1 H
  | [ H : subtype _ _ |- _ ] => invert1 H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end;
  subst.

Ltac tac := simplify;
            subst;
            propositional;
            repeat (tac0; simplify);
            try equality.
(* END handy tactic *)

(* The real prize: prove soundness of this type system.
 * We suggest starting from a copy of the type-safety proof from the book's
 * EvaluationContexts.v.
 * The soundness argument for simply typed lambda calculus is genuinely difficult
 * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
 * task of this pset is to *extend* it to cover subtyping. This will involve
 * changing some proofs and making appropriate additional helper lemmas (there
 * are more hints in Pset7Sig.v).
 * Trying to write this proof from scratch is *not* recommended for this pset.
 * This is in contrast to the *previous* psets, which we tried to design so that
 * they could be solved from scratch with a good understanding of the lecture
 * material. *)

Lemma value_implies_Abs G e t1 t2:
  hasty G e (Fun t1 t2)
  -> value e
  -> exists x e', e = Abs x e'.
Proof.
  induct 1; tac; auto.
  invert H0.
  econstructor.
  econstructor.
  equality.
  invert H.
  invert H0.
  destruct H1.
Admitted.

Local Hint Resolve value_implies_Abs : core.

Lemma value_implies_TupleCons G e t1 t2:
  hasty G e (TupleTypeCons t1 t2) /\ value e
  -> exists e1 e2, value e1 /\ value e2 /\ e = TupleCons e1 e2.
Proof.
  induct 1; tac; eauto.
  econstructor.
  econstructor.
Admitted.

Local Hint Resolve value_implies_TupleCons : core.

Lemma progress : forall e t,
    hasty $0 e t
    -> value e
      \/ (exists e' : exp, step e e').
Proof.
  induct 1; tac; eauto.
  eapply value_implies_Abs in H.
  tac.
  left.
  admit.
  equality.
  right.
  eapply StepRule in H5.
  eauto.
  eauto.
  eauto.
  right.
  eapply StepRule in H5.
  eauto.
  eauto.
  eauto.
  right.
  eapply StepRule in H7.
  eauto.
  eauto.
  eauto.
  eapply StepRule in H5.
  eauto.
  eauto.
  eauto.
  eapply StepRule in H5.
  eauto.
  eauto.
  eauto.
  eapply StepRule in H7.
  eauto.
  eauto.
  eauto.
  admit.
  eapply StepRule in H4.
  eauto.
  eauto.
  eauto.
Admitted.

Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                -> G' $+ (x, t) $? x' = Some t').
Proof.
  simplify.
  cases (x ==v x'); simplify; eauto.
Qed.

Local Hint Resolve weakening_override : core.

Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
            -> hasty G' e t.
Proof.
  induct 1; eauto.
Qed.

Local Hint Resolve weakening : core.

(* Replacing a typing context with an equal one has no effect (useful to guide
 * proof search as a hint). *)
Lemma hasty_change : forall G e t,
    hasty G e t
    -> forall G', G' = G
    -> hasty G' e t.
Proof.
  tac.
Qed.

Lemma hasty_TupleCons G e e' t:
   hasty G (TupleCons e e') t ->
   exists t1 t2, hasty G e t1 /\ hasty G e' t2 /\ TupleTypeCons t1 t2 $<: t.
Proof.
  induct 1; tac; eauto.
  econstructor.
  econstructor.
  eauto.
Qed.

Local Hint Resolve hasty_TupleCons : core.

Lemma hasty_Abs G x e t:
  hasty G (Abs x e) t ->
  exists t1 t2, hasty (G $+ (x, t1)) e t2 /\
             hasty G (Abs x e) (Fun t1 t2) /\
             Fun t1 t2 $<: t.
Proof.
  induct 1; tac; eauto.
  econstructor.
  econstructor.
  eauto.
  econstructor.
  econstructor.
  tac.
  eauto.
  eauto.
  eauto.
Qed.

Local Hint Resolve hasty_Abs : core.

Lemma hasty_App G e1 e2 t:
  hasty G (App e1 e2) t ->
  exists t1 t2, hasty G e1 (Fun t1 t2) /\
             hasty G e2 t1 /\
             t2 $<: t.
Proof.
  induct 1; tac; eauto.
  econstructor.
  econstructor.
  eauto.
Qed.

Local Hint Resolve hasty_App : core.

Lemma hasty_Proj G e n t:
  hasty G (Proj e n) t ->
  exists t' t'', hasty G e t' /\
              proj_t t' n t'' /\
              t'' $<: t.
Proof.
  induct 1; tac; eauto.
  econstructor.
  econstructor.
  eauto.
Qed.

Local Hint Resolve hasty_Proj : core.

Lemma substitution : forall G x x1 t' e t e',
    hasty (G $+ (x, t')) e x1 /\ x1 $<: t
    -> hasty $0 e' t'
    -> hasty G (subst e' x e) t.
Proof.
  invert 1; tac; eauto.
  invert H0; tac; eauto.
Admitted.

Local Hint Resolve substitution : core.

Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  induct 1; tac; eauto.
  eapply hasty_App in H0.
  tac.
  eapply hasty_Abs in H1.
  tac.
  eapply substitution.
  split.
  apply H2.
  eauto.
  eauto.
  eapply hasty_Proj in H1.
  tac.
  eapply hasty_TupleCons in H2.
  tac.
  eauto.
  eapply hasty_Proj in H1.
  tac.
  eapply hasty_TupleCons in H2.
  tac.
  eauto.
Qed.

Local Hint Resolve preservation0 : core.

Lemma preservation' : forall C e1 e1',
    plug C e1 e1'
    -> forall e2 e2' t, plug C e2 e2'
                  -> step0 e1 e2
                  -> hasty $0 e1' t
                  -> hasty $0 e2' t.
Proof.
  induct 1; tac; eauto.
  eapply hasty_App in H2.
  tac.
  eauto.
  eapply hasty_App in H3.
  tac.
  eauto.
  eapply hasty_TupleCons in H2.
  tac.
  eauto.
  eapply hasty_TupleCons in H3.
  tac.
  eauto.
  eapply hasty_Proj in H2.
  tac.
  eauto.
Qed.

Local Hint Resolve preservation' : core.

Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
           -> hasty $0 e2 t.
Proof.
  invert 1; tac; eauto.
Qed.

Local Hint Resolve progress preservation : core.

(* HINT 2-3 (see Pset7Sig.v) *) 
Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                (fun e' => value e'
                                        \/ exists e'', step e' e'').
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t); eauto.
  apply invariant_induction; simplify; eauto; try equality.
Qed.

End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset7Sig.S := Impl.

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Samuel Gruetter
 * Amanda Liu
 *)
