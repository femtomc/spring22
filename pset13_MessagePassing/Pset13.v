(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 13 *)

(* Author:
 * Samuel Gruetter (gruetter@mit.edu)
 *)

Require Import Frap MessagesAndRefinement Pset13Sig.

Module Impl.
(* We suggest that you start by reading Chapter 21 in the FRAP book.
   For this pset, you will need to understand everything in that chapter up to and
   including Theorem 19.2 ("If p1 <| p2, then every trace generated by p1 is
   also generated by p2").
   Also study the code in MessagesAndRefinement.v, because this
   pset depends on that code. 

   As always, if you ever get stuck, you can help yourself to the hints at
   the bottom of Pset13Sig.v! *)

Arguments Nat.modulo: simpl never.

(* In this pset, we will define a small key-value store server.
   To simplify, it only accepts GET requests: *)
Inductive request :=
| GET (client_id key : nat).

Definition get_key (req : request) : nat :=
  match req with
  | GET _ key => key
  end.

Definition get_id (req : request) : nat :=
  match req with
  | GET client_id _ => client_id
  end.

(* There are two possible responses for a GET request: *)
Inductive response :=
| FOUND (client_id key value : nat)
| NOT_FOUND (client_id key : nat).

(* Given a key-value store (modeled as an fmap), a source channel, and an output channel,
   here's how we handle one request: *)
Definition request_handler (store : fmap nat nat) (source output : channel) : proc :=
  ??source(req: request);
  match req with
  | GET client_id key =>
    match store $? key with
    | Some v => !!output(FOUND client_id key v); Done
| None => !!output(NOT_FOUND client_id key); Done
end
end.

(* Key-value stores might become very large, so that they don't fit on one single
   server's disk. Therefore, we split the store into two shards:
   One for all even keys, and one for all odd keys.
   Here's a predicate asserting that a full_store is split correctly into an
   even_store and an odd_store: *)
Definition split_store (full_store even_store odd_store : fmap nat nat) : Prop :=
  (forall k, k mod 2 = 0  -> even_store $? k = full_store $? k) /\
  (forall k, k mod 2 = 0  -> odd_store  $? k = None) /\
  (forall k, k mod 2 <> 0 -> even_store $? k = None) /\
  (forall k, k mod 2 <> 0 -> odd_store  $? k = full_store $? k).

(* The goal of this pset is to define a distributed key-value-store system
   implementation that does not need to save the full store anywhere, and only
   needs full_store to specify its correctness. *)

(* We use two intermediate channels forward_even and forward_odd, and add a
   request_dispatcher to forward requests to these channels: *)
Definition request_dispatcher (input forward_even forward_odd : channel) : proc :=
  ??input(req: request);
  if get_key req mod 2 ==n 0 then
    !!forward_even(req); Done
  else
    !!forward_odd(req); Done.

(* Our balanced request handler creates two intermediate channels and then combines the
   request dispatcher with two request handlers, one for even keys and one for odd keys: *)
Definition balanced_handler (even_store odd_store : fmap nat nat) (input output : channel) : proc :=
  New[input; output](forward_even);
  New[input; output; forward_even](forward_odd);
  request_dispatcher input forward_even forward_odd
  || request_handler even_store forward_even output
  || request_handler odd_store forward_odd output.

(* Here's the correctness property that we want to hold for our balanced_handler:
   Each I/O trace generated by balanced_handler should also be a trace generated
   by one single request_handler which uses the full_store. *)
Definition correctness: Prop := forall full_store even_store odd_store input output,
    split_store full_store even_store odd_store ->
    input <> output ->
    forall trace,
      couldGenerate (balanced_handler even_store odd_store input output) trace ->
      couldGenerate (request_handler full_store input output) trace.

(* We suggest that you start by testing your understanding by answering the
   following questions.
   They are graded as follows: If you complete all the Coq proofs, you will
   get full score, no matter what you write in the answers to these questions.
   On the other hand, if you can't finish the Coq proofs, you can get up to
   40 points for answering these questions, plus points for partial Coq proofs.

Question 1) For each of the following processes, briefly describe what they do:

a)  !!ch(v); k

b)  ??ch(x: T); k

c)  pr1 || pr2

d)  Dup pr

e)  Done

f)  New[ch1; ch2; ch3](ch4); k

g)  Block ch; k


Question 2) Is the "refines" relation symmetric?
That is, if "pr1 <| pr2", does that imply "pr2 <| pr1"?


Question 3) Which of "||" and ";" binds stronger?
In other words, does "pr1 || pr2 ; pr3" equal "pr1 || (pr2 ; pr3)" or
"(pr1 || pr2) ; pr3"?


Question 4) Draw a diagram of the balanced request handler and the channels it uses


Question 5) In order to prove refinements, we need to provide a simulation relation
R of type "proc -> proc -> Prop", and prove the three conditions defined by "simulates".
If we just pick "fun pr1 pr2 => True" for R, which of these three conditions can/cannot
be proven? And what if we pick "fun pr1 pr2 => False"?


Question 6) The specification (addN 2 input output) in MessagesAndRefinement.v performs
the following steps:

1) It starts as

         (??input(n : nat); !!output(n + 2); Done)

   where it reads an input n

2) and then becomes

         (!!output(n + 2); Done)

   where it outputs (n + 2)

3) and then becomes

         Done

Write down the same kind of explanation of steps for the implementation (add2_once input output):
You should get steps numbered from 1) to 5).

  1) It starts as

        New[input;output](intermediate)

    where it creates a new channel to be used in the following processes. It registers `input` and `output` as channels which already exists, and it creates the variable `intermediate` to bind the new channel to in the following.

  2) It enters the parallel composition. The first process can make progress, where it reads an input n from `input`.

  3) Then, it `!!output(n + 1)` onto intermediate, and becomes Done.

  4) Now the second process can make progress, where it reads
  the value off `intermediate` (`!!output(n + 1)`, from above). Call this value `v`.

  5) Then, it `!!output(v + 1)` onto the output channel, and moves to `Done`.`

Question 7) In order to prove that the specification (addN 2 input output) can
simulate the implementation (add2_once input output), we have to show that each
implementation state has a corresponding specification state. Do so by filling
out the following table:

Impl  | Spec
state | state
------+------
  1   | [input: nothing, output: nothing]
  2   | [input: n, output: nothing]
  3   | [input: n, output: nothing]
  4   | [input: n, output: nothing]
  5   | [input: n, output: n + 2]

Question 8) If you completed the above table, you've actually just created a paper
proof of add2_once_refines_addN. Now study the Coq proof add2_once_refines_addN,
and look at the three subgoals opened after the call to first_order.
Where do they come from, and what does each of them ask you to prove?


 *)

(* Now you should be ready to start proving correctness!
   NOTE: You MUST use refinement ("_ <| _") and "simulates" to earn full credit on this pset.
   Hint: You should follow the same approach as add2_once_refines_addN and define a relation
   similar to R_add2, with the following signature, where we use "fs", "es", and "os" as
   abbreviations for full_store, even_store, and odd_store: *)

(* HINT 1-2 (see Pset13Sig.v) *)   
Inductive R (fs es os : fmap nat nat) (input output : channel) : proc -> proc -> Prop :=
| Stage0 :
  input <> output ->
  R fs es os input output
    (balanced_handler es os input output)
    (request_handler fs input output)

| Stage1 : forall forward_even,
    NoDup [input; output; forward_even] ->
    R fs es os input output
      (Block forward_even;
         New [input; output; forward_even] (forward_odd);
         request_dispatcher input forward_even forward_odd
         || request_handler es forward_even output
         || request_handler os forward_odd output)
      (request_handler fs input output)

| Stage2 : forall forward_even forward_odd,
    NoDup [input; output; forward_even; forward_odd] ->
    R fs es os input output
      (Block forward_even; Block forward_odd;
         request_dispatcher input forward_even forward_odd
         || request_handler es forward_even output
         || request_handler os forward_odd output)
      (request_handler fs input output)

| Stage3 :
  forall forward_even forward_odd {req : request} key client_id,
    NoDup [input; output; forward_even; forward_odd] ->
    get_key req = key ->
    get_id req = client_id ->
    R fs es os input output
      (Block forward_even; Block forward_odd;
         (if key mod 2 ==n 0
         then !! forward_even (req); Done
         else !! forward_odd (req); Done)
        || request_handler es forward_even output
        || request_handler os forward_odd output)
    (match fs $? key with
    | Some v => !! output (FOUND client_id key v); Done
    | None => !! output (NOT_FOUND client_id key); Done
    end)

| Stage4_even : forall forward_even forward_odd client_id key,
    NoDup [input; output; forward_even; forward_odd] ->
    key mod 2 = 0 ->
    R fs es os input output
      (Block forward_even; Block forward_odd;
         Done || match es $? key with
                    | Some v => !! output (FOUND client_id key v); Done
                    | None => !! output (NOT_FOUND client_id key); Done
                    end
        || request_handler os forward_odd output)
    (match fs $? key with
    | Some v => !! output (FOUND client_id key v); Done
    | None => !! output (NOT_FOUND client_id key); Done
    end)

| Stage4_odd : forall forward_even forward_odd client_id key,
    NoDup [input; output; forward_even; forward_odd] ->
    key mod 2 <> 0 ->
    R fs es os input output
      (Block forward_even; Block forward_odd;
         Done
        || request_handler es forward_even output
         || match os $? key with
                    | Some v => !! output (FOUND client_id key v); Done
                    | None => !! output (NOT_FOUND client_id key); Done
                end)
    (match fs $? key with
    | Some v => !! output (FOUND client_id key v); Done
    | None => !! output (NOT_FOUND client_id key); Done
    end)

| Stage5_finished_even : forall forward_even forward_odd,
    NoDup [input; output; forward_even; forward_odd] ->
    R fs es os input output
      (Block forward_even; Block forward_odd; Done || Done || request_handler os forward_odd output)
      Done

| Stage5_finished_odd : forall forward_even forward_odd,
    NoDup [input; output; forward_even; forward_odd] ->
    R fs es os input output
      (Block forward_even; Block forward_odd; Done || request_handler es forward_even output || Done)
      Done.

Global Hint Constructors R : core.

Definition R_alias_for_grading := R.
(* One more hint: You can use the "lists" tactic to prove any "NoDup" goals/contradictions. *)

(* And another hint: Here's some tactic which you might find handy in your proofs.
   Feel free to use and/or adapt it! *)

Ltac head e :=
  match e with
  | ?e _ => head e
  | _ => e
  end.

Ltac head_constructor e :=
  let e := eval cbv beta delta in e in (* this is quite agressive... *)
    let h := head e in
    is_constructor h.

Ltac t_step :=
  match goal with
  | |- _ => solve [propositional]
  | H : ?a = ?b |- _ => head_constructor a; head_constructor b; progress invert H
  (* the previous case can loop because repeat invert can loop,
           propositional earlier prunes the cases where this occurs in our proof *)
  | H : R _ _ _  _ _  _ _ |- _ => invert H
  | H:lstep ?c _ _ |- _ => head_constructor c; (apply invert_Recv in H; try subst) || invert H
  | H:lstepSilent ?c _ |- _ => head_constructor c; invert H
  | r : request |- _ => cases r
  | H : True |- _ => clear H
  | _ => progress (cbn [notUse Channel get_key] in *; simplify)
  | |- _ /\ _ => split
  | _ => solve [equality]
  end.

Ltac t := repeat t_step.

Theorem balanced_handler_refines_request_handler :
  forall input output fs es os,
    split_store fs es os -> input <> output ->
    balanced_handler es os input output <|
      request_handler fs input output.
Proof.
  simplify.
  exists (R fs es os input output).
  first_order.
  t.
  eauto.
  eauto.
  cases (key mod 2 ==n 0).
  t.
  t.
  cases (key0 mod 2 ==n 0).
  t.
  eauto.
  t.
  lists.
  cases (key0 mod 2 ==n 0).
  t.
  lists.
  t.
  eauto.
  cases (es $? key).
  eexists.
  split.
  apply TrcRefl.
  t.
  t.
  cases (es $? key).
  invert H11.
  lists.
  invert H11.
  lists.
  cases (os $? key).
  t.
  t.
  cases (os $? key).
  invert H10.
  lists.
  invert H10.
  lists.
  eauto.
  eauto.
  invert H4.
  invert H5.
  t.
  t.
  eexists.
  eexists.
  eexists.
  eauto.
  split.
  eauto.
  unfold request_handler.
  eauto.
  eauto.
  cases (get_key req mod 2 ==n 0).
  t.
  t.
  cases (es $? key).
  t.
  cases (fs $? key).
  erewrite H in Heq.
  assert (n = n0).
  equality.
  rewrite H4.
  eexists.
  eexists.
  eexists.
  eauto.
  t.
  eauto.
  eauto.
  eauto.
  erewrite H in Heq.
  equality.
  eauto.
  t.
  eexists.
  eexists.
  eexists.
  eauto.
  t.
  cases (fs $? key).
  erewrite H in Heq.
  equality.
  eauto.
  eauto.
  eauto.
  cases (os $? key).
  t.
  eexists.
  eexists.
  eexists.
  eauto.
  eexists.
  cases (fs $? key).
  erewrite H3 in Heq.
  assert (n = n0) by equality.
  rewrite H4.
  eauto.
  eauto.
  erewrite H3 in Heq.
  equality.
  eauto.
  eauto.
  t.
  eexists.
  eexists.
  t.
  eauto.
  cases (fs $? key).
  erewrite H3 in Heq.
  equality.
  equality.
  eauto.
  eauto.
  t.
  eexists.
  eexists.
  eexists.
  eauto.
  eexists.
  t.
  t.
  eauto.
  Unshelve.
  eauto.
Qed.

(* HINT 3-5 (see Pset13Sig.v) *)
Theorem balanced_handler_correct : correctness.
Proof.
  unfold correctness.
  simplify.
  eapply refines_couldGenerate.
  eapply balanced_handler_refines_request_handler.
  eauto.
  eauto.
  eauto.
Qed.

(* OPTIONAL exercise (ungraded, very short):
   Another important property of refinment is that any subpart of a larger
   program can be replaced with a refined version of it, yielding a refined
   version of the larger program. You can try it out by wrapping our one-shot
   server in Dup and using the "impl <| spec" fact you proved as a part of
   the last theorem to show "Dup impl <| Dup spec". This should be trivial
   once you have found the appropariate lemma from FRAP and factored out the
   appropriate refinement claim from the last proof. *)
Lemma multicorrectness : forall full_store even_store odd_store input output,
    split_store full_store even_store odd_store ->
    input <> output ->
    forall trace,
      couldGenerate (Dup (balanced_handler even_store odd_store input output)) trace ->
      couldGenerate (Dup (request_handler full_store input output)) trace.
Proof.
Admitted.

End Impl.

Module ImplCorrect : Pset13Sig.S := Impl.
