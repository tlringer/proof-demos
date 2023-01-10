(*
 * Illustration of a common problem I see both newer students
 * and machine learning tools encounter when trying to write proofs.
 * The problem is what I call a "death loop," namely trying the
 * same thing over and over again but not noticing that the state
 * is changing only in ways that do not actually help you, since it
 * feels like you're making progress.
 *)

Require Import List.

(* Let's start with a good version that doesn't fall into a death loop: *)
Lemma app_nil_r_good:
  forall {T : Type} (l : list T),
    l ++ nil = l.
Proof.
  intros. induction l.
  - auto. (* nil ++ nil = nil by reflexivity *)
  - simpl. (* e.t.s that a :: l ++ nil = a :: l *)
    f_equal. (* e.t.s that l ++ nil = l *)
    auto. (* this holds by the inductive hypothesis *)
Qed.

(* With newer students, and with machine learning models, we often see
   something like this happen instead: *)
Lemma app_nil_r_bad:
  forall {T : Type} (l : list T),
    l ++ nil = l.
Proof.
  intros. induction l.
  - auto. (* nil ++ nil = nil by reflexivity *)
  - simpl. (* e.t.s that a :: l ++ nil = a :: l *)
    induction l. (* we can show that by induction over l *)
    + auto. (* a :: nil ++ nil = a :: nil by reflexivity. *)
    + simpl. (* e.t.s that a :: a0 :: l ++ nil = a :: a0 :: l *)
      (* ... could get stuck continuing this way forever *)
Abort.

(* The loop here happens because we induct over the same variable
   within a subcase generated by induction over that very variable.
   So we were at a proof state:

     T : Type
     a : T
     l : list T
     IHl : l ++ nil = l
     ______________________________________(1/1)
     a :: l ++ nil = a :: l

   And by the time we induct again and get to the second inductive
   case, we're at a proof state:

     T : Type
     a, a0 : T
     l : list T
     IHl : (a0 :: l) ++ nil = a0 :: l
     IHl0 : l ++ nil = l -> a :: l ++ nil = a :: l
     ______________________________________(1/1)
     a :: a0 :: l ++ nil = a :: a0 :: l
*)

(* At that point, we're no closer to the end than we were before.
   We can still finish the proof if we want: *)
Lemma app_nil_r_bad:
  forall {T : Type} (l : list T),
    l ++ nil = l.
Proof.
  intros. induction l.
  - auto. (* nil ++ nil = nil by reflexivity *)
  - simpl. (* e.t.s that a :: l ++ nil = a :: l *)
    induction l. (* we can show that by induction over l *)
    + auto. (* a :: nil ++ nil = a :: nil by reflexivity. *)
    + simpl. (* e.t.s that a :: a0 :: l ++ nil = a :: a0 :: l *)
      f_equal. (* e.t.s that a0 :: l ++ nil = a0 :: l *)
      auto. (* this holds by the [first] inductive hypothesis *)
Qed.

(*
 * But we could also keep looping infinitely, and in practice,
   many newer students and machine learning models do just this
   until they time out (machines) or get frustrated (students).

   Maybe, in the short term, some kind of repetition penalty
   is enough to catch this. But this is a bit of a hack.
   We could easily generate a different name for the variable
   in the inductive case that we induct over the second time,
   for example (and custom names for inductive cases are fairly
   common in Coq proof developments):
*)
Lemma app_nil_r_bad_subtler:
  forall {T : Type} (l : list T),
    l ++ nil = l.
Proof.
  intros. induction l as [|a l0].
  - auto. (* nil ++ nil = nil by reflexivity *)
  - simpl. (* e.t.s that a :: l0 ++ nil = a :: l0 *)
    induction l0 as [|b l1]. (* we can show that by induction over l0 *)
    + auto. (* a :: nil ++ nil = a :: nil by reflexivity. *)
    + simpl. (* e.t.s that a :: b :: l1 ++ nil = a :: b :: l1 *)
      (* ... could get stuck continuing this way forever *)
Abort.

(* Now our induction l0 takes is in a loop after inducting over l.
   Our two states that are in some sense "the same" (i.e., the latter
   is no closer to the goal than the former) are this state:

     T : Type
     a : T
     l : list T
     IHl : l0 ++ nil = l0
     ______________________________________(1/1)
     a :: l0 ++ nil = a :: l0

   and this state:

     T : Type
     a, b : T
     l1 : list T
     IHl0 : (b :: l1) ++ nil = b :: l1
     IHl1 : l1 ++ nil = l1 -> a :: l1 ++ nil = a :: l1
     ______________________________________(1/1)
     a :: b :: l1 ++ nil = a :: b :: l1
*)

(* RESEARCH QUESTION: What makes these two states "the same"
   in a way that we could actually teach a machine to use
   in proof automation? I don't know the answer.

   As a human, I get a sense of "deja vu," like I realize I'm
   doing the same thing over and over again, and I stop.
   But I don't know how it is I get the sense that I'm repeating myself! *)

(* Hopefully I'll add more examples of these later!
   Including more interesting ones, as they come up.
   Like this is even more of a problem when the goal is
   not provable but you feel like you're getting closer,
   or with proofs that are really cyclic where you need
   a more general IH. I can add an even/odd example for that. *)