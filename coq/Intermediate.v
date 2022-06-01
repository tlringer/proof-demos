(*
 * Proof assistants for the working researcher:
 * a crash course that's just hard enough to be interesting.
 *
 * I'm leaving out answers for now because I want to try having Jeff (hi) work
 * through this. But I'll probably post them in another file at some point.
 *
 * This is based on a class exercise I did for my proof automation class.
 *)
Require Import Nat List Ascii Arith.
Open Scope char_scope.
Import ListNotations.

(*
 * This will show toy examples, so it's always worth noting here that people
 * have already used these proof assistants to formally verify an optimizing C
 * compiler, an operating system microkernel inside of an autonomous helicopter,
 * and so on and so forth. But this is mostly targeting Jeff, for whom I aim to
 * answer three questions:
 * 
 * 1. How do proof assistants actually work, and how do you use them?
 * 2. What opportunities are there to better automate proofs inside of them?
 * 3. Why are they such a cool domain for automation?
 *)

(*** 1. How Proof Assistants Work ***)

(*
 * How do proof assistants actually work, and how do you use them?
 *
 * Let's explore.
 *)

(* --- Datatypes --- *)

(*
 * Datatypes in Coq can be defined inductively. Consider lists:
 *)
Print list.

(*
 * Some example lists, using nice syntax Coq has defined for us:
 *)
Definition empty_nat : list nat := []. (* syntax for nil nat *)
Definition empty_char : list ascii := []. (* syntax for nil ascii *)
Definition one_two_three_four : list nat := [1; 2; 3; 4]. (* syntax for (cons 4 ...) *)
Definition x_y_z : list ascii := ["x"; "y"; "z"]. (* syntax for (cons "x" ...) *)

(* --- Functions and recursion --- *)

(*
 * We can write functions about list by pattern matching and recursion,
 * like the length function (in the standard library, too, but let's rewrite it):
 *)
Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0 (* empty case *)
  | _ :: tl => S (length tl) (* cons case *)
  end.

(* --- Induction is recursion --- *)

(*
 * Coq has a limited form of recursion, since it needs to terminate to avoid
 * paradoxes. Basically, one of the arguments needs to provably get smaller every time.
 * Like in our length definition, we recurse on only the tail of the list.
 * Coq checks this guard for recursion syntactically.
 *
 * Coq also supports induction. It turns out this is the same thing
 * as the limited supported form of recursion---they are equally expressive.
 * When we define a datatype like "list", we get an induction principle for free:
 *)
Check list_rect.
Print list_rect.

(*
 * The first thing that's cool about this is that we can write our functions
 * using these induction principles. Here's an alternative way to define list length:
 *)
Definition length' {A : Type} (l : list A) : nat :=
  list_rect
    (fun _ => nat) (* motive *)
    O (* empty or base case*)
    (fun (a : A) (tl : list A) (length_tl : nat) =>
      (* cons or inductive case *)
      S length_tl)
    l. (* argument to induct over *)

(*
 * Take a second to look at these side-by-side.
 *)
Print length.
Print length'.

(* --- Automation for induction --- *)

(*
 * By Curry-Howard, our length function is a proof, so we can actually
 * define a function for length the same way we'd write a proof, using these
 * high-level strategies called tactics. That's cool!!! Let's do that.
 *)
Theorem length'' {A : Type}:
  list A ->
  nat.
Proof.
  intros l. (* bind l : list A in our environment. *)
  induction l as [| h tl length_tl]. (* induct over l *)
  - apply 0. (* empty or base case *)
  - apply S. apply length_tl. (* cons or inductive case *)
Defined.

(* --- Compiling proof scripts --- *)

(*
 * This is obviously a boring proof of a boring theorem, for which there are
 * many other proofs that behave quite differently (e.g., always return 0).
 * But the important thing here is that tactics are really search procedures
 * for proof terms. They sort of compile to proof terms, if you will.
 * So we can print our proof of length'':
 *)
Print length''.

(*
 * And see that it's the same as length'. Indeed:
 *)
Theorem length''_OK {A : Type}:
  forall (l : list A), length'' l = length' l.
Proof.
  auto.
Qed.

(* --- Let's write a proof!!! --- *)

(*
 * Let's (re)define list append:
 *)
Fixpoint app {A : Type} (l1 l2 : list A) :=
  match l1 with
  | [] => l2
  | h :: tl => h :: app tl l2
  end.

(*
 * And reverse:
 *)
Fixpoint rev {A : Type} (l : list A) :=
  match l with
  | [] => []
  | h :: tl => app (rev tl) [h]
  end.

(*
 * Proof time! Let's do this together. Major hint: notice how our reverse function
 * needs append as a helper function? Well, proofs about reverse will need analogous
 * helper lemmas about append. It's often best, though, to start the proof, see where
 * you get stuck, and then use that to figure out the ideal helper lemma---much like many
 * programmers would do to find the right helper function. (For Jeff only: I should talk about
 * something particular here I hope I'll remember when I see this.)
 *
 * EXERCISE: Prove that the reverse function preserves the length of the input list.
 *)

(* any lemmas you want to write can go here *)

Theorem rev_pres_length {A : Type}:
  forall (l : list A),
    length (rev l) = length l.
Proof.
  (* your proof here *)
Admitted. (* <- change to Qed when done *)

(*
 * EXERCISE: Uncomment the line below to print the proof term that the tactic proof
 * of rev_pres_length produces. How easy it to tell what is going on? If you have time,
 * consider tweaking some tactics to see how the proof term changes.
 *)
(*Print rev_pres_length.*)

(* 
 * EXERCISE: What else might you want to prove about the list reverse function?
 * Think about things you'd test---then try to generalize them to the infinite.
 *)

(*** 2. Opportunities for Automation ***)

(*
 * What opportunities are there to better automate proofs inside of proof assistants?
 *
 * Roughly, we can think of automation in two different categories:
 * 1. building new constructs (for example, new tactics that better produce terms), and
 * 2. operating over existing constructs.
 *
 * I can list a million things here---instead I recommend quickly looking at the
 * schedule of my class for the kinds of problems people are interested in so far:
 * https://dependenttyp.es/classes/598sp2022.html#schedule
 *
 * EXERCISE: Think about what was hard about proving rev_pres_length.
 * What automation would help you?
 *)

(*** 3. Super Cool Domain ***)

(*
 * Why are proof assistants such a cool domain for automation?
 *
 * Separation of concerns!!!
 *
 * There is this beautiful separation between the automation producing the proof
 * and the kernel checking the proof (in this case, the kernel is a type checker).
 *
 * The kernel is small, trusted, and hopefully easy enough for a human to understand
 * (this is called the de Bruijn Criterion). We never change the kernel!
 *
 * Automation just produces an object that the kernel checks. So this means we can
 * stick arbitrary automation on top of all of this---classic symbolic procedures,
 * programming techniques like program & proof transformations, and even a
 * whole-ass neural network---at any layer above the kernel, in any combination.
 * And still know in the end whether what we have is correct, as long as the
 * specification (theorem we are proving) is vetted at some point.
 *
 * We have an oracle for correctness.
 *
 * Everything we do is grounded.
 *
 * EXERCISE: Can you think of automation in other domains where such an oracle would have
 * helped you significantly? Could those same methods be useful in proof automation?
 *)
