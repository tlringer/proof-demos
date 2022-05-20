(*
 * It's good to step through this interactively rather than look at it statically.
 * In any proof IDE, when you step through this interactively, Coq will show you
 * your assumptions and goals at each step of the proof, which is really helpful.
 * I'm happy to show people this IRL or help you get Coq set up or whatever.
 *
 * This example is based on an example that Sanjay brought up in a conversation.
 * It mostly demonstrates the notion of what I would call a "unit proof"---kind of
 * like a unit test in that it proves properties of a small and reusable function
 * probably used lots of places in larger code.
 *
 * It's really common to have a lot of lemmas like this about reusable functions
 * in proof libraries. Finding them is another story---searching for relevant
 * proofs is still kind of a nightmare (a number of UIUC students are interested
 * in fixing this, as am I), and adapting them to slightly different use cases
 * in client code can still be annoying (this is something I have contributed
 * toward fixing for a while, including in my PhD thesis on proof repair).
 *
 * Anyways enough words; let's hack.
 *)

Require Import String.

(*
 * A string in Coq is one of two things: either it is empty, or it is
 * the result of sticking an ascii character in front of another string.
 * So if we type:
 *)
Print string.
(*
 * and step down, we'll see this definition:
 *
 * Inductive string : Set :=
 * | EmptyString : string
 * | String : Ascii.ascii -> string -> string.
 *
 * We can think of this like a list of ascii characters.
 * There is already notation in Coq that lets us type in normal strings like
 * "" and "foo" and will desugar to use this definition of strings.
 *)
Open Scope string_scope.

(*
 * Coq has its own string functions, along with lemmas and proofs about strings:
 * https://coq.inria.fr/library/Coq.Strings.String.html
 *
 * But for the sake of demonstration, I'll reimplement some of them and
 * prove things about them. Let's start with appending two strings:
 *)
Fixpoint append (s1 s2 : string) : string :=
  match s1 with
  | "" => s2
  | String hd tl => String hd (append tl s2)
  end.
Notation "s1 ++ s2" := (append s1 s2).

(*
 * Let's write a function that takes the length of each list:
 *)
Fixpoint length (s : string) : nat :=
  match s with
  | "" => 0
  | String _ tl => 1 + (length tl) 
  end.

(*
 * Now let's prove that append preserves length:
 *)
Lemma app_length:
  forall (s1 s2 : string),
    length (s1 ++ s2) =
    length s1 + length s2.
Proof.
  induction s1.
  - (* the base (empty) case holds by reflexivity *)
    auto. 
  - (* the inductive case holds by the inductive hypothesis *)
    intros s2. simpl. rewrite IHs1. reflexivity.
Qed.

(*
 * Just for fun, if you want to see the proof term that this sequence of
 * tactics compiles down to, you can actually print the proof term:
 *)
Print app_length.
(*
 * This mostly matters for advance use or if you're interested in building
 * automation. My thesis has a good overview of the correspondence between
 * tactics and terms in Chapter 2: https://dependenttyp.es/pdf/thesis.pdf.
 *)

(*
 * Let's make a function that behaves the way Sanjay's made up function
 * ought to behave. Here's a function that just repeats the same string
 * three times:
 *)
Definition threpeat (s : string) :=
  s ++ s ++ s.

(*
 * Threpeat triples length:
 *)
Lemma threpeat_length:
  forall (s : string),
    length (threpeat s) =
    3 * (length s).
Proof.
  (* this holds by the lemma we just proved *)
  intros s. simpl. unfold threpeat.
  repeat rewrite app_length.
  auto with arith.
Qed.

(*
 * Consider, in contrast, testing this property (just going to print the
 * output for now, but you could test equality and so on):
 *)
Eval compute in (length (threpeat "")). (* 0 : nat *)
Eval compute in (length (threpeat "Hi")). (* 6 : nat *)

(*
 * A proof is an infinite test that covers all of these cases.
 * So the specification need not be exhaustive!
 * It can be anything you'd like to test about your function, really.
 *
 * This is just a taste, but hopefully it's a fun and interesting one to start.
 *)








