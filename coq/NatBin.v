(*
 * This tutorial is for Shizhuo! But anyone else who likes it
 * is welcome to take a look at it. It's about pairs of unary
 * and binary natural numbers in Coq, and why unary and binary
 * numbers are equivalent, and what that means.
 *
 * Consider the unary natural numbers, which we redefine
 * from scratch inductively:
 *)
Inductive nat : Set :=
| O : nat           (* 0 *)
| S : nat -> nat.   (* successor (1 + n) *)

(*
 * Consider also the binary natural numbers, which we also
 * redefine from scratch inductively, starting with the
 * positive binary numbers:
 *)
Inductive bin_pos : Set :=
| O1 : bin_pos             (* 01 *)
| xO : bin_pos -> bin_pos  (* shift left and add 0 *)
| x1 : bin_pos -> bin_pos. (* shift left and add 1 *)
(*
 * and continuing:
 *)
Inductive bin : Set :=
| OO : bin                 (* 00 *)
| pos : bin_pos -> bin.    (* positive binary numbers *)

(* --- Some related terms --- *)

(*
 * How are these related? Let's define corresponding points/terms.
 *)
Definition zeros : nat * bin :=
  (O, OO). (* 0, 00 *)

Definition ones : nat * bin :=
  (S O, pos O1). (* 1, 01 *)

Definition twos : nat * bin :=
  (S (S O), pos (xO O1)). (* 2, 10 *)

Definition threes : nat * bin :=
  (S (S (S O)), pos (x1 O1)). (* 3, 11 *)

Definition fours : nat * bin :=
  (S (S (S (S O))), pos (xO (xO O1))). (* 4, 100 *)

Definition fives : nat * bin :=
  (S (S (S (S (S O)))), pos (x1 (xO O1))). (* 5, 101 *)

Definition sixes : nat * bin :=
  (S (S (S (S (S (S O))))), pos (xO (x1 O1))). (* 6, 110 *)

(* --- Converting from unary to binary --- *)

(*
 * In general, we can define a function that gets us from unary
 * to binary. First we define the successor function over
 * positive binary numbers:
 *)
Fixpoint S_bin_pos (b : bin_pos) : bin_pos :=
  match b with
  | O1 => xO O1
  | xO bb => x1 bb
  | x1 bb => xO (S_bin_pos bb)
  end.
(*
 * and then over all of binary:
 *)
Definition S_bin (b : bin) : bin :=
  match b with
  | OO => pos O1
  | pos bb => pos (S_bin_pos bb)
  end.

(*
 * Our function f maps O to OO, and S n to S_bin (f n):
 *)
Fixpoint f (n : nat) : bin :=
  match n with
  | O => OO
  | S m => S_bin (f m)
  end.

(*
 * Some tests, which correspond to the examples above:
 *)
Eval compute in (f O).
Eval compute in (f (S O)).
Eval compute in (f (S (S O))).
Eval compute in (f (S (S (S O)))).
Eval compute in (f (S (S (S (S O))))).
Eval compute in (f (S (S (S (S (S O)))))).
Eval compute in (f (S (S (S (S (S (S O))))))).

(* --- Getting from binary to unary --- *)

(*
 * We can also go back in the opposite direction.
 * The easiest way is to play a similar game.
 * We define what "shift to the left and add zero"
 * and "shift to the left and add one" correspond to in unary.
 * The function falls out of that by pattern matching and
 * recursion.
 *
 * First, let's define addition (since we defined
 * numbers from scratch, this isn't a primitive):
 *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m              (* O + m = m *)
  | S p => S (add p m)  (* (1 + p) + m = 1 + (p + m) *)
  end.

(*
 * Now we can define shifting to the left and adding zero/one:
 *)
Definition xO_nat (n : nat) :=
  add n n.

Definition x1_nat (n : nat) :=
  S (add n n).

(*
 * Now we can get back from binary to unary, starting with this:
 *)
Fixpoint g_pos (b : bin_pos) : nat :=
  match b with
  | O1 => S O
  | xO bb => xO_nat (g_pos bb)
  | x1 bb => x1_nat (g_pos bb)
  end.
(*
 * and concluding with this:
 *)
Definition g (b : bin) : nat :=
  match b with
  | OO => O
  | pos bb => g_pos bb
  end.

(* --- This is an equivalence! --- *)

(*
 * Some lemmas, first, about the auxiliary functions we defined.
 * I'm going to automate these a bit since the proofs are not
 * super important.
 *)
Lemma add_n_Sm:
  forall (n m : nat),
    add n (S m) = S (add n m).
Proof.
  induction n; simpl; congruence.
Qed.

Lemma S_OK :
  forall (b : bin), g (S_bin b) = S (g b).
Proof.
  induction b as [|bb]; auto.
  induction bb; auto.
  simpl in *. rewrite IHbb. unfold xO_nat, x1_nat. simpl.
  f_equal. apply add_n_Sm.
Qed.

Definition xO_bin (b : bin) :=
  match b with
  | OO => OO
  | pos bb => pos (xO bb)
  end.

Lemma xO_OK:
  forall (n : nat), f (xO_nat n) = xO_bin (f n).
Proof.
  intros n. induction n; auto.
  simpl. unfold xO_nat in IHn.
  rewrite add_n_Sm. simpl in *. rewrite IHn.
  destruct (f n); auto.
Qed.

Definition x1_bin (b : bin) :=
  match b with
  | OO => pos O1
  | pos bb => pos (x1 bb)
  end.

Lemma x1_OK:
  forall (n : nat), f (x1_nat n) = x1_bin (f n).
Proof.
  intros n. induction n; auto.
  simpl. unfold x1_nat in IHn.
  rewrite add_n_Sm. simpl in *. rewrite IHn.
  destruct (f n); auto.
Qed.

(*
 * OK, the proofs we care about! These are worth stepping through.
 *)
Theorem section:
  forall (n : nat), g (f n) = n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite S_OK. rewrite IHn. reflexivity.
Qed.

Theorem retraction:
  forall (b : bin), f (g b) = b.
Proof.
  intros b. induction b as [|bb].
  - reflexivity.
  - induction bb.
    + reflexivity.
    + simpl in *. rewrite xO_OK. rewrite IHbb. reflexivity.
    + unfold g. replace (g_pos (x1 bb)) with (x1_nat (g_pos bb)) by reflexivity.
      rewrite x1_OK. simpl in IHbb. rewrite IHbb.
      reflexivity.
Qed.


