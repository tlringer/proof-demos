Require Import NatBin List.

(*
 * This is another Dylan tutorial, building on NatBin.v.
 * This time we look at some other equivalences like
 * the unary/binary example.
 *)

(* --- Equivalence 1: Unary and Ternary --- *)

(*
 * This is another change in shape (recursive structure), much like
 * the unary/binary example.
 *)

Module One.

(*
 * This will be a lot like our unary and binary examples,
 * but now we look at unary and ternary instead.
 * Ternary can be defined a lot like binary:
 *)
Inductive tern_pos : Set :=
| O1 : tern_pos              (* 01 *)
| O2 : tern_pos              (* 02 *)
| xO : tern_pos -> tern_pos  (* shift left and add 0 *)
| x1 : tern_pos -> tern_pos  (* shift left and add 1 *)
| x2 : tern_pos -> tern_pos. (* shift left and add 2 *)

Inductive tern : Set :=
| OO : tern                  (* 00 *)
| pos : tern_pos -> tern.    (* positive ternary numbers *)

(* --- Some related terms --- *)

(*
 * How are these related? Let's define corresponding points/terms.
 *)
Definition zeros : nat * tern :=
  (O, OO). (* 0, 00 *)

Definition ones : nat * tern :=
  (S O, pos O1). (* 1, 01 *)

Definition twos : nat * tern :=
  (S (S O), pos O2). (* 2, 02 *)

Definition threes : nat * tern :=
  (S (S (S O)), pos (xO O1)). (* 3, 10 *)

Definition fours : nat * tern :=
  (S (S (S (S O))), pos (x1 O1)). (* 4, 11 *)

Definition fives : nat * tern :=
  (S (S (S (S (S O)))), pos (x2 O1)). (* 5, 12 *)

Definition sixes : nat * tern :=
  (S (S (S (S (S (S O))))), pos (xO O2)). (* 6, 20 *)

Definition sevens : nat * tern :=
  (S (S (S (S (S (S (S O)))))), pos (x1 O2)). (* 7, 21 *)

Definition eights : nat * tern :=
  (S (S (S (S (S (S (S (S O))))))), pos (x2 O2)). (* 8, 22 *)

Definition nines : nat * tern :=
  (S (S (S (S (S (S (S (S (S O)))))))), pos (xO (xO O1))). (* 9, 100 *)

(*
 * We can similary define S over ternary:
 *)
Fixpoint S_tern_pos (t : tern_pos) : tern_pos :=
  match t with
  | O1 => O2
  | O2 => xO O1
  | xO t' => x1 t'
  | x1 t' => x2 t'
  | x2 t' => xO (S_tern_pos t')
  end.

Definition S_tern (t : tern) : tern :=
  match t with
  | OO => pos O1
  | pos t' => pos (S_tern_pos t')
  end.

(*
 * Likewise in the opposite direction:
 *)
Definition xO_nat (n : nat) :=
  add n (add n n).

Definition x1_nat (n : nat) :=
  S (add n (add n n)).

Definition x2_nat (n : nat) :=
  S (S (add n (add n n))).

(*
 * Our functions for the equivalence:
 *)
Fixpoint f (n : nat) : tern :=
  match n with
  | O => OO
  | S m => S_tern (f m)
  end.

Fixpoint g_pos (t : tern_pos) : nat :=
  match t with
  | O1 => S O
  | O2 => S (S O)
  | xO t' => xO_nat (g_pos t')
  | x1 t' => x1_nat (g_pos t')
  | x2 t' => x2_nat (g_pos t')
  end.

Definition g (t : tern) : nat :=
  match t with
  | OO => O
  | pos t' => g_pos t'
  end.

(*
 * Lemmas for equivalence proof:
 *)
Lemma S_OK :
  forall (t : tern), g (S_tern t) = S (g t).
Proof.
  induction t as [|t']; auto.
  induction t'; auto.
  simpl in *. rewrite IHt'. unfold xO_nat, x2_nat. simpl.
  f_equal. rewrite add_n_Sm.
  f_equal. rewrite add_n_Sm. 
  apply add_n_Sm.
Qed.

Definition xO_tern (t : tern) :=
  match t with
  | OO => OO
  | pos t' => pos (xO t')
  end.

Lemma xO_OK:
  forall (n : nat), f (xO_nat n) = xO_tern (f n).
Proof.
  intros n. induction n; auto.
  simpl. unfold xO_nat in IHn.
  rewrite add_n_Sm. simpl in *.
  rewrite add_n_Sm. simpl in *.
  rewrite add_n_Sm. simpl in *.
  rewrite IHn. destruct (f n); auto.
Qed.

Definition x1_tern (t : tern) :=
  match t with
  | OO => pos O1
  | pos t' => pos (x1 t')
  end.

Lemma x1_OK:
  forall (n : nat), f (x1_nat n) = x1_tern (f n).
Proof.
  intros n. induction n; auto.
  simpl. unfold x1_nat in IHn.
  rewrite add_n_Sm. simpl in *. 
  rewrite add_n_Sm. simpl in *. 
  rewrite add_n_Sm. simpl in *.
  rewrite IHn.
  destruct (f n); auto.
Qed.

Definition x2_tern (t : tern) :=
  match t with
  | OO => pos O2
  | pos t' => pos (x2 t')
  end.

Lemma x2_OK:
  forall (n : nat), f (x2_nat n) = x2_tern (f n).
Proof.
  intros n. induction n; auto.
  simpl. unfold x2_nat in IHn.
  rewrite add_n_Sm. simpl in *. 
  rewrite add_n_Sm. simpl in *. 
  rewrite add_n_Sm. simpl in *.
  rewrite IHn.
  destruct (f n); auto.
Qed.

Theorem section:
  forall (n : nat), g (f n) = n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite S_OK. rewrite IHn. reflexivity.
Qed.

Theorem retraction:
  forall (t : tern), f (g t) = t.
Proof.
  intros t. induction t as [|t']; auto.
  induction t'; auto; simpl in IHt'.
  + simpl. rewrite xO_OK. rewrite IHt'. reflexivity.
  + unfold g. replace (g_pos (x1 t')) with (x1_nat (g_pos t')) by reflexivity.
    rewrite x1_OK. rewrite IHt'. reflexivity.
  + unfold g. replace (g_pos (x2 t')) with (x2_nat (g_pos t')) by reflexivity.
    rewrite x2_OK. rewrite IHt'. reflexivity.
Qed.

End One.

(* --- Equivalence 2: bin_tree / rose_tree --- *)

Module two.

(*
 * See: https://twitter.com/PTOOP/status/1575238476861153280
 * This is another change in shape as well. I have not finished
 * proving the equivalence yet. I'm also removing the type parameter
 * T because it complicates things a lot.
 *
 * TODO the current function here is incorrect! Unsure which one.
 *)

Inductive bin_tree : Type :=
| leaf : bin_tree
| node : bin_tree -> bin_tree -> bin_tree.

Inductive rose_tree : Type :=
| rose : list rose_tree -> rose_tree.

Fixpoint binRose (b : bin_tree) : rose_tree :=
  match b with
  | leaf => rose nil
  | node l r =>
      match binRose r with
      | rose rs => rose (cons (binRose l) rs)
      end
  end.

Section rose_tree_ind'.
  Variable P : rose_tree -> Prop.

  Hypothesis rose_case : forall (rs : list rose_tree),
    Forall P rs -> P (rose rs).

  Fixpoint rose_tree_ind' (r : rose_tree) : P r :=
    match r with
    | rose rs =>
      let fars := list_ind (Forall P) (Forall_nil P) (fun r' rs' Hrs' => Forall_cons r' (rose_tree_ind' r') Hrs') rs in
      rose_case rs fars
    end.
End rose_tree_ind'.

Eval compute in (binRose leaf). (* rose nil *)
Eval compute in (binRose (node leaf leaf)). (* rose (rose nil :: nil) *)
Eval compute in (binRose (node (node leaf leaf) leaf)). (* rose (rose (rose nil :: nil) :: nil) *)
Eval compute in (binRose (node leaf (node leaf leaf))). (* rose (rose nil :: rose nil :: nil) *)
Eval compute in (binRose (node (node (node leaf leaf) (node leaf leaf)) (node leaf leaf))).

Fixpoint roseBin (r: rose_tree) : bin_tree :=
match r with
| rose rs =>
fold_right (fun r' bt => node (roseBin r') bt) leaf rs
end.


Eval compute in (roseBin (binRose (node (node leaf leaf) (node leaf leaf)))).

(*
(* Max Fan wrote this function via tactics, here is the simplified term: *)
Definition roseBinSub (h : rose_tree) (tl : list rose_tree) (roseBin_tl : bin_tree) :=     
  match h with
  | rose hl =>
    list_rect 
      (fun _ : list rose_tree => _)
      (leaf, roseBin_tl)
      (fun (hl_h : rose_tree) (hl_tl : list rose_tree) (roseBin_hl_tl : _) =>
         (* (node (fst roseBin_hl_tl) (snd roseBin_hl_tl), roseBin_tl)) *)

         (node (fst roseBin_hl_tl) roseBin_tl, (snd roseBin_hl_tl))) 
      hl
   end.

Definition roseBin (r: rose_tree) : bin_tree :=
  match r with
  | rose l =>
     list_rec 
       (fun _ : list rose_tree => bin_tree) 
       leaf
       (fun (h : rose_tree) (tl : list rose_tree) (roseBin_tl : bin_tree) => 
          node (fst (roseBinSub h tl roseBin_tl)) (snd (roseBinSub h tl roseBin_tl)))
       l
  end.

*)

Eval compute in (roseBin (binRose (node (node leaf leaf) (node leaf leaf)))).

(*
Example wrong:
  (roseBin (binRose (node (node leaf leaf) (node leaf leaf)))) 
    = node (node leaf (node leaf leaf)) (node leaf leaf).
Proof.
reflexivity.
Qed.

*)

Lemma roseBin_cons :
  forall (r : rose_tree) (rs : list rose_tree),
    roseBin (rose (r::rs)) = node (roseBin r) (roseBin (rose rs)).
Proof.
  reflexivity.
Qed.

Theorem section' :
  forall (b : bin_tree) (rs : list rose_tree),
    roseBin (rose (binRose b::rs)) = node b (roseBin (rose rs)).
Proof.
induction b; intros; auto.
- simpl roseBin.
  f_equal.
  destruct (binRose b2) eqn:?.
  destruct (binRose b1) eqn:?.
  rewrite IHb1.
  f_equal.
  enough (roseBin (rose (rose l::nil)) = node b2 leaf).
  + inversion H.
    simpl.
    reflexivity.
  + apply IHb2.
Qed.

Theorem section :
  forall (b : bin_tree),
    roseBin (binRose b) = b.
Proof.
induction b; auto; intros; simpl.
- destruct (binRose b2).
  simpl.
  rewrite IHb1.
  f_equal.
  rewrite <- IHb2.
  reflexivity.
Qed.

Theorem retraction :
  forall (r : rose_tree),
    binRose (roseBin r) = r.
Proof.
fix H 1.
destruct r.
induction l.
- reflexivity.
- simpl.
  simpl in IHl.
  rewrite IHl.
  simpl.
  rewrite (H a).
  reflexivity.
Qed.

(*
TODO refolding behavior is hard omg
*)

(*
TODO then write section/retraction proofs, which will suck

 *)

End two.

(* --- Equivalence 3: No recursion --- *)

Module three.

(*
 * From https://github.com/uwplse/pumpkin-pi/blob/master/plugin/coq/playground/constr_refactor.v.
 * This is an equivalence without any recursion at all.
 * What is interesting here is that it is fully classified by the 
 * only two possible examples of constructors. So when learning to
 * synthesize and prove the functions that actually make up
 * equivalences, a tool that cannot learn this is in a bad place.
 *)

Inductive I :=
| A : I
| B : I.

Inductive bool : Set :=
| true : bool
| false : bool.

Inductive J :=
| makeJ : bool -> J.

(* the examples that fully classify the equivalence: *)
Definition trues := (A, makeJ true).
Definition falses := (B, makeJ false).

(* the equivalence: *)
Definition f (i : I) : J :=
  match i with
  | A => makeJ true
  | B => makeJ false
  end.

Definition g (j : J) : I :=
  match j with
  | makeJ true => A
  | makeJ false => B
  end.

Theorem section:
  forall (i : I), g (f i) = i.
Proof.
  intros i. induction i; reflexivity.
Qed.

Theorem retraction:
  forall (j : J), f (g j) = j.
Proof.
  intros j. induction j. induction b; reflexivity.
Qed.

End three.

(* --- Equivalence 4: Variations on a theme --- *)

Module four.

(*
 * This is a modification of the previous equivalence, but with some changes to
 * make it recursive. This should still be fairly syntactic, since there's not
 * a change in inductive structure. But it's slightly more interesting than the
 * previous example.
 *)

Inductive I : Set :=
| A : I
| B : I -> I.

Inductive J :=
| makeJ : nat -> J.

(* Examples: *)
Definition zeros := (A, makeJ O).
Definition ones := (B A, makeJ (S O)).
Definition twos := (B (B A), makeJ (S (S O))).

(* the equivalence: *)
Fixpoint f (i : I) : J :=
  match i with
  | A => makeJ O
  | B i' =>
     match f i' with
     | makeJ n => makeJ (S n)
     end
  end.

Program Definition g (j : J) : I.
Proof.
  induction j. induction n.
  - apply A.
  - apply B. apply IHn.
Defined.

Theorem section:
  forall (i : I), g (f i) = i.
Proof.
  intros i. induction i.
  - reflexivity.
  - simpl. destruct (f i). simpl. simpl in IHi.
    rewrite IHi. reflexivity.
Qed.

Theorem retraction:
  forall (j : J), f (g j) = j.
Proof.
  intros j. induction j. induction n.
  - reflexivity.
  - simpl. simpl in IHn. rewrite IHn. reflexivity.
Qed.

End four.
