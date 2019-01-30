Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.

Inductive type : Type :=
| type_var : string -> type
| type_app : type -> type -> type
| type_arr : type.

Notation "a --> b" :=
  (type_app (type_app type_arr a) b) (at level 60, right associativity).

Inductive term : Type :=
| term_bvar : nat -> term
| term_fvar : string -> term
| term_app : term -> term -> term
| term_lam : term -> term
| term_shift : term -> term.

Inductive index {A} : nat -> list A -> A -> Prop :=
| here : forall {x xs}, index 0 (x :: xs) x
| there : forall {n x y xs}, index n xs x -> index (S n) (y :: xs) x.

Inductive has_type : (string -> option type) -> list type -> term -> type -> Prop :=
| ht_bvar :
    forall {fs bs n A},
      index n bs A ->
      has_type fs bs (term_bvar n) A

| ht_fvar :
    forall {fs bs s A},
      fs s = Some A ->
      has_type fs bs (term_fvar s) A

| ht_app :
    forall {fs bs f x A B},
      has_type fs bs f (A --> B) ->
      has_type fs bs x A ->
      has_type fs bs (term_app f x) B

| ht_lam :
    forall {fs bs x A B},
      has_type fs (A :: bs) x B ->
      has_type fs bs (term_lam x) (A --> B)

| ht_shift :
    forall {fs bs x A B},
      has_type fs bs x A ->
      has_type fs (B :: bs) (term_shift x) A.

Notation "fs || bs |- x ∈ T" := (has_type fs bs x T) (at level 45, no associativity).

Definition substituteNat (n' : nat) (n : nat) (x : term) : term :=
  match eqb n' n with
  | true => x
  | false => term_bvar n'
  end.
Hint Unfold substituteNat.

Fixpoint substituteNat_inner (acc : nat -> nat) (n' : nat) (n : nat) (x : term) : term :=
  match n', n with
  | O, S k => term_bvar (acc n')
  | S k, O => term_bvar (acc n')
  | O, O => x
  | S k', S k => substituteNat_inner (fun x => S (acc x)) k' k x
  end.
Hint Unfold substituteNat_inner.

Definition substituteNat' (n' : nat) (n : nat) (x : term) : term :=
  substituteNat_inner (fun x => x) n' n x.
Hint Unfold substituteNat'.

Theorem substituteNat'_refines_substituteNat :
  forall n' n x,
    substituteNat n' n x = substituteNat' n' n x.
Proof.
  unfold substituteNat. unfold substituteNat'.
  induction n'.
  - (* O *)
    unfold substituteNat_inner.
    destruct n. reflexivity. reflexivity.
  - (* S *)
    destruct n.
    + (* O *)
      reflexivity.
    + simpl.
      destruct (Nat.eq_dec n' n).
      * (* = *)
        rewrite e in *. rewrite (Nat.eqb_refl n). unfold substituteNat_inner.



Theorem substituteNat_type :
  forall {n' n fs bs x T},
    fs || bs |- x ∈ T ->
    fs || bs |- term_bvar n' ∈ T ->
    fs || bs |- substituteNat n' n x ∈ T.
Proof.
  intro n'. destruct n'.
  - (* O *)
    intro n. destruct n as [| k].
    + (* O *)
      auto.
    + (* S *)
      auto.
  - (* S *)
    intro n. destruct n as [| k].
    + (* O *)
      auto.
    + (* S *)
      intros fs bs x T xT varT.
      unfold substituteNat. simpl.
      destruct (Nat.eq_dec n' k).
      * (* = *)
        rewrite e in *. rewrite (Nat.eqb_refl k). assumption.
      * (* <> *)
        apply (Nat.eqb_neq n' k) in n. rewrite n. assumption.
Qed.