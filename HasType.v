Require Import Coq.Strings.String.

Require Import Term.
Require Import Ty.

Inductive index {A} : nat -> list A -> A -> Prop :=
| here : forall {x xs}, index 0 (x :: xs) x
| there : forall {n x y xs}, index n xs x -> index (S n) (y :: xs) x.

Theorem index_inj : forall {A n} {xs : list A} {a b}, index n xs a -> index n xs b -> a = b.
Proof.
  intros A n xs a b H. generalize dependent b.
  induction H; intros.
  - (* here *)
    inversion H. subst. reflexivity.
  - (* there *)
    apply IHindex.
    inversion H0. subst. assumption.
Qed.

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
