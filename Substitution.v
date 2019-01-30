Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.

Require Import Term.
Require Import Ty.
Require Import HasType.

Definition substituteNat_spec (n' : nat) (n : nat) (x : term) : term :=
  match eqb n' n with
  | true => x
  | false => term_bvar n'
  end.
Hint Unfold substituteNat_spec.

Theorem substituteNat_spec_type :
  forall {n' n fs bs x T},
    fs || bs |- x ∈ T ->
    fs || bs |- term_bvar n' ∈ T ->
    fs || bs |- substituteNat_spec n' n x ∈ T.
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
      unfold substituteNat_spec. simpl.
      destruct (Nat.eq_dec n' k).
      * (* = *)
        rewrite e in *. rewrite (Nat.eqb_refl k). assumption.
      * (* <> *)
        apply (Nat.eqb_neq n' k) in n. rewrite n. assumption.
Qed.

Fixpoint substituteNat_inner (acc : nat -> nat) (n' : nat) (n : nat) (x : term) : term :=
  match n', n with
  | O, S k => term_bvar (acc n')
  | S k, O => term_bvar (acc n')
  | O, O => x
  | S k', S k => substituteNat_inner (fun x => acc (S x)) k' k x
  end.
Hint Unfold substituteNat_inner.

Definition substituteNat (n' : nat) (n : nat) (x : term) : term :=
  substituteNat_inner (fun x => x) n' n x.
Hint Unfold substituteNat.

Theorem substituteNat_inner_eq : forall n f x, substituteNat_inner f n n x = x.
Proof.
  induction n.
  - (* O *)
    reflexivity.
  - simpl. intros. apply IHn.
Qed.

Theorem substituteNat_inner_neq :
  forall n' n f x, n' <> n -> substituteNat_inner f n' n x = term_bvar (f n').
Proof.
  induction n', n.
  - (* O, O *)
    intros f x Contra. exfalso. apply Contra. reflexivity.
  - (* O, S *)
    auto.
  - (* S, O *)
    auto.
  - simpl. intros f x H. apply IHn'.
    apply (Nat.succ_inj_wd_neg n' n) in H. assumption.
Qed.

Theorem substituteNat_correct :
  forall n' n x,
    substituteNat_spec n' n x = substituteNat n' n x.
Proof.
  unfold substituteNat_spec. unfold substituteNat.
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
        rewrite e in *. rewrite (Nat.eqb_refl n).
        intros. symmetry. apply substituteNat_inner_eq.
      * (* <> *)
        pose (n0' := n0).
        apply Nat.eqb_neq in n0'. rewrite n0'.
        intros. symmetry.
        apply substituteNat_inner_neq.
        assumption.
Qed.

Theorem substituteNat_type :
  forall {n' n fs bs x T},
    fs || bs |- x ∈ T ->
    fs || bs |- term_bvar n' ∈ T ->
    fs || bs |- substituteNat n' n x ∈ T.
Proof.
  intros.
  rewrite <- (substituteNat_correct n' n x).
  apply substituteNat_spec_type. assumption. assumption.
Qed.