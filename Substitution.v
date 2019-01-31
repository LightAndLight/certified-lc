Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.

Require Import LC.Term.
Require Import LC.Ty.
Require Import LC.HasType.

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

Theorem substituteNat_eq : forall n x, substituteNat n n x = x.
Proof.
  unfold substituteNat.
  induction n.
  - (* O *)
    reflexivity.
  - (* S *)
    intros. simpl. apply substituteNat_inner_eq.
Qed.

Theorem substituteNat_neq : forall n' n x, n' <> n -> substituteNat n' n x = term_bvar n'.
Proof.
  intros n' n. induction n', n.
  - (* O, O *)
    contradiction.
  - auto.
  - auto.
  - intros x Contra.
    apply (Nat.succ_inj_wd_neg n' n) in Contra.
    unfold substituteNat. simpl.
    apply substituteNat_inner_neq. assumption.
Qed.

Theorem substituteNat_correct :
  forall n' n x,
    substituteNat_spec n' n x = substituteNat n' n x.
Proof.
  unfold substituteNat_spec.
  intros n' n.
  destruct (Nat.eq_dec n' n).
  - (* = *)
    rewrite e. rewrite (Nat.eqb_refl n). symmetry. apply (substituteNat_eq n).
  - (* <> *)
    pose (n0' := n0).
    apply Nat.eqb_neq in n0'. rewrite n0'.
    symmetry. apply (substituteNat_neq n' n x). assumption.
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

Fixpoint
  substitute_inner
  (f : nat -> nat) (s : term) (n : nat) (x : term) : term :=

  match s with
  | term_bvar n' => substituteNat_inner f n' n x
  | term_fvar a => term_fvar a
  | term_app a b =>
      term_app (substitute_inner f a n x) (substitute_inner f b n x)
  | term_lam a =>
      term_lam (substitute_inner f a (S n) (term_shift x))
  | term_shift a =>
    match n with
    | O => s
    | S k =>
      term_shift
        (substitute_inner (fun x => match f x with O => O | S k => k end) a k x)
    end
  end.
Hint Unfold substitute_inner.

Definition substitute (s : term) (n : nat) (x : term) : term :=
  substitute_inner (fun x => x) s n x.
Hint Unfold substitute.

Theorem substitute_inner_type :
  forall s n f x fs bs A B,
  index n bs B ->
  index (f n) bs B ->
  fs || bs |- x ∈ B ->
  fs || bs |- s ∈ A ->
  fs || bs |- substitute_inner f s n x ∈ A.
Proof.

Theorem substitute_type :
  forall s n x fs bs A B,
  index n bs B ->
  fs || bs |- x ∈ B ->
  fs || bs |- s ∈ A ->
  fs || bs |- substitute s n x ∈ A.
Proof.
  unfold substitute.
  induction s; intros; simpl; inversion H1; subst.
  - (* term_bvar *)
    destruct (Nat.eq_dec n n0).
    + (* = *)
      rewrite e in *.
      rewrite (index_inj H H5) in *.
      rewrite (substituteNat_inner_eq n0 (fun x => x) x).
      assumption.
    + (* <> *)
      apply (substituteNat_inner_neq n n0 (fun x => x) x) in n1.
      rewrite n1.
      assumption.
  - (* term_fvar *)
    constructor. assumption.
  - (* term_app *)
    econstructor.
    eapply IHs1. apply H. assumption. eassumption.
    eapply IHs2. apply H. assumption. assumption.
  - (* term_lam *)
    constructor.
    eapply IHs. apply there. apply H.
    constructor. assumption.
    assumption.
  - (* term_shift *)
    destruct n.
    + (* O *)
      assumption.
    + (* S *)
      inversion H. subst.
      constructor.
      eapply IHs. eassumption.

