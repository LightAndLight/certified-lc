Set Implicit Arguments.

Require Extraction.
Extraction Language Haskell.

Inductive ty : Type :=
| tyvar : nat -> ty
| tyarr : ty
| tyapp : ty -> ty -> ty.

Notation "a ==> b" := (tyapp (tyapp tyarr a) b) (at level 51, right associativity).

Inductive index {a : Type} : nat -> list a -> a -> Prop :=
| here : forall {x xs}, index O (x :: xs) x
| there : forall {n x y xs}, index n xs x -> index (S n) (y :: xs) x.

Extraction Implicit index [a].
Extraction Implicit here [x xs].
Extraction Implicit there [n x y xs].

Inductive term : list ty -> ty -> Type :=
| term_var : forall (n : nat) {ctx ty} {ix : index n ctx ty}, term ctx ty
| term_app : forall {ctx a b}, term ctx (a ==> b) -> term ctx a -> term ctx b
| term_lam : forall {ctx a b}, term (a :: ctx) b -> term ctx (a ==> b).

Extraction Implicit term_var [ctx ty ix].
Extraction Implicit term_app [ctx a b].
Extraction Implicit term_lam [ctx a b].

Definition index_nil_impossible : forall {n a} {x : a}, index n nil x -> False.
  intros. inversion H.
Defined.

Fixpoint
  lookup
  {a : Type} {x : a}
  (n : nat) (xs : list a)
  {ix : index n xs x} : a.
  destruct n as [|n'].
  - (* O *)
    destruct xs as [|x' xs'].
    + (* nil *)
      exfalso. apply (@index_nil_impossible 0 a x). apply ix.
    + (* cons *)
      apply x'.
  - (* S *)
    destruct xs as [|x' xs'].
    + (* nil *)
      exfalso. apply (@index_nil_impossible (S n') a x). apply ix.
    + (* cons *)
      apply (lookup a x n' xs').
      inversion ix as [| _a1 _a2 _a3 _a4 H ]. subst.
      apply H.
Defined.

Extraction Implicit lookup [x ix].

Definition index_0_get {a} {x y : a} {xs} (ix : index 0 (x :: xs) y) : x = y.
  inversion ix. subst. auto.
Defined.

Definition index_S_tail {n a} {x y : a} {xs} (ix : index (S n) (x :: xs) y) : index n xs y.
  inversion ix. subst. assumption.
Defined.

Inductive value {ctx} : forall {A}, term ctx A -> Type :=
| value_lam : forall {X Y} {s : term (X :: ctx) (X ==> Y)}, value (term_lam s).

Reserved Notation "x ↓ y" (at level 60, no associativity).
Inductive smallstep {ctx : list ty} : forall {A}, term ctx A -> term ctx A -> Type :=
| step_app :
    forall {X Y} {a : term ctx (X ==> Y)} {a' b},
      a ↓ a' -> term_app a b ↓ term_app a' b
where "x ↓ y" := (smallstep x y).

Unset Extraction SafeImplicits.
Extraction "LC" ty term lookup.