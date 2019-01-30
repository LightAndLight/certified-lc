Require Import Coq.Strings.String.

Inductive term : Type :=
| term_bvar : nat -> term
| term_fvar : string -> term
| term_app : term -> term -> term
| term_lam : term -> term
| term_shift : term -> term.
