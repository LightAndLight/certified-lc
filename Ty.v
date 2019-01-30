Require Import Coq.Strings.String.

Inductive type : Type :=
| type_var : string -> type
| type_app : type -> type -> type
| type_arr : type.

Notation "a --> b" :=
  (type_app (type_app type_arr a) b) (at level 60, right associativity).
