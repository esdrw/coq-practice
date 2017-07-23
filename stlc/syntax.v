Require Import Coq.Strings.String.

Inductive idType : Type := 
| idTerm : idType. (* Term id *)

Inductive id : idType -> Type :=
| makeId : forall (idT : idType), string -> id idT.

Definition termId := id idTerm.

Inductive type : Type :=
| tunit : type
| tarrow : type -> type -> type.

Inductive term : Type :=
| eunit : term
| evar : termId -> term
| eabs : termId -> type -> term -> term
| eapp : term -> term -> term.

Inductive context : Type :=
| cempty : context
| cextend : context -> termId -> type -> context.