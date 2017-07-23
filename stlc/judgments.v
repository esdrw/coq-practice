Require Import Coq.Strings.String.
Require Import syntax.

(* Helpers *)
Section helpers.

Theorem eqId :
  forall (idT : idType) (x1 : id idT) (x2 : id idT),
  {x1 = x2} + {x1 <> x2}.
Proof.
  intros T x1 x2.
  destruct x1 as [H1 s1].
  destruct x2 as [H1 s2].
  pose (H2 := string_dec s1 s2).
  case H2.
  - intros H3.
    apply left.
    congruence.
  - intros H3.
    apply right.
    congruence.
Qed.

(* Look up variables in the context *)
Fixpoint lookupEvar (c1 : context) (x1 : termId) :=
  match c1 with
  | cempty => None
  | cextend c2 x2 t =>
    match eqId idTerm x1 x2 with
    | left _ => Some t
    | right _ => lookupEvar c2 x1
    end
  end.

Fixpoint varIsFreeInTerm (x1 : termId) (e1 : term) :=
  match e1 with
  | eunit => false
  | evar x2 =>
    match eqId idTerm x1 x2 with
    | left _ => true
    | right _ => false
    end
  | eabs x2 t e2 =>
    match eqId idTerm x1 x2 with
    | left _ => false
    | right _ => varIsFreeInTerm x1 e2
    end
  | eapp e2 e3 => orb (varIsFreeInTerm x1 e2) (varIsFreeInTerm x1 e3)
  end.

Fixpoint subst (e1 : term) (x1 : termId) (e2 : term) :=
  match e1 with
  | eunit => e1
  | evar x2 =>
    match eqId idTerm x1 x2 with
    | left _ => e2
    | right _ => e1
    end
  | eabs x2 t e3 =>
    match eqId idTerm x1 x2 with
    | left _ => e1
    | right _ => eabs x2 t (subst e3 x1 e2)
    end
  | eapp e3 e4 => eapp (subst e3 x1 e2) (subst e4 x1 e2)
  end.
End helpers.

(* Typing rules *)
Inductive hasType : context -> term -> type -> Prop :=
| tUnit :
    forall c,
    hasType c eunit tunit
| tVar :
    forall c x t,
    lookupEvar c x = Some t ->
    hasType c (evar x) t
| tAbs :
    forall c x e1 t1 t2,
    hasType (cextend c x t2) e1 t1 ->
    hasType c (eabs x t2 e1) (tarrow t2 t1)
| tApp :
    forall c e1 e2 t1 t2,
    hasType c e2 (tarrow t1 t2) ->
    hasType c e1 t1 ->
    hasType c (eapp e2 e1) t2.

(* Operational semantics *)
Inductive value : term -> Prop :=
| valUnit : value eunit
| valAbs : forall x e1 t1, value (eabs x t1 e1).

Inductive step : term -> term -> Prop :=
| stAppAbs :
    forall x e1 e2 t1,
    value e2 ->
    step (eapp (eabs x t1 e1) e2) (subst e1 x e2)
| stApp1 :
    forall e1 e2 e3,
    step e1 e2 ->
    step (eapp e1 e3) (eapp e2 e3)
| stApp2 :
    forall e1 e2 e3,
    value e1 ->
    step e2 e3 ->
    step (eapp e1 e2) (eapp e1 e3).