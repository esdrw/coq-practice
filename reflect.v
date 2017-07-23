Require Import Coq.Lists.List.
Import ListNotations.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H.
  destruct b.
  - apply ReflectT.
    rewrite H.
    reflexivity.
  - apply ReflectF.
    rewrite H.
    intros H'.
    inversion H'.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S x) => isEven x
  end.

Lemma strongInduction :
  forall P : nat -> Prop, (
    forall m : nat,
    (forall n : nat, n < m -> P n) ->
    P m
  ) ->
  forall n : nat, P n.
Proof.
  intros P H1 n1.
  apply H1.
  induction n1 as [| n1 H2].
  - intros n1 H2.
    inversion H2.
  - intros n2 H3.
    inversion H3 as [H4| n3 H4 H5].
    + set (H5 := H1 n1).
      apply H5.
      auto.
    + assert (n2 < n1) as H6.
      * auto.
      * apply H2.
        auto.
Qed.

Lemma evenHelper :
  forall P : nat -> Prop,
  P 0 ->
  (
    forall n : nat,
    P (S n) /\
    P (S (S n))
  ) ->
  forall n : nat, P n.
Proof.
  intros P P0 H1 n1.
  induction n1 as [| n1 IH].
  - assumption.
  - apply H1.
Qed.

(* Proved with strongInduction lemma *)
Lemma isEvenImpliesEven : forall n : nat, isEven n = true -> ev n.
Proof.
  refine (evenHelper _ _ _).
  - intros H1.
    apply ev_0.
  - intros n1.
    induction n1 as [| n1 IH].
    + split.
      * intros H1.
        discriminate.
      * intros H1.
        apply ev_SS.
        apply ev_0.
    + split.
      * apply IH.
      * intros H1.
        apply ev_SS.
        apply IH.
        apply H1.
Qed.

Lemma evenImpliesIsEven : forall n : nat, ev n -> isEven n = true.
Proof.
  intros n1 H1.
  induction H1 as [| n1 H1 IH].
  - simpl.
    reflexivity.
  - simpl.
    congruence.
Qed.

Lemma evenIffIsEven : forall n : nat, ev n <-> isEven n = true.
Proof.
  split.
  - apply evenImpliesIsEven.
  - apply isEvenImpliesEven.
Qed.

Theorem reflectIsEven : forall n, reflect (ev n) (isEven n).
Proof.
  intros n.
  destruct n.
  - apply (ReflectT (ev 0) ev_0).
  - case isEven eqn:H1.
    + apply ReflectT.
      apply evenIffIsEven.
      auto.
    + apply ReflectF.
      unfold not.
      intros H2.
      apply evenIffIsEven in H2.
      rewrite H1 in H2.
      inversion H2.
Qed.