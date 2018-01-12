Require Import Coq.Strings.String.
Require Import Coq.Program.Basics.

(**************)
(* Categories *)
(**************)

Module Type Category.
  Parameter object : Set.
  Parameter morphism : object -> object -> Set.

  (**
   * Composition takes two morphisms f : b -> c and g : a -> b. It
   * returns a morphism from a -> c.
   * f o g can also be thought of as f after g, following the g morphism
   * and then the f morphism.
   *)
  Parameter compose :
    forall { a b c },
    morphism b c ->
    morphism a b ->
    morphism a c.

  (**
   * Composition must be associative.
   *)
  Axiom assoc :
    forall a b c d
    (f : morphism c d)
    (g : morphism b c)
    (h : morphism a b),
    compose f (compose g h) =
    compose (compose f g) h.

  (**
   * Every object must have an identity morphism.
   *)
  Axiom ident :
    forall a,
    exists (f : morphism a a),
    forall b (g : morphism a b) (h : morphism b a),
    compose g f = g /\
    compose f h = h.
End Category.

(************)
(* Functors *)
(************)

Module Type Functor (C D : Category).
  Parameter obj : C.object -> D.object.
  Parameter morph :
    forall { a b },
    C.morphism a b -> D.morphism (obj a) (obj b).

  (**
   * Functors preserve identity morphisms.
   *)
  Axiom ident :
    forall a,
    exists (f : (C.morphism a a)) (g : D.morphism (obj a) (obj a)),
    morph f = g.

  (**
   * Functors preserve composition.
   *)
  Axiom composition :
    forall a b c
      (f : C.morphism b a)
      (g : C.morphism c b),
    morph (C.compose f g) = D.compose (morph f) (morph g).
End Functor.

(* The identity functor is a functor. *)
Module IdentityFunctor (C : Category) : Functor C C.
  Definition obj (a : C.object) := a.
  Definition morph { a b } (f : C.morphism a b) := f.

  Lemma ident :
    forall a,
    exists (f : (C.morphism a a)) (g : C.morphism (obj a) (obj a)),
    morph f = g.
  Proof.
    intros.
    set (H := C.ident a).
    elim H. intros.
    exists x.
    eauto.
  Qed.

  Lemma composition :
    forall a b c
      (f : C.morphism b a)
      (g : C.morphism c b),
    morph (C.compose f g) = C.compose (morph f) (morph g).
  Proof.
    auto.
  Qed.
End IdentityFunctor.

(* The composition of two functors is a functor. *)
Module ComposedFunctors
  (B C D : Category)
  (F : Functor C D)
  (G : Functor B C) : Functor B D.
  Definition obj := compose F.obj G.obj.
  Definition morph {a : B.object} {b : B.object}
    := compose F.morph (@G.morph a b).

  Lemma ident :
    forall a,
    exists (f : (B.morphism a a)) (g : D.morphism (obj a) (obj a)),
    morph f = g.
  Proof.
    intros.
    set (H := G.ident a).
    elim H. intros.
    exists x.
    eauto.
  Qed.

  Lemma composition :
    forall a b c
      (f : B.morphism b a)
      (g : B.morphism c b),
    morph (B.compose f g) = D.compose (morph f) (morph g).
  Proof.
    intros.
    unfold morph, compose.
    replace (G.morph (B.compose f g)) with
      (C.compose (G.morph f) (G.morph g)).
    - refine (F.composition _ _ _ _ _).
    - symmetry.
      refine (G.composition _ _ _ _ _).
  Qed.
End ComposedFunctors.

(***************************)
(* Natural Transformations *)
(***************************)

Module Type NaturalTransformation (C D : Category) (F G : Functor C D).
  Parameter eta : forall { a b }, C.object -> D.morphism a b.

  Axiom commute :
    forall a b (f : C.morphism a b),
    D.compose (eta b) (F.morph f) =
    D.compose (G.morph f) (eta a).
End NaturalTransformation.
