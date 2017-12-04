Require Import Coq.Strings.String.

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
  Parameter f_obj : C.object -> D.object.
  Parameter f_morph :
    forall { a b },
    C.morphism a b -> D.morphism (f_obj a) (f_obj b).

  (**
   * Functors preserve identity morphisms.
   *)
  Axiom ident :
    forall a,
    exists (f : (C.morphism a a)) (g : D.morphism (f_obj a) (f_obj a)),
    f_morph f = g.

  (**
   * Functors preserve composition.
   *)
  Axiom composition :
    forall a b c
      (f : C.morphism a c)
      (g : C.morphism b c)
      (h : C.morphism a b),
    f = C.compose g h ->
    f_morph f = D.compose (f_morph g) (f_morph h).
End Functor.

(***************************)
(* Natural Transformations *)
(***************************)

Module Type Natural_Transformation (C D : Category) (F G : Functor C D).
  Parameter eta : forall { a b }, C.object -> D.morphism a b.

  Axiom commute :
    forall a b (f : C.morphism a b),
    D.compose (eta b) (F.f_morph f) =
    D.compose (G.f_morph f) (eta a).
End Natural_Transformation.