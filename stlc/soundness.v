Require Import syntax.
Require Import judgments.
Require Import Coq.Bool.Bool.

Theorem progress :
  forall e1 t,
  hasType cempty e1 t ->
  (exists e2, step e1 e2) \/
  value e1.
Proof.
  intros e1 t H1.
  remember cempty as c eqn:H in H1.
  induction H1 as [
    c                           (* tUnit *)
  | c x t H1                    (* tVar  *)
  | c x e t1 t2 H1 IH           (* tAbs  *)
  | c e1 e2 t1 t2 H1 IH1 H2 IH2 (* tApp  *)
  ].
  (* tUnit *)
  - right.
    apply valUnit.
  (* tVar *)
  - rewrite H in H1.
    simpl in H1.
    discriminate H1.
  (* tAbs *)
  - right.
    apply valAbs.
  (* tApp *)
  - left.
    elim (IH1 H).
    + intros H3.
      elim H3.
      intros e3 H4.
      exists (eapp e3 e1).
      apply stApp1.
      assumption.
    + intros H3.
      elim (IH2 H).
      * intros H4.
        elim H4.
        intros e3 H5.
        exists (eapp e2 e3).
        apply stApp2; auto.
      * {
        intros H4.
        destruct H3.
        (* eunit *)
        - inversion H1.
        (* eabs x t e *)
        - exists (subst e0 x e1).
          apply stAppAbs.
          assumption.
        }
Qed.

Lemma contextInvariance :
  forall c1 c2 e t1,
  hasType c1 e t1 -> (
    forall x,
    freeVar x e ->
    lookupEvar c1 x = lookupEvar c2 x
  ) ->
  hasType c2 e t1.
Proof.
  intros c1 c2 e t1 H1.
  generalize c2.
  clear c2.
  induction H1 as [
    c1                           (* tUnit *)
  | c1 x1 t1 H1                  (* tVar  *)
  | c1 x1 e1 t1 t2 H1 IH         (* tAbs  *)
  | c1 e1 e2 t1 t2 H1 IH1 H2 IH2 (* tApp  *)
  ].
  (* tUnit *)
  - intros.
    apply tUnit.
  (* tVar *)
  - intros c2 H2.
    apply tVar.
    rewrite <-H1.
    symmetry.
    apply H2.
    apply freeEvar.
    reflexivity.
  (* tAbs *)
  - intros c2 H2.
    apply tAbs.
    apply IH.
    simpl.
    intros x2 H3.
    destruct (eqId idTerm x2 x1) as [ H4 | H4 ].
    (* eqId idTerm x2 x1 = left e *)
    + reflexivity.
    (* eqId idTerm x2 x1 = right n *)
    + apply H2.
      apply freeAbs; assumption.
  (* tApp *)
  - intros c2 H3.
    apply tApp with (t1 := t1).
    (* hastype c2 e2 (tarrow t1 t2) *)
    + apply IH1.
      intros x1 H4.
      apply H3.
      apply freeApp2.
      assumption.
    (* hasType c2 e1 t1 *)
    + apply IH2.
      intros x1 H4.
      apply H3.
      apply freeApp1.
      assumption.
Qed.

Lemma freeVarsAppearInContext :
  forall c e x t1,
  hasType c e t1 ->
  freeVar x e ->
  exists t2,
  lookupEvar c x = Some t2.
Proof.
  intros c1 e1 x1 t1 H1 H2.
  induction H1 as [
    c1                           (* tUnit *)
  | c1 x2 t1 H1                  (* tVar  *)
  | c1 x2 e1 t1 t2 H1 IH         (* tAbs  *)
  | c1 e1 e2 t1 t2 H1 IH1 H3 IH2 (* tApp  *)
  ].
    (* tUnit *)
  - inversion H2.
    (* tVar *)
  - exists t1.
    inversion H2 as [
      x3 H3 H4 (* freeEvar *)
    |          (* freeAbs  *)
    |          (* freeApp1 *)
    |          (* freeApp2 *)
    ].
    congruence.
    (* tAbs *)
  - inversion H2 as [
                        (* freeEvar *)
    | x4 t3 e2 H3 H4 H5 (* freeAbs  *)
    |                   (* freeApp1 *)
    |                   (* freeApp2 *)
    ].
    apply IH in H4.
    destruct H4 as [ t4 ].
    exists t4.
    simpl in H4.
    destruct (eqId idTerm x1 x2) as [ Eq | Neq ].
    (* x1 = x2 *)
    + contradiction.
    (* x1 <> x2 *)
    + assumption.
    (* tApp *)
  - inversion H2 as [
                        (* freeEvar *)
    |                   (* freeAbs  *)
    | e3 e4 H4 H5       (* freeApp1 *)
    | e3 e4 H4 H5       (* freeApp2 *)
    ].
    (* freeApp1 *)
    + apply IH2.
      assumption.
    (* freeApp2 *)
    + apply IH1.
      assumption.
Qed.

Lemma swapVarsInContext :
  forall c1 x1 x2 x3 t1 t2,
  x1 <> x2 ->
  lookupEvar (cextend (cextend c1 x1 t1) x2 t2) x3 =
  lookupEvar (cextend (cextend c1 x2 t2) x1 t1) x3.
Proof.
  intros c1 x1 x2 x3 t1 t2 H1.
  simpl.
  destruct (eqId idTerm x3 x2) as [ Eq1 | Neq1 ].
  (* x3 = x2 *)
  - destruct (eqId idTerm x3 x1) as [ Eq2 | Neq2 ].
    (* x3 = x1 *)
    + rewrite Eq2 in Eq1.
      contradiction.
    (* x3 <> x1 *)
    + reflexivity.
  (* x3 <> x2 *)
  - destruct (eqId idTerm x3 x1); reflexivity.
Qed.

Lemma substPreservesType :
  forall c1 e1 e2 x1 t1 t2,
  hasType (cextend c1 x1 t2) e1 t1 ->
  hasType cempty e2 t2 ->
  hasType c1 (subst e1 x1 e2) t1.
Proof.
  intros c1 e1 e2 x1.
  generalize c1.
  clear c1.
  induction e1 as [
                  (* eunit *)
  | x2            (* evar  *)
  | x2 t3 e1 IH   (* eabs  *)
  | e1 IH1 e3 IH2 (* eapp  *)
  ].
  (* eunit *)
  - simpl.
    intros c1 t1 t2 H1 H2.
    inversion H1.
    apply tUnit.
  (* evar *)
  - intros c1 t1 t2 H1 H2.
    simpl.
    destruct (eqId idTerm x1 x2) eqn:H3.
    (* x1 = x2 *)
    + rewrite e in H1.
      inversion H1 as [
                    (* tUnit *)
      | c2 x3 t3 H4 (* tVar  *)
      |             (* tAbs  *)
      |             (* tApp  *)
      ].
      apply contextInvariance with (c1 := cempty).
      (* hasType cempty e2 t1 *)
      * simpl in H4.
        rewrite e in H3.
        rewrite H3 in H4.
        congruence.
      (* free variables occur in both contexts *)
      * {
        intros x4 H6.
        apply freeVarsAppearInContext with (c := cempty) (t1 := t2) in H6.
        (* lookupEvar cempty x4 = lookupEvar c1 x4 *)
        - destruct H6.
          inversion H6.
        (* hasType cempty e2 t2 *)
        - assumption.
        }
    (* hasType c1 (evar x2) t1 *)
    + apply tVar.
      inversion H1 as [
                             (* tUnit *)
      | c2 x3 t3 H4 H5 H6 H7 (* tVar  *)
      |                      (* tAbs  *)
      |                      (* tApp  *)
      ].
      simpl in H4.
      destruct (eqId idTerm x2 x1) as [ Eq | Neq ].
      (* x1 = x2 *)
      * contradiction n.
        congruence.
      (* x1 <> x2 *)
      * assumption.
  (* eabs *)
  - intros c1 t1 t2 H1 H2.
    simpl.
    inversion H1 as [
                                 (* tUnit *)
    |                            (* tVar  *)
    | c2 x3 e3 t4 t5 H4 H5 H6 H7 (* tAbs  *)
    |                            (* tApp  *)
    ].
    destruct (eqId idTerm x1 x2) eqn:H8.
    (* x1 = x2 *)
    + apply tAbs.
      rewrite e in H4.
      apply contextInvariance with (c1 := cextend (cextend c1 x2 t2) x2 t3).
      * assumption.
      * intros x4 H9.
        simpl.
        destruct (eqId idTerm x4 x2); congruence.
    (* x1 <> x2 *)
    + apply tAbs.
      apply IH with (t2 := t2).
      (* hasType (cextend (cextend c1 x2 t3) x1 t2) e1 t4 *)
      * {
        apply contextInvariance with (c1 := cextend (cextend c1 x1 t2) x2 t3).
        - congruence.
        - intros.
          apply swapVarsInContext.
          assumption.
        }
      (* hasType cempty e2 t2 *)
      * assumption.
  (* eapp *)
  - intros c1 t1 t2 H1 H2.
    simpl.
    inversion H1 as [
                                    (* tUnit *)
    |                               (* tVar  *)
    |                               (* tAbs  *)
    | c2 e4 e5 t3 t4 H4 H5 H6 H7 H8 (* tApp  *)
    ].
    apply tApp with (t1 := t3).
    (* hasType c1 (subst e1 x1 e2) (tarrow t3 t1) *)
    + apply IH1 with (t2 := t2); assumption.
    (* hasType c1 (subst e3 x1 e2) t3 *)
    + apply IH2 with (t2 := t2); assumption.
Qed.

Theorem preservation :
  forall e1 e2 t,
  hasType cempty e1 t ->
  step e1 e2 ->
  hasType cempty e2 t.
Proof.
  intros e1 e2 t H1.
  generalize e2.
  clear e2.
  remember cempty as c eqn:H2 in H1.
  induction H1 as [
                                (* tUnit *)
  | c x t H1                    (* tVar  *)
  | c x e t1 t2 H1 IH           (* tAbs  *)
  | c e1 e3 t1 t2 H1 IH1 H3 IH2 (* tApp  *)
  ].
  (* tUnit *)
  - intros e2 H1.
    inversion H1.
  (* tVar *)
  - intros e2 H3.
    inversion H3.
  (* tAbs *)
  - intros e2 H3.
    inversion H3.
  (* tApp *)
  - intros e2 H4.
    inversion H4 as [
      x e4 e5 t3 H5 H6 H7  (* stAppAbs *)
    | e4 e5 e6 H5 H6 H7    (* stApp1   *)
    | e4 e5 e6 H5 H6 H7 H8 (* stApp2   *)
    ].
    (* stAppAbs *)
    + clear IH1 IH2.
      apply substPreservesType with (t2 := t1).
      (* hasType (cextend cempty x t1) e4 t2 *)
      * rewrite <-H6 in H1.
        inversion H1.
        congruence.
      (* hasType cempty e1 t1 *)
      * congruence.
    (* stApp1 *)
    + set (H8 := IH1 H2 e5 H5).
      rewrite H2 in H3.
      set (H9 := tApp cempty e1 e5 t1 t2 H8 H3).
      assumption.
    (* stApp2 *)
    + set (H9 := IH2 H2 e6 H6).
      rewrite H2 in H1.
      set (H10 := tApp cempty e6 e3 t1 t2 H1 H9).
      assumption.
Qed.

(* Optional: determinism *)