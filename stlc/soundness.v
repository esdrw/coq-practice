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
    c                           |
    c x t H1                    |
    c x e t1 t2 H1 IH           |
    c e1 e2 t1 t2 H1 IH1 H2 IH2
  ].
  - right.
    apply valUnit.
  - rewrite H in H1.
    simpl in H1.
    discriminate H1.
  - right.
    apply valAbs.
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
        - inversion H1.
        - exists (subst e0 x e1).
          apply stAppAbs.
          assumption.
        }
Qed.

Lemma contextInvariance :
  forall c1 c2 e t1,
  hasType c1 e t1 -> (
    forall x,
    varIsFreeInTerm x e = true ->
    lookupEvar c1 x = lookupEvar c2 x
  ) ->
  hasType c2 e t1.
Proof.
  intros c1 c2 e t1 H1.
  generalize c2.
  clear c2.
  induction H1 as [
    c1                            |
    c1 x1 t1 H1                   |
    c1 x1 e1 t1 t2 H1 IH          |
    c1 e1 e2 t1 t2 H1 IH1 H2 IH2
  ].
  - intros.
    apply tUnit.
  - intros c2 H2.
    apply tVar.
    rewrite <-H1.
    symmetry.
    apply H2.
    simpl.
    destruct (eqId idTerm x1 x1); congruence.
  - intros c2 H2.
    apply tAbs.
    apply IH.
    simpl.
    intros x2 H3.
    destruct (eqId idTerm x2 x1) eqn:H4.
    + congruence.
    + apply H2.
      simpl.
      rewrite H4.
      congruence.
  - intros c2 H3.
    apply tApp with (t1 := t1).
    + apply IH1.
      intros x1 H4.
      apply H3.
      simpl.
      apply orb_true_iff.
      left.
      assumption.
    + apply IH2.
      intros x1 H4.
      apply H3.
      simpl.
      apply orb_true_iff.
      right.
      assumption.
Qed.

Lemma freeVarsAppearInContext :
  forall c e x t1,
  hasType c e t1 ->
  varIsFreeInTerm x e = true ->
  exists t2,
  lookupEvar c x = Some t2.
Proof.
  intros c1 e1 x1.
  generalize c1.
  clear c1.
  induction e1 as [
                 |
    x2           |
    x2 t2 e1 IH  |
    e1 IH1 e2 IH2
  ].
  - intros c1 t1 H1 H2.
    inversion H2.
  - intros c1 t1 H1 H2.
    inversion H1 as [
                            |
      c2 x3 t2 H3 H4 H5 H6  |
                            |

    ].
    simpl in H2.
    destruct (eqId idTerm x1 x2).
    + exists t1.
      congruence.
    + inversion H2.
  - intros c1 t1 H1 H2.
    inversion H1 as [
                                  |
                                  |
      c2 x3 e2 t3 t4 H3 H4 H5 H6  |
    ].
    set (H7 := IH (cextend c1 x2 t2) t3 H3).
    simpl in H2.
    destruct (eqId idTerm x1 x2) eqn:H8.
    + inversion H2.
    + apply H7 in H2.
      destruct H2 as [ t5 ].
      simpl in H2.
      rewrite H8 in H2.
      exists t5.
      assumption.
  - intros c1 t1 H1 H2.
    simpl in H2.
    inversion H1 as [
                                    |
                                    |
                                    |
      c2 e3 e4 t2 t3 H3 H4 H5 H6 H7
    ].
    apply orb_true_iff in H2.
    destruct H2.
    + apply IH1 with (t1 := (tarrow t2 t1)); assumption.
    + apply IH2 with (t1 := t2); assumption.
Qed.

Lemma swapVarsInContext :
  forall c1 x1 x2 x3 t1 t2,
  x1 <> x2 ->
  lookupEvar (cextend (cextend c1 x1 t1) x2 t2) x3 =
  lookupEvar (cextend (cextend c1 x2 t2) x1 t1) x3.
Proof.
  intros c1 x1 x2 x3 t1 t2 H1.
  simpl.
  destruct (eqId idTerm x3 x2).
  - destruct (eqId idTerm x3 x1).
    + rewrite e0 in e.
      contradiction.
    + reflexivity.
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
                      |
    x2                |
    x2 t3 e1 IH       |
    e1 IH1 e3 IH2
  ].
  - simpl.
    intros c1 t1 t2 H1 H2.
    inversion H1.
    apply tUnit.
  - intros c1 t1 t2 H1 H2.
    simpl.
    destruct (eqId idTerm x1 x2) eqn:H3.
    + rewrite e in H1.
      inversion H1.
      apply contextInvariance with (c1 := cempty).
      * simpl in H4.
        rewrite e in H3.
        rewrite H3 in H4.
        congruence.
      * {
        intros x3 H6.
        apply freeVarsAppearInContext with (c := cempty) (t1 := t2) in H6.
        - destruct H6.
          inversion H6.
        - assumption.
        }
    + apply tVar.
      inversion H1.
      simpl in H4.
      destruct (eqId idTerm x2 x1).
      * contradiction n.
        congruence.
      * assumption.
  - intros c1 t1 t2 H1 H2.
    simpl.
    inversion H1 as [
                                 |
                                 |
      c2 x3 e3 t4 t5 H4 H5 H6 H7 |

    ].
    destruct (eqId idTerm x1 x2) eqn:H8.
    + apply tAbs.
      rewrite e in H4.
      apply contextInvariance with (c1 := cextend (cextend c1 x2 t2) x2 t3).
      * assumption.
      * intros x4 H9.
        simpl.
        destruct (eqId idTerm x4 x2); congruence.
    + apply tAbs.
      apply IH with (t2 := t2).
      * {
        apply contextInvariance with (c1 := cextend (cextend c1 x1 t2) x2 t3).
        - congruence.
        - intros.
          apply swapVarsInContext.
          assumption.
        }
      * simpl.
        assumption.
  - intros c1 t1 t2 H1 H2.
    simpl.
    inversion H1 as [
                                    |
                                    |
                                    |
      c2 e4 e5 t3 t4 H4 H5 H6 H7 H8
    ].
    apply tApp with (t1 := t3).
    + apply IH1 with (t2 := t2); assumption.
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
                                |
    c x t H1                    |
    c x e t1 t2 H1 IH           |
    c e1 e3 t1 t2 H1 IH1 H3 IH2
  ].
  - intros e2 H.
    inversion H.
  - intros e2 H.
    inversion H.
  - intros e2 H.
    inversion H.
  - intros e2 H4.
    inversion H4 as [
      x e4 e5 t3 H5 H6 H7  |
      e4 e5 e6 H5 H6 H7    |
      e4 e5 e6 H5 H6 H7 H8
    ].
    + clear IH1 IH2.
      apply substPreservesType with (t2 := t1).
      * rewrite <-H6 in H1.
        inversion H1.
        congruence.
      * congruence.
    + set (H8 := IH1 H2 e5 H5).
      rewrite H2 in H3.
      set (H9 := tApp cempty e1 e5 t1 t2 H8 H3).
      assumption.
    + set (H9 := IH2 H2 e6 H6).
      rewrite H2 in H1.
      set (H10 := tApp cempty e6 e3 t1 t2 H1 H9).
      assumption.
Qed.

(* Optional: determinism *)