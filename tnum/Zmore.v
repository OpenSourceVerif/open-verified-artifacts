From Coq Require Import ZArith Bool Lia Btauto.
Open Scope Z_scope.

Lemma Zland_ub : forall x y,
    0 <= x ->
    0 <= y ->
    Z.land x y <= x.
Proof.
  intros.
  destruct x; destruct y;  try lia.
  - simpl. lia.
  - rewrite Z.land_0_l. lia.
  - rewrite Z.land_0_r. lia.
  - simpl. clear.  revert p0.
    induction p; destruct p0;
      try specialize (IHp p0); simpl; try lia.
Qed.
  
Lemma add_lor_excl : forall x y,
  Z.land x y = 0%Z ->
  (x + y)%Z = Z.lor x y.
Proof.
  intros.
  rewrite <- Z.add_lor_land.
  rewrite H.
  ring.
Qed.

Lemma lor_land_not : forall x y, Z.lor (Z.land x (Z.lnot y)) y = Z.lor x y.
Proof.
  intros.
  rewrite Z.lor_land_distr_l.
  rewrite (Z.lor_comm (Z.lnot _)).
  rewrite Z.lor_lnot_diag.
  rewrite Z.land_m1_r.
  reflexivity.
Qed.

Lemma Z_lor_recompose : forall x y,
  x = Z.lor (Z.land x (Z.lnot y)) (Z.land x y).
Proof.
  intros.
  rewrite <- Z.land_lor_distr_r.
  rewrite Z.lor_comm.
  rewrite Z.lor_lnot_diag.
  symmetry; apply Z.land_m1_r.
Qed.

Lemma Z_land_disjoint : forall x y,
  Z.land (Z.land x (Z.lnot y)) (Z.land x y) = 0.
Proof.
  intros.
  rewrite (Z.land_comm x y).
  rewrite (Z.land_assoc (Z.land x (Z.lnot y)) y x).
  rewrite <- (Z.land_assoc x (Z.lnot y) y).
  rewrite (Z.land_comm (Z.lnot y) y).
  rewrite Z.land_lnot_diag.
  rewrite Z.land_0_r; apply Z.land_0_l.
Qed.

Lemma Z_ldiff_ones n x : 
  0 <= n -> Z.ldiff x (Z.ones n) = 0 <-> (0 <= x <= Z.ones n).
Proof.
  intros. split.
  - apply Z.ldiff_le; rewrite Z.ones_equiv.
    apply Z.lt_le_pred, Z.pow_pos_nonneg. lia. apply H.
  - intros; destruct H0. destruct (Z.eqb_spec x 0).
    + rewrite e. reflexivity.
    + apply Z.ldiff_ones_r_low. lia.
      rewrite Z.ones_equiv in H1; apply Z.lt_le_pred in H1.
      apply Z.log2_lt_pow2. lia. apply H1.
Qed.

Lemma pos_land_le: forall p p0,
  Z.of_N (Pos.land p p0) <= Z.pos p.
Proof.
  induction p; simpl; intros; try lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
Qed.

Lemma pos_pred_n_diff_le: forall p p0,
    Z.of_N (Pos.ldiff p p0) <= Z.pos p.
Proof.
  induction p; simpl; intros; try lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
    + specialize (IHp p0). lia.
    + specialize (IHp p0). lia.
  - destruct p0; try lia.
Qed.

Lemma Z_land_leb: forall i j,
  0 <= i ->
  Z.land i j <= i.
Proof.
  unfold Z.land.
  destruct i; simpl; intros; try lia.
  destruct j; try lia.
  - apply pos_land_le.
  - destruct (Pos.pred_N p0) eqn: Hp0; try lia.
    apply pos_pred_n_diff_le.
Qed.
