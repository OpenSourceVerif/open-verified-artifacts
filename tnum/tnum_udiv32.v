From compcert Require Import Coqlib Integers Values.
From bpf.tnum Require Import tnumZ tnumZ_inv tnumZ_udiv tnum32.

(** https://www.kernel.org/doc/Documentation/bpf/standardization/instruction-set.rst
  BPF Instruction Set Architecture (ISA) - Arithmetic instructions
    - DIV: dst = (src != 0) ? (dst / src) : 0
  *)
Definition bpf_div_u32 (n1 n2:int) : int :=
  if (Int.eq n2 Int.zero)
  then Int.zero
  else Int.divu n1 n2.

Definition Int_size (x: int) : Z :=
  Z_size_Z (Int.unsigned x).

Definition Int_ones (n: Z) : int :=
  Int.repr (Z.ones n).

Definition tnum_udiv_32 (a b: tnum) : tnum :=
  if (Int.eq (fst b) Int.zero) && (Int.eq (snd b) Int.zero) then
    (Int.zero, Int.zero) (* BPF div specification: x / 0 = 0 *)
  else if (Int.eq (snd a) Int.zero) && (Int.eq (snd b) Int.zero) then
    (Int.divu (fst a) (fst b), Int.zero) (* concrete udiv *)
  else if (Int.eq (fst b) Int.zero) then
    (Int.zero, Int.mone) (* -1 represents unsigned_max *)
  else let max_res := Int.divu (Int.add (fst a) (snd a)) (fst b) in
    (Int.zero, Int_ones (Int_size max_res)).

Lemma testbit_divu : forall i x y,
    0 <= i < Int.zwordsize ->
    Int.testbit (Int.divu x y) i =
      Z.testbit (Z.div (Int.unsigned x) (Int.unsigned y)) i.
Proof.
  intros. unfold Int.divu.
  rewrite Int.testbit_repr by auto.
  reflexivity.
Qed.

Lemma tnum_udiv_eq : forall (a b : tnum),
    Int.unsigned (fst a) + Int.unsigned (snd a) <= Int.max_unsigned ->
    tnum_udiv_32 a b =
      of_tnumZ (tnumZ_udiv.tnum_udiv (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros. unfold tnum_udiv_32, tnumZ_udiv.tnum_udiv. simpl.
  rewrite !Int_eq_unsigned. rewrite Int.unsigned_zero.
  destruct ((Int.unsigned (fst b) =? 0) && (Int.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct ((Int.unsigned (snd a) =? 0) && (Int.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct (Int.unsigned (fst b) =? 0) eqn:Hb_v0.
  { reflexivity. }
  unfold of_tnumZ. f_equal. simpl.
  unfold Int_ones, Int_size, Int.divu.
  rewrite Int_unsigned_add; try lia.
  rewrite Int.unsigned_repr. reflexivity.
  pose proof (Int.unsigned_range (fst b)).
  pose proof (Int_unsigned_add_nonneg (fst a) (snd a)).
  split.
  - apply Z_div_nonneg_nonneg; lia.
  - apply Z.le_trans with (m := Int.unsigned (fst a) + Int.unsigned (snd a)).
    2:{ apply H. }
    rewrite <- Z.div_1_r.
    apply Z.div_le_compat_l; lia.
Qed.

Theorem tnum_binary_sound_ge_0 :
  forall a b i j f fz tnum_f tnum_fz
         (TNUM_FZ_SOUND : forall a i b j,
            tnum_ge_inv a -> tnum_ge_inv b ->
              gamma a i -> gamma b j -> gamma (tnum_fz a b) (fz i j))
         (FFZ : forall n, 0 <= n < Int.zwordsize ->
            forall i j, (Int.testbit (f i j) n =
              Z.testbit (fz (Int.unsigned i) (Int.unsigned j)) n))
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b) = true.
Proof.
  intros.
  apply mem_tnum_gamma in MEMA.
  apply mem_tnum_gamma in MEMB.
  rewrite EQ.
  specialize (TNUM_FZ_SOUND _ _ _ _ GEA GEB MEMA MEMB).
  revert TNUM_FZ_SOUND.
  unfold to_tnumZ.
  generalize (Int.unsigned (fst a), Int.unsigned (snd a)) as az.
  generalize (Int.unsigned (fst b), Int.unsigned (snd b)) as bz.
  intros bz az.
  generalize (tnum_fz az bz) as r.
  destruct r.
  unfold gamma. simpl in *. intros. subst.
  unfold mem_tnum.
  simpl.
  apply int_eq_if_same.
  apply Int.same_bits_eq.
  intros.
  rewrite Int.testbit_repr by auto.
  rewrite Int.bits_and by auto.
  rewrite Z.land_spec.
  rewrite Z.lnot_spec by lia.
  rewrite Int.bits_not by auto.
  rewrite! Int.testbit_repr by auto.
  rewrite FFZ. reflexivity.
  auto.
Qed.

Theorem tnum_udiv_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true),
    mem_tnum (bpf_div_u32 i j) (tnum_udiv_32 a b) = true.
Proof.
  intros.
  unfold bpf_div_u32.
  destruct (Int.eq j Int.zero) eqn:EQ.
  - assert (Int.eq (fst b) Int.zero = true).
    { unfold mem_tnum in MEMB.
      apply Int.same_if_eq in EQ.
      rewrite EQ in MEMB.
      rewrite Int.and_zero_l in MEMB.
      rewrite Int.eq_sym. apply MEMB. }
    unfold tnum_udiv_32. rewrite H. rewrite andb_true_l.
    destruct (Int.eq (snd b) Int.zero).
    { reflexivity. }
    rewrite andb_false_r. reflexivity.
  - apply tnum_binary_sound_ge_0
      with (tnum_fz := tnumZ_udiv.tnum_udiv) (fz:= Z.div); auto.
    + intros. apply tnumZ_udiv.tnum_udiv_sound; auto.
    + intros. apply testbit_divu ; auto.
    + apply tnum_udiv_eq; auto. apply (mem_tnum_range _ _ MEMA).
Qed.