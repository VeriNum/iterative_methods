From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.
From mathcomp Require Import all_ssreflect ssralg ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.

From vcfloat Require Import FPStdLib.

Require Import fma_floating_point_model inf_norm_properties.

Require Import common fma_dot_acc float_acc_lems dotprod_model.


Set Bullet Behavior "Strict Subproofs". 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas fma_is_finite finite_lemmas_additional.
Require Import Coq.ZArith.BinInt.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section WITHNANS.
Context {NANS: Nans}. 



Notation "A +f B" := (addmx_float A B) (at level 80).
Notation "-f A" := (opp_mat A) (at level 50).
Notation "A *f B" := (mulmx_float A B) (at level 70).
Notation "A -f B" := (sub_mat A B) (at level 80).


Definition F' (t: type) := 
    (fmax t * (1 -  2 * default_rel t))%Re.

Lemma F_p_ge_0 {ty}:
  (0 <= F' ty)%Re.
Proof.
unfold F'.
apply Rmult_le_pos.
+ unfold fmax. apply bpow_ge_0.
+  apply Rge_le. apply Rge_minus. apply Rle_ge.
   unfold default_rel.
   assert ((2 * (/ 2 * bpow Zaux.radix2 (- fprec ty + 1)))%Re = 
            bpow Zaux.radix2 (- fprec ty + 1)).
   { nra. } rewrite H.
   assert ((- fprec ty + 1)%Z = (- (fprec ty - 1))%Z).
   {  rewrite Z.opp_add_distr Z.opp_involutive. reflexivity. }
   rewrite H0 bpow_opp.
   replace 1%Re with (/1)%Re by nra.
   apply Rlt_le. apply Rinv_lt_contravar.
   - apply Rmult_lt_0_compat. nra. 
     apply bpow_gt_0.
   - assert (1%Re = bpow Zaux.radix2 0).
     { by unfold bpow. } rewrite H1.
     apply bpow_lt. apply Z.lt_0_sub, fprec_gt_one.
Qed.


Lemma finite_bminus {ty} {n:nat} (v1 v2 : 'cV[ftype ty]_n.+1) i:
  let xy := (v1 (inord i) ord0, v2 (inord i) ord0) in 
  In xy
      (combine 
         (vec_to_list_float n.+1 v1)
         (vec_to_list_float n.+1 v2)) ->
   (finite xy.1 /\finite xy.2 /\ 
    (Rabs (FT2R (fst (xy))) <= (F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))%Re /\
     (Rabs (FT2R (snd (xy))) <= (F' ty /2) / (INR n.+1 * (1 + default_rel ty)^n.+1))%Re) ->
  finite (BPLUS (v1 (inord i) 0) (BOPP (v2 (inord i) 0))).
Proof.
intros ? Hin Hfin.
apply Bplus_no_ov_finite .
  - apply Hfin.
  - rewrite finite_BOPP. apply Hfin.
  - unfold Bplus_no_overflow. 
    pose proof (generic_round_property ty (FT2R (v1 (inord i) 0) +  FT2R (BOPP  (v2 (inord i) 0)))).
    destruct H as [d [e [Hpr [Hdf [Hde H]]]]].
    rewrite H.
    destruct Hfin as [Hf1 [Hf2 [Ha1 Ha2]]].
    apply Rle_lt_trans with 
    (Rabs ((FT2R (v1 (inord i) ord0) +
              FT2R (BOPP (v2 (inord i) ord0))) *  (1 + d)) + 
    (Rabs e))%Re.
    * apply Rabs_triang.
    * rewrite Rabs_mult.
      eapply Rle_lt_trans.
      ++ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
          apply Rabs_pos. apply Rabs_triang.
      ++ apply Rle_lt_trans with 
         ((2 * ((F' ty/2) / (INR n.+1 * (1 + default_rel ty) ^ n.+1))) *
          (1 + default_rel ty) + default_abs ty)%Re.
         -- apply Rplus_le_compat.
            ** apply Rmult_le_compat.
               +++ apply Rplus_le_le_0_compat; apply Rabs_pos.
               +++ apply Rabs_pos.
               +++ rewrite RIneq.double. apply Rplus_le_compat. 
                   --- apply Ha1.
                   --- unfold FT2R in *. rewrite B2R_Bopp. rewrite Rabs_Ropp.
                       apply Ha2.
               +++ apply Rle_trans with (Rabs 1 + Rabs d)%Re.
                   apply Rabs_triang. rewrite Rabs_R1. by apply Rplus_le_compat_l.
            ** apply Hde.
         --  assert ((F' ty + default_abs ty < bpow Zaux.radix2 (femax ty))%Re)%Re.
             { unfold F'. unfold fmax.
               assert ((bpow Zaux.radix2 (femax ty) *
                          (1 - 2 * default_rel ty) + default_abs ty)%Re = 
                        (bpow Zaux.radix2 (femax ty) - 
                          (2 * bpow Zaux.radix2 (femax ty) * default_rel ty - default_abs ty))%Re).
               { nra. } rewrite H0.
               assert (forall x y:R, (0 < y)%Re -> (x - y < x)%Re).
               { intros. nra. } apply H1.
               apply Rgt_lt. apply Rgt_minus. apply Rlt_gt.
               unfold default_abs, default_rel.
               assert ((2 * bpow Zaux.radix2 (femax ty) *
                          (/ 2 * bpow Zaux.radix2 (- fprec ty + 1)))%Re = 
                       (1 * (bpow Zaux.radix2 (femax ty) * bpow Zaux.radix2 (- fprec ty + 1)))%Re).
               { nra. } rewrite H2. clear H2.
               apply Rmult_lt_compat. nra. apply bpow_ge_0. nra.
               rewrite Z.add_comm. rewrite Rmult_comm.
               rewrite -bpow_plus. apply bpow_lt. rewrite Z.add_shuffle0.
               apply Z.add_lt_mono_r.
               apply Z.lt_sub_lt_add. simpl.
               unfold Z.sub. rewrite Z.opp_involutive. 
               assert (2%Z = (1+1)%Z). { by simpl. }
               rewrite H2.  
               apply Z.add_lt_mono;
               apply Z.lt_trans with (fprec ty); try apply fprec_gt_one;
               try apply fprec_lt_femax.
             } apply Rle_lt_trans with (F' ty + default_abs ty)%Re.
             ** apply Rplus_le_compat_r.
                assert ((2 *
                           (F' ty / 2 /
                            (INR n.+1 * (1 + default_rel ty) ^ n.+1)) *
                           (1 + default_rel ty))%Re = 
                        ((F' ty * / (INR n.+1 * (1 + default_rel ty) ^ n.+1)) * (1 + default_rel ty))%Re).
                { nra. } rewrite H1. clear H1.
                rewrite Rinv_mult_distr.
                +++ replace (F' ty) with (F' ty * 1)%Re by nra.
                    assert (((F' ty * 1) *
                               (/ INR n.+1 * / (1 + default_rel ty) ^ n.+1) *
                               (1 + default_rel ty))%Re = 
                             ((F' ty * / INR n.+1) * (/ (1 + default_rel ty) ^ n.+1 * (1 + default_rel ty)))%Re).
                    { nra. } rewrite H1. clear H1.
                    apply Rmult_le_compat.
                    --- apply Rmult_le_pos.  apply F_p_ge_0.
                        apply Rlt_le. apply Rinv_0_lt_compat. apply lt_0_INR.
                        lia.
                    --- apply Rmult_le_pos. apply Rlt_le. apply Rinv_0_lt_compat.
                        apply pow_lt. apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
                        apply Rlt_le. apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
                    --- replace (F' ty) with (F' ty * 1)%Re by nra.
                        replace (F' ty * 1 * / INR n.+1)%Re with (F' ty * / INR n.+1)%Re by nra.
                        apply Rmult_le_compat_l. 
                        *** apply F_p_ge_0.
                        *** replace 1%Re with (/1)%Re by nra.
                            assert ((0 <= n)%nat ). { by []. }
                            rewrite leq_eqVlt in H1.
                            assert ((0%nat == n) \/ (0 < n)%nat).
                            { by apply /orP. } destruct H2.
                            ++++ rewrite eq_sym in H2. 
                                 assert (n = 0%nat). { by apply /eqP. }
                                 rewrite H3. simpl;nra. 
                            ++++ apply /Rlt_le. apply  Rinv_lt_contravar.
                                 apply Rmult_lt_0_compat. nra. apply lt_0_INR. lia.
                                 apply lt_1_INR. apply /ssrnat.ltP. by []. 
                    --- simpl.
                        assert ((/ ((1 + default_rel ty) * (1 + default_rel ty) ^ n) *
                                    (1 + default_rel ty))%Re = 
                                (((1 + default_rel ty) * / (1 + default_rel ty)) * /(1 + default_rel ty) ^ n)%Re).
                        { rewrite Rinv_mult_distr. nra.
                          assert ((0 < 1 + default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                          { nra. } apply H1. 
                          apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
                          apply pow_nonzero.
                          assert ((0 < 1 + default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                          { nra. } apply H1. 
                          apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
                        } rewrite H1. rewrite Rinv_r.
                        assert (( / (1 + default_rel ty) ^ n <= / 1)%Re ->
                                (1 * / (1 + default_rel ty) ^ n <= 1)%Re).
                        { nra. } apply H2. destruct n.
                        *** simpl. nra.
                        *** apply Rlt_le.  
                            apply Rinv_lt_contravar. apply Rmult_lt_0_compat.
                            nra. apply pow_lt. apply Rplus_lt_0_compat. nra.
                            apply default_rel_gt_0. 
                            apply Rlt_pow_R1.
                            assert (forall x, (0 < x)%Re -> (1 < 1 + x)%Re).
                            { intros. nra. } apply H3. apply default_rel_gt_0.
                            lia.
                        *** assert ((0 < 1 + default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                            { nra. } apply H2. 
                            apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
                +++ apply not_0_INR. lia.
                +++ apply pow_nonzero . 
                    assert ((0 < 1 + default_rel ty)%Re -> (1 + default_rel ty)%Re <> 0%Re).
                    { nra. } apply H1. 
                    apply Rplus_lt_0_compat. nra. apply default_rel_gt_0. 
             ** apply H0.
Qed.


Lemma vec_float_sub {ty} {n:nat} (v1 v2 : 'cV[ftype ty]_n.+1):
  (forall (xy : ftype ty * ftype ty),
    In xy
      (combine 
         (vec_to_list_float n.+1 v1)
         (vec_to_list_float n.+1 v2)) ->
         finite xy.1 /\finite xy.2 /\ finite (BPLUS xy.1 (BOPP xy.2))) ->
  vec_inf_norm (FT2R_mat (v1 -f v2) - (FT2R_mat v1 - FT2R_mat v2)) <= 
  (vec_inf_norm (FT2R_mat v1) + vec_inf_norm (FT2R_mat v2)) * (default_rel ty) .
Proof.
intros Hfin.
unfold vec_inf_norm.
apply /RleP. apply lemmas.bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
rewrite !mxE. rewrite -!RminusE -RmultE -!RplusE.
specialize (Hfin ((v1 (inord i) ord0), (v2 (inord i) ord0))).
assert (Hin: In (v1 (inord i) ord0, v2 (inord i) ord0)
           (combine (vec_to_list_float n.+1 v1)
              (vec_to_list_float n.+1 v2))).
{ apply in_rev. rewrite -combine_rev; last by rewrite !length_veclist.
  assert ((v1 (inord i) ord0, v2 (inord i) ord0) = 
           nth i (combine (rev (vec_to_list_float n.+1 v1))
                    (rev (vec_to_list_float n.+1 v2))) (Zconst ty 0, Zconst ty 0)).
  { rewrite combine_nth. rewrite !rev_nth !length_veclist.
    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
    { lia. } rewrite H0. rewrite !nth_vec_to_list_float; try by [].
    by rewrite size_map size_enum_ord in H.
    by rewrite size_map size_enum_ord in H.
    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H.
    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H.
    by rewrite !rev_length !length_veclist.
 } rewrite H0. apply nth_In. rewrite combine_length.
 rewrite !rev_length !length_veclist Nat.min_id.
 rewrite size_map size_enum_ord in H. by apply /ssrnat.ltP.
} specialize (Hfin Hin).
rewrite Bminus_bplus_opp_equiv.
+ assert ((FT2R (v1 (inord i) ord0) -  FT2R (v2 (inord i) ord0))%Re = 
          (FT2R (v1 (inord i) ord0) +  FT2R (BOPP (v2 (inord i) ord0)))%Re ).
  { unfold FT2R. rewrite B2R_Bopp. nra. }
  rewrite H0.
  apply Rle_trans with 
  ((Rabs (FT2R (v1 (inord i) ord0)) + Rabs (FT2R (BOPP (v2 (inord i) ord0)))) * (default_rel ty))%Re.
  - apply BPLUS_error_le_rel.
    apply Hfin. 
  - apply Rle_trans with
    ((bigmaxr 0%Re
          [seq Rabs (FT2R_mat v1 i0 ord0)
             | i0 <- enum 'I_n.+1] +
        bigmaxr 0%Re
          [seq Rabs (FT2R_mat v2 i0 ord0)
             | i0 <- enum 'I_n.+1]) * default_rel ty)%Re.
    * apply Rmult_le_compat_r.
      ++ apply default_rel_ge_0.
      ++ apply Rplus_le_compat.
         -- apply Rle_trans with 
            [seq Rabs (FT2R_mat v1 i0 ord0)
                 | i0 <- enum 'I_n.+1]`_i.
            ** rewrite seq_equiv. rewrite nth_mkseq;
               last by rewrite size_map size_enum_ord in H.
               rewrite !mxE. nra.
            ** apply /RleP. 
               apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v1 i0 ord0)
                                              | i0 <- enum 'I_n.+1] i).
               rewrite size_map size_enum_ord.
               by rewrite size_map size_enum_ord in H.
         -- apply Rle_trans with 
            [seq Rabs (FT2R_mat v2 i0 ord0)
                 | i0 <- enum 'I_n.+1]`_i.
            ** rewrite seq_equiv. rewrite nth_mkseq;
               last by rewrite size_map size_enum_ord in H.
               rewrite !mxE. unfold FT2R. rewrite B2R_Bopp Rabs_Ropp. nra.
            ** apply /RleP. 
               apply (@bigmaxr_ler _ 0%Re [seq Rabs (FT2R_mat v2 i0 ord0)
                                              | i0 <- enum 'I_n.+1] i).
               rewrite size_map size_enum_ord.
               by rewrite size_map size_enum_ord in H.
    * apply Rle_refl.
+ apply Hfin.
Qed.


Lemma vec_float_sub_1 {ty} {n:nat} (v1 v2 : 'cV[ftype ty]_n.+1):
  (forall (xy : ftype ty * ftype ty),
    In xy
      (combine 
         (vec_to_list_float n.+1 v1)
         (vec_to_list_float n.+1 v2)) ->
    finite xy.1 /\ finite xy.2 /\ finite (BPLUS xy.1 (BOPP xy.2))) ->
  vec_inf_norm (FT2R_mat (v1 -f v2) - (FT2R_mat v1 - FT2R_mat v2)) <= 
  (vec_inf_norm (FT2R_mat v1 - FT2R_mat v2)) * (default_rel ty) .
Proof.
intros Hfin.
unfold vec_inf_norm.
apply /RleP. apply lemmas.bigmax_le; first by rewrite size_map size_enum_ord.
intros. rewrite seq_equiv. 
rewrite nth_mkseq; last by rewrite size_map size_enum_ord in H.
rewrite !mxE. rewrite -!RminusE -RmultE.
specialize (Hfin ((v1 (inord i) ord0), (v2 (inord i) ord0))).
assert (Hin: In (v1 (inord i) ord0, v2 (inord i) ord0)
           (combine (vec_to_list_float n.+1 v1)
              (vec_to_list_float n.+1 v2))).
{ apply in_rev. rewrite -combine_rev; last by rewrite !length_veclist.
  assert ((v1 (inord i) ord0, v2 (inord i) ord0) = 
           nth i (combine (rev (vec_to_list_float n.+1 v1))
                    (rev (vec_to_list_float n.+1 v2))) (Zconst ty 0, Zconst ty 0)).
  { rewrite combine_nth. rewrite !rev_nth !length_veclist.
    assert ((n.+1 - i.+1)%coq_nat = (n.+1.-1 - i)%coq_nat).
    { lia. } rewrite H0. rewrite !nth_vec_to_list_float; try by [].
    by rewrite size_map size_enum_ord in H.
    by rewrite size_map size_enum_ord in H.
    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H.
    apply /ssrnat.ltP. by rewrite size_map size_enum_ord in H.
    by rewrite !rev_length !length_veclist.
 } rewrite H0. apply nth_In. rewrite combine_length.
 rewrite !rev_length !length_veclist Nat.min_id.
 rewrite size_map size_enum_ord in H. by apply /ssrnat.ltP.
} specialize (Hfin Hin).
rewrite Bminus_bplus_opp_equiv.
+ assert ((FT2R (v1 (inord i) ord0) -  FT2R (v2 (inord i) ord0))%Re = 
          (FT2R (v1 (inord i) ord0) +  FT2R (BOPP (v2 (inord i) ord0)))%Re ).
  { unfold FT2R. rewrite B2R_Bopp. nra. }
  rewrite H0.
  apply Rle_trans with 
  (Rabs (FT2R (v1 (inord i) ord0) + (FT2R (BOPP (v2 (inord i) ord0)))) * (default_rel ty))%Re.
  - apply BPLUS_error_le_rel'.
    apply Hfin.
  - apply Rmult_le_compat_r.
    * apply default_rel_ge_0.
    * apply Rle_trans with 
      [seq Rabs
          ((FT2R_mat v1 - FT2R_mat v2)%Ri i0
             0)
      | i0 <- enum 'I_n.+1]`_i.
      ++ rewrite seq_equiv. rewrite nth_mkseq;
         last by rewrite size_map size_enum_ord in H.
         rewrite !mxE. rewrite -RminusE.
         assert (FT2R (BOPP (v2 (inord i) ord0)) = 
                  (- (FT2R (v2 (inord i) ord0)))%Re).
         { unfold FT2R. rewrite B2R_Bopp. nra. }
         rewrite H1. apply Rle_refl.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re [seq Rabs
                                           ((FT2R_mat v1 - FT2R_mat v2)%Ri i0
                                              0)
                                       | i0 <- enum 'I_n.+1] i).
         rewrite size_map size_enum_ord.
         by rewrite size_map size_enum_ord in H.
+ apply Hfin.
Qed.



End WITHNANS.