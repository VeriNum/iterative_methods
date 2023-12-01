From Coq Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect ssralg 
              ssrnat all_algebra seq matrix.
From mathcomp.analysis Require Import Rstruct.
Import List ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import lemmas inf_norm_properties.

Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


(** 2 norm of a vector **)
Definition vec_norm2 {n:nat} (v : 'cV[R]_n.+1) :=
  sqrt (\sum_j (Rsqr (v j ord0))).


Lemma sum_const {n:nat} (a:R): 
  \sum_(j < n) a = (INR n * a)%Re.
Proof.
induction n.
+ rewrite big_ord0 /=. by rewrite RmultE mul0r.
+ rewrite big_ord_recr. rewrite IHn.
  rewrite -addn1. rewrite plus_INR /=.
  rewrite Rmult_plus_distr_r. rewrite -RplusE. nra.
Qed. 


Lemma norm2_inf_norm_compat {n:nat} (v : 'cV[R]_n.+1):
  (vec_norm2 v <= sqrt (INR n.+1) * vec_inf_norm v)%Re.
Proof.
unfold vec_norm2, vec_inf_norm.
match goal with |-context[(_ <= _ * ?a)%Re]=>
  replace a with (sqrt (Rsqr a)) 
end.
+ rewrite -sqrt_mult_alt.
  - apply sqrt_le_1_alt . rewrite -sum_const .
    apply /RleP. apply big_sum_ge_ex_abstract.
    intros. rewrite Rsqr_abs. apply  Rsqr_incr_1.
    * apply Rle_trans with 
      [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1]`_i.
      ++ rewrite seq_equiv. rewrite nth_mkseq. 
         rewrite inord_val. apply Rle_refl.
         apply ltn_ord.
      ++ apply /RleP. 
         apply (@bigmaxr_ler _ 0%Re 
                    [seq Rabs (v i0 0) | i0 <- enum 'I_n.+1] i).
    * rewrite size_map size_enum_ord. apply ltn_ord.
    * apply Rabs_pos.
  - apply /RleP. apply bigmax_le_0. apply /RleP. apply Rle_refl.
    intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H0.
    apply /RleP. apply Rabs_pos.
  - apply pos_INR.
+ apply sqrt_Rsqr. apply /RleP. apply bigmax_le_0.
  - apply /RleP. apply Rle_refl.
  - intros. rewrite seq_equiv. rewrite nth_mkseq;
    last by rewrite size_map size_enum_ord in H.
    apply /RleP. apply Rabs_pos.
Qed.

Require Import floatlib fma_floating_point_model common 
      op_defs sum_model fma_dot_acc float_acc_lems dotprod_model fma_matrix_vec_mult.


From vcfloat Require Import FPStdLib.

Lemma fma_dot_prod_norm2_holds {t} {n:nat} {NANS: Nans} m (v : 'cV[ftype t]_n.+1):
  let v_l := @vec_to_list_float _ n m v in
  fma_dot_prod_rel (combine v_l v_l) (norm2 (rev v_l)).
Proof.
intros.
unfold norm2. rewrite dotprod_rev_equiv;last by []. unfold v_l.
induction m.
+ simpl. apply fma_dot_prod_rel_nil.
+ simpl.
  assert ( dotprod_r
             (v (inord m) ord0 :: vec_to_list_float m v)
             (v (inord m) ord0 :: vec_to_list_float m v) = 
            BFMA (v (inord m) ord0) (v (inord m) ord0) 
            (dotprod_r (vec_to_list_float m v)
                      (vec_to_list_float m v))).
  { apply dotprod_cons . by rewrite !length_veclist. } 
  rewrite H. by apply fma_dot_prod_rel_cons. 
Qed.



Lemma R_dot_prod_norm2_holds {t} {n:nat} {NANS: Nans} m 
  (v : 'cV[ftype t]_n.+1) (le_n_m : (m <= n.+1)%nat):
  let v_l := @vec_to_list_float _ n m v in
   R_dot_prod_rel  (combine (map FT2R v_l) (map FT2R v_l))
   (\sum_(j < m)
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) 0 * 
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) 0).
Proof.
intros. unfold v_l.
induction m.
+ simpl. rewrite big_ord0 //=. apply R_dot_prod_rel_nil.
+ simpl. rewrite big_ord_recr //=.
  rewrite -RplusE -RmultE.
  assert ((widen_ord le_n_m ord_max) = (inord m)).
  { unfold widen_ord. 
    apply val_inj. simpl. by rewrite inordK.
  } rewrite H. rewrite Rplus_comm. rewrite !mxE.
  apply R_dot_prod_rel_cons.
  assert ((m <= n.+1)%nat). { by apply ltnW. }
  specialize (IHm H0). 
  assert (\sum_(j < m)
            FT2R_mat v (widen_ord H0 j) 0 *
            FT2R_mat v (widen_ord H0 j) 0 = 
          \sum_(i0 < m)
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) 0 *
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) 0).
  { apply eq_big. by []. intros.
    assert ((widen_ord le_n_m
                  (widen_ord (leqnSn m) i))= 
             (widen_ord  H0 i)).
    { unfold widen_ord. 
      apply val_inj. by simpl.
    } by rewrite H2.
  } rewrite -H1. apply IHm.
Qed.

Lemma R_dot_prod_norm2_abs_holds {t} {n:nat} {NANS: Nans} m 
  (v : 'cV[ftype t]_n.+1) (le_n_m : (m <= n.+1)%nat):
  let v_l := @vec_to_list_float _ n m v in
  R_dot_prod_rel
      (combine
         (map Rabs (map FT2R v_l))
         (map Rabs (map FT2R v_l)))
       (\sum_(j < m)
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) 0 * 
      FT2R_mat v (@widen_ord m n.+1 le_n_m j) 0).
Proof.
intros. induction m.
+ simpl. rewrite big_ord0 //=. apply R_dot_prod_rel_nil.
+ simpl. rewrite big_ord_recr //=.
  rewrite -RplusE -RmultE.
  assert ((widen_ord le_n_m ord_max) = (inord m)).
  { unfold widen_ord. 
    apply val_inj. simpl. by rewrite inordK.
  } rewrite H. rewrite Rplus_comm. rewrite !mxE.
  Print  R_dot_prod_rel_cons.
  assert ((FT2R (v (inord m) ord0) * FT2R (v (inord m) ord0))%Re = 
          (Rabs (FT2R (v (inord m) ord0)) * Rabs (FT2R (v (inord m) ord0)))%Re).
  { assert (forall x:R, Rsqr x = (x * x)%Re).
    { intros. unfold Rsqr;nra. } rewrite -!H0.
      by rewrite Rsqr_abs.
  } rewrite H0. 
   apply R_dot_prod_rel_cons.
  assert ((m <= n.+1)%nat). { by apply ltnW. }
  specialize (IHm H1). 
  assert (\sum_(j < m)
            FT2R_mat v (widen_ord H1 j) 0 *
            FT2R_mat v (widen_ord H1 j) 0 = 
          \sum_(i0 < m)
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) 0 *
                FT2R_mat v
                  (widen_ord le_n_m
                     (widen_ord (leqnSn m) i0)) 0).
  { apply eq_big. by []. intros.
    assert ((widen_ord le_n_m
                  (widen_ord (leqnSn m) i))= 
             (widen_ord  H1 i)).
    { unfold widen_ord. 
      apply val_inj. by simpl.
    } by rewrite H3.
  } rewrite -H2. apply IHm.
Qed. 



(*** error between norm2 float and norm2 real **)
Lemma norm2_error {t} {n:nat} {NANS: Nans} (v : 'cV[ftype t]_n.+1):
  let v_l := vec_to_list_float n.+1 v in
  (forall xy : ftype t * ftype t,
     In xy (combine v_l v_l) -> finite xy.1 /\ finite xy.2) ->
  finite (norm2 (rev v_l)) ->
  Rabs (FT2R (norm2 (rev v_l)) - Rsqr (vec_norm2 (FT2R_mat v))) <=  
  g t n.+1 * (Rsqr (vec_norm2 (FT2R_mat v))) + g1 t n.+1 (n.+1 - 1)%coq_nat.
Proof.
intros.
pose proof (@fma_dotprod_forward_error _ t v_l v_l).
assert (length v_l = length v_l).
{ by rewrite !length_veclist. }
specialize (H1 H2).
specialize (H1 (norm2 (rev v_l)) (Rsqr (vec_norm2 (FT2R_mat v))) 
              (Rsqr (vec_norm2 (FT2R_mat v)))).
specialize (H1 (fma_dot_prod_norm2_holds n.+1 v)).
assert (Rsqr (vec_norm2 (FT2R_mat v)) = 
         \sum_(j < n.+1)
            FT2R_mat v (@inord n j) 0 * 
            FT2R_mat v (@inord n j) 0).
{ unfold vec_norm2. 
  rewrite Rsqr_sqrt.
  + apply eq_big. by []. intros. rewrite -RmultE. unfold Rsqr.
    by rewrite inord_val.
  + apply /RleP. apply big_ge_0_ex_abstract. intros.
    apply /RleP. apply Rle_0_sqr.
} rewrite H3 in H1.
pose proof (R_dot_prod_norm2_holds v (leqnn n.+1)).
assert ( \sum_j (FT2R_mat v  (widen_ord (leqnn n.+1) j) 0 *
                  FT2R_mat v  (widen_ord (leqnn n.+1) j) 0) = 
          \sum_(j < n.+1)
            FT2R_mat v (@inord n j) 0 * 
            FT2R_mat v (@inord n j) 0).
{ apply eq_big. by []. intros.
  assert (widen_ord (leqnn n.+1) i = i).
  { unfold widen_ord. apply val_inj. by simpl. }
  rewrite H6. by rewrite inord_val.
} rewrite -H5 in H1. specialize (H1 H4).
specialize (H1 (R_dot_prod_norm2_abs_holds v (leqnn n.+1)) H0).
rewrite H3 -H5.
assert (length v_l = n.+1).
{ unfold v_l. by rewrite length_veclist. }
rewrite H6 in H1. rewrite sum_abs_eq in H1.
+ apply H1.
+ intros. rewrite -RmultE. 
  assert (forall x:R, Rsqr x = (x * x)%Re).
  { intros. unfold Rsqr;nra. } rewrite -H1.
  apply Rle_0_sqr.
Qed.

(** Relate norm2 with inf-vec norm **)
Lemma norm2_vec_inf_norm_rel {t} {n:nat} {NANS: Nans} (v : 'cV[ftype t]_n.+1):
   let v_l := vec_to_list_float n.+1 v in
  (forall xy : ftype t * ftype t,
     In xy (combine v_l v_l) -> finite xy.1/\ finite xy.2) ->
   finite (norm2 (rev v_l)) ->
  (Rabs (FT2R (norm2 (rev v_l))) <=
    (INR n.+1 * Rsqr (vec_inf_norm (FT2R_mat v))) * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat)%Re.
Proof.
intros.
pose proof (@norm2_error _ _ _ v H H0).
apply Rle_trans with 
((vec_norm2 (FT2R_mat v))² * (1 + g t n.+1) + g1 t n.+1 (n.+1 - 1)%coq_nat).
+ assert (Rsqr (vec_norm2 (FT2R_mat v)) = Rabs (Rsqr (vec_norm2 (FT2R_mat v)))).
  { rewrite Rabs_right. nra. apply Rle_ge,  Rle_0_sqr . }
  rewrite H2. 
  rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
  assert (forall a b c d:R, (a - b<= c + d)%Re -> (a <= b + c + d)%Re).
  { intros. nra. } apply H3. 
  apply Rle_trans with
  (Rabs (FT2R (norm2 (rev v_l)) - (vec_norm2 (FT2R_mat v))²))%Re.
  - apply Rabs_triang_inv.
  - fold v_l in H1. rewrite Rmult_comm .
    rewrite -H2. apply H1.
+ apply Rplus_le_compat_r. apply Rmult_le_compat_r.
  - apply Rplus_le_le_0_compat. nra. apply g_pos.
  - assert (INR n.+1 = Rsqr (sqrt (INR n.+1))).
    { rewrite Rsqr_sqrt. by []. apply pos_INR. }
    rewrite H2. rewrite -Rsqr_mult.
    apply Rsqr_incr_1.
    * apply norm2_inf_norm_compat.
    * unfold vec_norm2. apply sqrt_pos.
    * apply Rmult_le_pos. apply sqrt_pos.
      apply /RleP. apply vec_norm_pd.
Qed.
    

