(** This file contains the main accuracy theorem **) 

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


From Iterative Require Import inf_norm_properties local_float_error real_model float_model.
From Iterative Require Import model_mat_lemmas lemmas vcfloat_lemmas.

From mathcomp Require Import matrix bigop all_algebra all_ssreflect.
From mathcomp.analysis Require Import Rstruct.
From Coquelicot Require Import Lub Rbar.

Local Open Scope float32_scope.

Section WITHNANS.
Context {NANS: Nans}.

Import Interval.Tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** We will open the real scope and the Ring scope 
  separately **)

Open Scope ring_scope.

(** We instantiate the ring scope with real scope using
  Delimit Scope ... **)
Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

(** We next import the ring theory so that we can use
  it for reals **)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Theorem iterative_round_off_error:
  forall (x_l: list (ftype Tsingle)),
  boundsmap_denote bmap (varmap x_l) -> 
  let x0 := listR_to_vecR (FT2R_list x_l) in
  let b := listR_to_vecR b_real in
  @vec_inf_norm 3 x0 <= 48 -> @vec_inf_norm 3 b <= 1 -> 
  let h := 1 in
  let h_f := 1%F32 in  
  let len := 3%nat in
  forall k: nat,
  (k <= 100)%nat -> 
  let varmap_k := (varmap (X_m k x_l b_float h_f)) in
  vec_inf_norm (@X_m_real k len x0 b h - listR_to_vecR (FT2R_list (X_m k x_l b_float h_f))) <=
  round_off_error *
  error_sum k.+1 (@matrix_inf_norm len (S_mat _ h)) /\ boundsmap_denote bmap varmap_k.
Proof.
intros ? ? ? ? ? Hx0 ? ? ?  ? Hk. intros.
induction k.
(* base case*)
-
split. 
+
rewrite /error_sum big_ord_recr //= expr0 big_ord0 add0r mulr1.
  rewrite /x0 x_minus_x_is_0.
  assert ( @vec_inf_norm (len.-1.+1) 0 = 0%Re).
  { apply vec_inf_norm_0_is_0. }
  assert (@vec_inf_norm (len.-1.+1) 0 = @vec_inf_norm len 0).
  { assert ((len.-1.+1) = len). 
    { by rewrite prednK. } auto.  
  } rewrite H1. apply /RleP.  apply roundoff_pos.
+
simpl in varmap_k; subst varmap_k; auto.
-
match goal with |-context [?A /\ ?B] => 
assert A;
try split; auto
end.
simpl in IHk; destruct IHk as (IHk & BMDk); try apply ltnW; auto.
try interval.
set (xkr := (X_m_real k x0 (listR_to_vecR b_real) h)) in *.
assert (X_m_real k.+1 x0 b h = X_m_real 1 xkr b h) by (apply X_m_real_iter).
set (xkf :=  @listR_to_vecR len (FT2R_list (X_m k x_l b_float h_f))) in *.
set (xkpf := @listR_to_vecR len (FT2R_list (X_m k.+1 x_l b_float h_f))).
assert ((X_m_real k.+1 x0 b h - listR_to_vecR (FT2R_list (X_m k.+1 x_l b_float h_f)))
= 
X_m_real 1 xkr b h - X_m_real 1 xkf b h + X_m_real 1 xkf b h - xkpf
).
rewrite H1.
subst xkpf.
apply vec_sum_simpl.
rewrite H2. 
apply /RleP.
eapply Rle_trans. 

apply /RleP.
apply cs_ineq_vec_inf_norm; auto.


eapply Rle_trans; auto.
apply /RleP.
eapply ler_add.

assert (Hlen: len = len.-1.+1) by (rewrite prednK; auto).
assert (Hlen2 : (0 < len)%nat). by unfold len. 
pose proof ( @matrix_norm_submult len Hlen2 xkr xkf b 1) as submult.
apply submult.  

pose proof step_round_off_error as Hstep.
set (sk:= (X_m k x_l b_float h_f)).
specialize (Hstep sk BMDk).
cbv zeta in Hstep.
unfold xkf.
assert (
H_Flist: listR_to_vecR (FT2R_list (X_m 1 (X_m k x_l b_float h_f) b_float 1%F32)) =
xkpf
).
+
unfold xkpf. 
rewrite /h_f.
by rewrite /X_m.
+
rewrite <- H_Flist .
unfold h in H1.
unfold len.
apply Hstep.
+
(* invoke lemma relating VCFloat bound (LHS) and analytic bound (RHS) *)
eapply Rle_trans. 
eapply Rplus_le_compat.
eapply Rmult_le_compat.
(* matrix norm positive definite *) 
apply /RleP. apply matrix_norm_pd.
(* vector norm positive definite *)
apply /RleP. apply vec_norm_pd.
apply Rle_refl.
unfold xkr.
unfold len in *.
apply /RleP.
apply IHk.
apply Rle_refl.
unfold h; subst len.
rewrite -!RmultE.
assert (Hsums : error_sum k.+2 (matrix_inf_norm (S_mat 3 1)) =
                 error_sum_ind (matrix_inf_norm (S_mat 3 1)) k.+2).
{ by rewrite error_sum_equiv. }
rewrite Hsums.
rewrite <- error_sum_aux2.
rewrite_scope.


rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
rewrite_scope.
eapply Rplus_le_compat.
rewrite <- error_sum_equiv.
rewrite_scope.
rewrite_scope.
rewrite Rmult_comm.
rewrite !Rmult_assoc.
apply Rmult_le_compat_l.
apply roundoff_pos.
rewrite Rmult_comm.
apply Rmult_le_compat_l.
rewrite_scope.
apply matrix_norm_pd.
all : (apply Req_le; auto).
+
simpl in IHk; destruct IHk as (IHk & BMDk); try apply ltnW; auto.
apply boundsmap_succ_step; auto.
unfold h in *; repeat fold x0 f_list b.
set (xkp:=
    (X_m_real k.+1 x0 b 1)).
set (xk :=
    (@X_m_real k len x0 b 1)).
exists 99; split; unfold xkp.
apply sol_up_bound_exists; auto.
exists (round_off_error * error_sum k.+2 (@matrix_inf_norm len (S_mat len 1))).
split.
apply H1. 
rewrite_scope. 
eapply Rle_trans.
eapply Rplus_le_compat_r.
rewrite_scope.
apply concrete_roundoff_k; try apply ltnW; auto.
compute; lra.
Qed.


End WITHNANS.

