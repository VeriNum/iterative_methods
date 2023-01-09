Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model spec_sparse spec_jacobi fun_model_lemmas.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := JacobiASI ++ SparseASI ++ MathASI.

Lemma body_jacobi2_oneiter: semax_body Vprog Gprog f_jacobi2_oneiter jacobi2_oneiter_spec.
Proof.
start_function.
rename H3 into H4; rename H2 into H3; rename H1 into H2; pose proof I.
forward_call.
forward.
pose (r := jacobi_iter A1 A2 b x).
set (N := matrix_rows A2) in *.
assert (0 <= N < Int.max_unsigned) by (unfold matrix_rows in N; rep_lia).
clear H0 H1; rename H5 into H0.
assert_PROP (Zlength A1 = N /\ Zlength b = N /\ Zlength x = N).
  entailer!. rewrite Zlength_map in *. auto. 
forward_for_simple_bound N
  (EX i:Z, EX y: vector Tdouble, EX s: ftype Tdouble,
   PROP (Forall2 feq y (sublist 0 i r);
             feq s (norm2 (sublist 0 i (vector_sub x r))))
   LOCAL (temp _s (Vfloat s);
       temp _N (Vint (Int.repr (matrix_rows A2))); 
       temp _A1 A1p; temp _A2 A2p; temp _b bp; 
       temp _x xp; temp _y yp)
   SEP (crs_rep shA2 A2 A2p;
   data_at shA1 (tarray tdouble N) (map Vfloat A1) A1p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at shx (tarray tdouble N) (map Vfloat x) xp;
   data_at shy (tarray tdouble N) (map Vfloat y ++ Zrepeat Vundef (N-i)) yp))%assert.
- Exists (@nil (ftype Tdouble)) (Zconst Tdouble 0). entailer!.
   apply derives_refl.
- forward_call (shA2,shx,shy, A2p, A2, xp, x, i).
   replace (Zlength x) with N by (clear - H1; lia).  cancel.
   replace (Zlength x) with N by (clear - H1; lia).  auto.
   replace (Zlength x) with N by (clear - H1; lia).
   Intros y'.
   forward. 
   progress change float with (ftype Tdouble) in *.
   rewrite Znth_map by lia.
   forward.
       entailer!. rewrite Znth_map by lia. hnf; auto.
   rewrite Znth_map by lia.
   forward.
   forward.
       entailer!. rewrite Znth_map by lia. hnf; auto.
   rewrite Znth_map by lia.
   forward.
   forward_call.
   forward.
   autorewrite with float_elim in *.
   pose proof (Zlength_jacobi_iter A1 A2 b x ltac:(lia) ltac:(lia) ltac:(lia)).
   fold r in H9.
   change (Binary.Bfma _ _ _ _ _ _ ?x ?y ?z) with (BFMA x y z).
   Exists (y ++ [BDIV _ (Zconst _ 1) (Znth i A1) * (Znth i b - y')]%F64).
   EExists.
   entailer!.
 + 
  set (N := matrix_rows A2) in *.
  assert (Zlength (vector_sub x r) = N). {
     unfold vector_sub, map2. rewrite Zlength_map, Zlength_combine. lia.
  } 
  rewrite !(sublist_split 0 i (i+1)) by lia.
  rewrite !sublist_len_1 by lia.
  split.
  * apply Forall2_app; auto.
     constructor; [ | constructor].
     symmetry; eapply Znth_jacobi_iter; eauto; lia.
  *
    rewrite norm2_snoc.
    clear - H7 H8 H5 H2 H3 H4 H H1 H6 H9 .
    destruct H1 as [? [? ?]].
    rewrite Znth_vector_sub by lia.
    apply BFMA_xx_mor; auto.
    apply BMINUS_congr; auto.
    subst r.
   erewrite Znth_jacobi_iter; eauto.
 +
   apply derives_refl'; f_equal.
   clear - H9 H5 H1 H0 H20.  list_solve.
-
 Intros y s. forward. Exists y s.
 rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
 unfold crs_rep. Intros.
 entailer!.
 pose proof (Zlength_jacobi_iter A1 A2 b x ltac:(lia) ltac:(lia) ltac:(lia)).
 fold r in H21|-*. 
  set (N := matrix_rows A2) in *.
  assert (Zlength (vector_sub x r) = N). {
     unfold vector_sub, map2. rewrite Zlength_map, Zlength_combine. lia.
  } 
 rewrite sublist_same in H6,H5 by lia.
 split; auto.
 rewrite H6.
 clearbody r. clearbody N.
 destruct H1 as [_ [_ ?]].
 clear - H21 H5 H4 H1.
 apply norm2_loose_congr.
 apply vector_sub_congr; auto.
 clear - H4. induction H4; constructor; auto.
 clear - H5. induction H5; constructor; auto.
 symmetry; auto.
Qed.

