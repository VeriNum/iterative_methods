Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse sparse_model spec_sparse.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdLib.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := SparseASI ++ MathASI.

Lemma fold_csr_rep:
  forall sh  (p v ci rp: val) mval (csr: csr_matrix Tdouble),
     csr_rep_aux mval csr ->
     data_at sh t_csr
          (v, (ci, (rp, (Vint (Int.repr (matrix_rows mval)),
                      Vint (Int.repr (csr_cols csr)))))) p *
     data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v *
     data_at sh (tarray tuint (Zlength (csr_col_ind csr)))
                     (map Vint (map Int.repr (csr_col_ind csr))) ci *
     data_at sh (tarray tuint (matrix_rows mval + 1))
            (map Vint (map Int.repr (csr_row_ptr csr))) rp
     |-- csr_rep sh mval p.
Proof.
intros.
unfold csr_rep.
Exists v ci rp csr.
rewrite prop_true_andp by auto.
cancel.
Qed.

Lemma body_csr_matrix_rows: semax_body Vprog Gprog f_csr_matrix_rows csr_matrix_rows_spec.
Proof.
start_function.
forward.
sep_apply fold_csr_rep.
forward.
Qed.

Lemma body_csr_row_vector_multiply: semax_body Vprog Gprog f_csr_row_vector_multiply csr_row_vector_multiply_spec.
Proof.
start_function.
rename H3 into FINmval.
assert (0 <= matrix_rows mval) by (unfold matrix_rows; rep_lia).
forward.
forward.
forward.
freeze FR1 := (data_at sh1 _ _ _).
rename v0 into vp.
assert_PROP (0 <= i + 1 < Zlength (csr_row_ptr csr))
  by (entailer!; list_solve).
forward.
forward.
clear H6.
assert (CRS := H5).
assert (COLS: csr_cols csr = Zlength vval). {
  pose proof (csr_rep_matrix_cols _ _ H5).
  rewrite <- (sublist.Forall_Znth _ _ _ H2 H).
  rewrite (sublist.Forall_Znth _ _ _ H2 H6); auto.
}
destruct H5 as [H2' [H7 [H8 [H9 H10]]]].
unfold matrix_rows in *.
assert (H9': 0 <= Znth i (csr_row_ptr csr) <= Znth (i+1) (csr_row_ptr csr) 
            /\ Znth (i+1) (csr_row_ptr csr) <= Znth (Zlength mval) (csr_row_ptr csr) <= Int.max_unsigned)
   by (clear - H9 H2' H2; list_solve).
clear H9. destruct H9' as [H9 H9'].
forward_for_simple_bound (Znth (i + 1) (csr_row_ptr csr))
  (EX h:Z, PROP(0 <= Znth i (csr_row_ptr csr) <= h)
   LOCAL (
   temp _s (Vfloat (partial_row i h (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval));
   temp _i (Vint (Int.repr i));
   temp _hi (Vint (Int.repr (Znth (i+1) (csr_row_ptr csr)))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _m m; temp _v v)
   SEP (FRZL FR1;
   data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
   data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
     (map Vint (map Int.repr (csr_col_ind csr))) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr (csr_row_ptr csr))) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v))%assert.
-
 forward.
 change float with (ftype Tdouble) in *. 
 EExists. entailer!.
 f_equal. erewrite partial_row_start. reflexivity. eassumption.
-
rename i0 into h.
forward.
change float with (ftype Tdouble) in *. 
forward.
assert (0 <= Znth h (csr_col_ind csr) < Zlength vval). {
    specialize (H10 _ H2).
    assert (H11 := csr_row_rep_col_range _ _ _ _ H10 (h - Znth i (csr_row_ptr csr))).
    autorewrite with sublist in H11.
  rewrite COLS in *.
  apply H11. rep_lia.
  }
forward.
rewrite (@Znth_map (ftype Tdouble) _ _ _ h Vfloat) by rep_lia.
rewrite (@Znth_map (ftype Tdouble) _ _ _ (Znth h (csr_col_ind csr))) by rep_lia.
forward_call (Znth h (csr_vals csr), Znth (Znth h (csr_col_ind csr)) vval, partial_row i h (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval).
forward.
entailer!.
f_equal.
rewrite BFMA_eq.
eapply partial_row_next; try eassumption; lia.
-
 forward.
 Exists  (partial_row i (Znth (i + 1) (csr_row_ptr csr)) (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval).
 entailer!.
 erewrite partial_row_end; try eassumption; auto.
 unfold matrix_vector_mult.
 rewrite Znth_map by rep_lia. reflexivity.
 unfold csr_rep.
 thaw FR1.
 Exists vp ci rp csr.
 entailer!.
Qed.

Lemma body_csr_matrix_vector_multiply_byrows: semax_body Vprog Gprog f_csr_matrix_vector_multiply_byrows csr_matrix_vector_multiply_byrows_spec.
Proof.
start_function.
forward_call.
forward_for_simple_bound (Zlength mval)
  (EX i:Z, EX result: list (ftype Tdouble),
   PROP(Forall2 feq result (sublist 0 i (matrix_vector_mult mval vval))) 
   LOCAL (temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (csr_rep sh1 mval m;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) 
      (map Vfloat result ++ Zrepeat Vundef (matrix_rows mval - i)) p))%assert.
- unfold matrix_rows in H0; lia.
- Exists (@nil (ftype Tdouble)). simpl app. entailer!.
     apply derives_refl.
- forward_call (sh1,sh2,sh3, m, mval, v, vval, i).
   Intros s.
   unfold matrix_rows in H0.
   forward.
   progress change float with (ftype Tdouble) in *. 
   Exists (result ++ [s]).
   entailer!. 
   clear H11 H12 H10 H9 H8 H7 PNp PNv PNm.
   assert (Zlength (matrix_vector_mult mval vval) = Zlength mval). 
      unfold matrix_vector_mult. list_solve.
   rewrite (sublist_split 0 i (i+1)) by list_solve.
   apply Forall2_app.
   auto.
   rewrite sublist_len_1 by rep_lia.
   constructor; [ | constructor].
   unfold matrix_vector_mult. rewrite Znth_map by rep_lia. auto.
   assert (Zlength result = i). {
     clear - H5 H4. unfold matrix_vector_mult in H5.
      apply Forall2_Zlength in H5. rewrite H5.
    list_solve.
   }
   apply derives_refl'; f_equal.
   unfold matrix_rows; subst i. clear H9 H11 H12 H10 H8 H7 PNp PNv PNm H5.
    list_solve.
-
 Intro result. Exists result.
 unfold matrix_rows in *. list_simplify.
 entailer!.
 unfold matrix_vector_mult in H8 |- *.
 rewrite sublist_same in H8 by list_solve. auto.
Qed.

