Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse sparse_model spec_sparse.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := SparseASI ++ MathASI.

Definition the_loop_body : statement.
let c := constr:(f_csr_matrix_vector_multiply) in
let c := eval red in c in 
match c with context [Sloop (Ssequence _ ?body)] =>
 exact body
end.
Defined.

Lemma csr_multiply_loop_body: 
 forall (Espec : OracleKind)  (sh1 sh2 sh3 : share)
   (m : val) (mval : matrix Tdouble)
   (v : val) (vval : vector Tdouble)
   (p : val) (partial_result: list val)
  (SH : readable_share sh1)
  (SH0 : readable_share sh2)
  (SH1 : writable_share sh3)
  (H : matrix_cols mval (Zlength vval))
  (H0 : matrix_rows mval < Int.max_unsigned)
  (H1 : Zlength vval < Int.max_unsigned)
  (H2 : Forall (Forall finite) mval)
  (FINvval: Forall finite vval)
  (H3 : 0 <= matrix_rows mval)
  (vp ci rp : val)
  (csr : csr_matrix Tdouble)
  (H4 : csr_to_matrix csr mval)
  (FRAME: mpred)
  (H5 : 0 <= 0 < Zlength (csr_row_ptr csr))
  (i : Z)
  (H6 : 0 <= i < matrix_rows mval),
semax (func_tycontext f_csr_matrix_vector_multiply Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _next (Vint (Int.repr (Znth i (csr_row_ptr csr)))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (FRAME;
   data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
   data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
     (map Vint (map Int.repr (csr_col_ind csr))) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr (csr_row_ptr csr))) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) partial_result p))
      the_loop_body
  (normal_ret_assert
    (EX r: ftype Tdouble,
     (PROP (feq r (dotprod (Znth i mval) vval))
      LOCAL (temp _i (Vint (Int.repr i));
      temp _next (Vint (Int.repr (Znth (i + 1) (csr_row_ptr csr))));
      temp _row_ptr rp; temp _col_ind ci; temp _val vp;
      temp _rows (Vint (Int.repr (matrix_rows mval))); 
      temp _m m; temp _v v; temp _p p)
      SEP (FRAME;
      data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
      data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
        (map Vint (map Int.repr (csr_col_ind csr))) ci;
      data_at sh1 (tarray tuint (matrix_rows mval + 1))
        (map Vint (map Int.repr (csr_row_ptr csr))) rp;
      data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
      data_at sh3 (tarray tdouble (matrix_rows mval))
                   (upd_Znth i partial_result (Vfloat r)) p)))).
Proof.
intros.
unfold the_loop_body.
abbreviate_semax.
assert (CRS := H4).
assert (COLS := csr_to_matrix_cols _ _ H4).
destruct H4 as [? [? [? [? ?]]]].
forward.
forward.
assert(0 <= i + 1 < Zlength (csr_row_ptr csr))
  by (rewrite H4; unfold matrix_rows in H6; lia).
forward.

forward_loop 
  (EX h:Z, (PROP (Znth i (csr_row_ptr csr) <= h <= Znth (i+1) (csr_row_ptr csr) )
   LOCAL (
   temp _s (Vfloat (partial_row i h (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval));
   temp _i (Vint (Int.repr i));
   temp _h (Vint  (Int.repr h));
   temp _next (Vint (Int.repr (Znth (i+1) (csr_row_ptr csr)))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (FRAME;
   data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
   data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
     (map Vint (map Int.repr (csr_col_ind csr))) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr (csr_row_ptr csr))) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) partial_result p)))
  break:
  (EX r: ftype Tdouble,
   PROP (feq r (dotprod (Znth i mval) vval))
   LOCAL (
   temp _s (Vfloat r);
   temp _i (Vint (Int.repr i));
   temp _next (Vint (Int.repr (Znth (i+1) (csr_row_ptr csr)))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (FRAME;
   data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
   data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
     (map Vint (map Int.repr (csr_col_ind csr))) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr (csr_row_ptr csr))) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) partial_result p)).
-
EExists. entailer!.
split.
clear - H6 H11 H9. list_solve.
 erewrite partial_row_start; try eassumption. reflexivity.
-
Intros h.
 assert (Znth (i+1) (csr_row_ptr csr) <= Int.max_unsigned) by list_solve.
forward_if.
 +
  assert (0 <= Znth i (csr_row_ptr csr)) by list_solve.
  rewrite Int.unsigned_repr in H14 by list_solve.
  rewrite Int.unsigned_repr in H14 
     by (clear - H4 H6 H9; unfold matrix_rows in H6; list_solve).
  forward.
  apply prop_right. rewrite H8. unfold matrix_rows in *; list_solve.
  entailer!.
   change float with (ftype Tdouble) in *.
   unfold matrix_rows in *.
   rewrite Znth_map. hnf; auto.
   clear - H7 H14 H12 H6 H9 H4. list_solve.
  assert (0 <= h < Zlength (csr_col_ind csr))
    by (rewrite H8; clear - H7 H14 H12 H6 H9 H4; unfold matrix_rows in *;  list_solve).
  forward.
  assert (0 <= Znth h (csr_col_ind csr) < Zlength vval). {
     assert (Znth i (csr_row_ptr csr) <= h < Znth (i+1) (csr_row_ptr csr)) by lia.
     assert (Znth (i+1) (csr_row_ptr csr) <= Zlength (csr_col_ind csr)) by list_solve.
     clear - COLS H H17 H14 H6 H10 H15 H18.
      specialize (H10 _ H6).
      replace (Znth h (csr_col_ind csr)) with 
              (Znth (h-Znth i (csr_row_ptr csr)) (sublist (Znth i (csr_row_ptr csr)) (Znth (i+1) (csr_row_ptr csr)) (csr_col_ind csr)))
         by list_solve.

  pose proof (csr_row_rep_col_range _ _ _ _ H10).
  specialize (H0 (h - Znth i (csr_row_ptr csr))).
  autorewrite with sublist in H0. autorewrite with sublist. 
  rewrite <- (sublist.Forall_Znth _ _ _ H6 H), (sublist.Forall_Znth _ _ _ H6 COLS).
  apply H0. list_solve.
  }
  forward.
  change float with (ftype Tdouble) in *.
  rewrite (@Znth_map (ftype Tdouble) _ _ _ h Vfloat) by rep_lia.
  rewrite (@Znth_map (ftype Tdouble) _ _ _ (Znth h (csr_col_ind csr))) by rep_lia.
  forward_call (Znth h (csr_vals csr), Znth (Znth h (csr_col_ind csr)) vval, partial_row i h (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval).
  forward.
  Exists (h+1).
  entailer!.
  f_equal.
  change (FPCore.fprec _) with (fprec Tdouble).
  rewrite BFMA_eq.
  eapply partial_row_next; try eassumption; lia.
+
 forward. 
 Exists (partial_row i h (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval).
 entailer!. 
 replace h with (Znth (i+1) (csr_row_ptr csr)).
 erewrite partial_row_end; try eassumption.
 unfold matrix_vector_mult.
 rewrite Znth_map by lia. reflexivity.
  rewrite <- (sublist.Forall_Znth _ _ _ H6 H), (sublist.Forall_Znth _ _ _ H6 COLS); auto.
 clear - H14 H13 H12 H9 H4 H0 H10 H6.
 specialize (H10 i H6).
 unfold matrix_rows in *.
  rewrite Int.unsigned_repr in H14 by list_solve.
  rewrite Int.unsigned_repr in H14 
     by (clear - H4 H6 H9; unfold matrix_rows in H6; list_solve).
 lia.
-
Intros r.
forward.
Exists r.
entailer!.
Qed.

Lemma body_csr_matrix_vector_multiply: semax_body Vprog Gprog f_csr_matrix_vector_multiply csr_matrix_vector_multiply_spec.
Proof.
start_function.
rename H into H'. rename H0 into H; rename H1 into H0; rename H2 into H1;
rename H3 into H2; rename H4 into FINmval.
assert (0 <= matrix_rows mval) by (unfold matrix_rows; rep_lia).
forward.
forward.
forward.
forward.
freeze FR1 := (data_at sh1 _ _ _).
rename v0 into vp.
(*assert_PROP (0 <= 0 < csr_rows csr + 1)
 by (entailer!!; rewrite (csr_to_matrix_rows _ _ H'); lia).*)
assert_PROP (0 <= 0 < Zlength (csr_row_ptr csr)) as H4'
  by (entailer!; rewrite !Zlength_map in H11; rewrite H11, (csr_to_matrix_rows _ _ H');lia). 
forward.
  entailer!!. rewrite (csr_to_matrix_rows _ _ H'); lia.
forward_for_simple_bound (matrix_rows mval)
  (EX i:Z, EX result: list (ftype Tdouble),
   PROP(Forall2 feq result (sublist 0 i (matrix_vector_mult mval vval))) 
   LOCAL (temp _next (Vint (Int.repr (Znth i (csr_row_ptr csr)))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (FRZL FR1;
   data_at sh1 (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) vp;
   data_at sh1 (tarray tuint (Zlength (csr_col_ind csr)))
     (map Vint (map Int.repr (csr_col_ind csr))) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr (csr_row_ptr csr))) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) 
      (map Vfloat result ++ Zrepeat Vundef (matrix_rows mval - i)) p))%assert.
-
Exists (@nil (ftype Tdouble)). simpl app.
entailer!!.
   f_equal; f_equal; symmetry; apply csr_to_matrix_rows; auto.
   rewrite (csr_to_matrix_rows _ _ H'). cancel.  
-
Intros.
eapply semax_post_flipped'.
eapply csr_multiply_loop_body; eassumption; auto.
Intros r.
Exists (result ++ [r]).
entailer!!. {
  clear - H4 H5 H6.
  assert (matrix_rows mval = Zlength (matrix_vector_mult mval vval)). {
    unfold matrix_vector_mult. rewrite Zlength_map. reflexivity.
  }
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite sublist_len_1 by list_solve.
  apply Forall2_app; auto.
  constructor; auto.
  unfold matrix_vector_mult. rewrite Znth_map by auto. auto.
}
apply derives_refl'. f_equal.
assert (Zlength result = i). {
 apply Forall2_Zlength in H5. 
 clear - H5 H4. unfold matrix_rows, matrix_vector_mult in *. list_solve.
}
clear - H7 H4.
unfold matrix_rows in *.
rewrite upd_Znth_app2
 by list_solve.
rewrite !map_app.
rewrite <- app_assoc.
f_equal.
list_solve.
-
Intros result.
Exists result.
rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
thaw FR1.
entailer!.
clear - H4.
unfold matrix_rows, matrix_vector_mult in *.
rewrite sublist_same in H4 by list_solve. auto.
unfold csr_rep.
Exists vp ci rp.
rewrite (csr_to_matrix_rows _ _ H').
cancel.
Qed.
