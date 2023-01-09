Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model spec_sparse 
         spec_jacobi fun_model_lemmas vst_improvements.
Import RelationPairs.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import VSTlib.spec_malloc.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:Ctypes.type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Gprog: funspecs := surely_malloc_spec :: JacobiASI ++ SparseASI ++ MathASI ++ MallocASI.

(*
Definition first_loop : statement.
let c := constr:(f_jacobi2) in
let c := eval red in c in 
match c with context [Ssequence (Sset _i ?e) ?s] =>
 exact (Ssequence (Sset _i e ) s)
end.
Defined.
*)

Definition the_loop : statement.
let c := constr:(f_jacobi2) in
let c := eval red in c in 
match c with context [Sloop ?a ?b] => match a with context [Sset _maxiter] => idtac end;
 exact (Sloop a b)
end.
Defined.

(*
Lemma jacobi2_first_loop: forall {Espec : OracleKind}
  (sh1 : share) gv acc maxiter
  (A : matrix Tdouble)
  (yp xp A2p bp A1p : val)
  (SH : readable_share sh1),
  let N := matrix_rows A in
  forall  (H : matrix_cols A N)
  (H0 : 0 < N < Int.max_unsigned)
  (H1 : Forall (Forall finite) A)
  (A1ip : val)
  (FR1 : mpred),
semax (func_tycontext f_jacobi2 Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp; 
   temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; data_at_ Ews (tarray tdouble N) A1ip;
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p))
   first_loop
 (normal_ret_assert
  (PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp; 
   temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; data_at Ews (tarray tdouble N) (map Vfloat (invert_diagmatrix (diag_of_matrix A))) A1ip;
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p))).
Proof.
intros.
unfold first_loop.
abbreviate_semax.
assert (Zlength (diag_of_matrix A) = N)
  by (unfold diag_of_matrix; autorewrite with sublist; auto).
forward_for_simple_bound N
  (EX i:Z, PROP ( )
   LOCAL (temp _A1inv A1ip; temp _y yp; temp _z xp;
   temp _N (Vint (Int.repr N)); 
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp;
   temp _acc (Vfloat acc); temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FR1; 
   data_at sh1 (tarray tdouble N) (map Vfloat (diag_of_matrix A)) A1p;
   data_at Ews (tarray tdouble N)
        (map Vfloat (sublist 0 i (map (BDIV _ (Zconst _ 1)) (diag_of_matrix A)))
          ++ Zrepeat Vundef (N-i)) A1ip))%assert.
-
  entailer!. simpl; apply derives_refl.
- 
   forward.
   forward.
   change float with (ftype Tdouble) in *.
   rewrite Znth_map by list_solve.
   simpl force_val.
   entailer!.
   apply derives_refl'; f_equal.
   clear - H3 H2 H0 H H1.
   rewrite (sublist_split 0 i (i+1)) by list_solve.
   rewrite sublist_len_1 by list_solve.
   replace (matrix_rows A - i) with (matrix_rows A - (i+1) + 1) by lia.
   rewrite <- Zrepeat_app by lia.
   change (Zrepeat Vundef 1) with [Vundef].
   list_simplify.
   rewrite Znth_app1 by list_solve. f_equal.
   list_simplify.
-
list_simplify.
rewrite sublist_map.
rewrite sublist_same by auto.
fold (invert_diagmatrix (diag_of_matrix A)).
entailer!.
Qed.
*)

Definition choose {A} n (a b: A) := if Nat.odd n then a else b.

Lemma choose_S {A}: forall n (a b: A), choose (S n) a b = choose n b a.
Proof. 
intros. unfold choose. rewrite Nat.odd_succ, <-Nat.negb_odd;
        destruct (Nat.odd n); auto.
Qed.

Lemma jacobi2_the_loop: forall {Espec : OracleKind}
 (shA1 shA2 shb shx shy : share)
  (A : matrix Tdouble)
  (A1p A2p bp xp : val)
  (b x : vector Tdouble)
  (acc : ftype Tdouble)
  (maxiter : Z)
  (gv : globals)
  (SHA1 : readable_share shA1)
  (SHA2 : readable_share shA2)
  (SHb : readable_share shb)
  (SHx : writable_share shx)
  (SHy : writable_share shy)
  (N := matrix_rows A : Z)
  (COLS: matrix_cols A N)
  (FINA : Forall (Forall finite) A)
  (FINA1inv: Forall finite (invert_diagmatrix (diag_of_matrix A)))
  (FINb : Forall finite b)
  (FINx : Forall finite x)
  (FINacc : finite acc)
  (Hmaxiter : 0 < maxiter <= Int.max_unsigned)
  (HN : 0 < N < Int.max_unsigned)
  (yp : val)
  (FR1 : list mpred),
semax (func_tycontext f_jacobi2 Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _y yp; temp _z xp; temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; 
   temp _x xp; temp _acc (Vfloat acc);
   temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FRZL FR1; data_at_ shy (tarray tdouble N) yp;
   crs_rep shA2 (remove_diag A) A2p;
   data_at shA1 (tarray tdouble N)
     (map Vfloat (diag_of_matrix A)) A1p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at shx (tarray tdouble N) (map Vfloat x) xp))
  the_loop
  (normal_ret_assert
     (EX (n: nat) (z : vector Tdouble) (s : ftype Tdouble),
      PROP (RelProd feq (Forall2 feq) (s,z) (jacobi A b x acc (Z.to_nat maxiter)))
      LOCAL (temp _y (choose n xp yp); temp _z (choose n yp xp);
      temp _N (Vint (Int.repr (matrix_rows A))); gvars gv; 
      temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp; 
      temp _acc (Vfloat acc); temp _s (Vfloat s))
      SEP (FRZL FR1; 
         data_at_ (choose n shx shy) (tarray tdouble N) (choose n xp yp);
         crs_rep shA2 (remove_diag A) A2p;
         data_at shb (tarray tdouble N) (map Vfloat b) bp;
         data_at (choose n shy shx) (tarray tdouble N) (map Vfloat z) (choose n yp xp);
         data_at shA1 (tarray tdouble (matrix_rows A))
           (map Vfloat (diag_of_matrix A)) A1p))%argsassert).
Proof.
intros.
unfold the_loop.
assert (FINA2 := finite_remove_diag A COLS FINA).
subst N.
rewrite <- matrix_rows_remove_diag in *.
set (A2 := remove_diag A) in *.
set (N := matrix_rows A2) in *.
abbreviate_semax.
assert_PROP (Zlength b = N /\ Zlength x = N) as LENbx. {
  entailer!. clear - H4 H7; unfold matrix_rows in *; split;  list_solve.
}
destruct LENbx as [LENb LENx].
set (A1(*inv*) := (*invert_diagmatrix*) (diag_of_matrix A)) in *.
assert (LENA1(*inv*): Zlength A1(*inv*) = N). {
  unfold A1(*inv*), N, A2 (*, invert_diagmatrix*).
   rewrite ?Zlength_map, Zlength_diag_of_matrix, matrix_rows_remove_diag; auto.
}
assert (COLS2: matrix_cols A2 N). {
  subst A2 N. 
  rewrite matrix_rows_remove_diag in COLS|-*; apply matrix_cols_remove_diag; auto.
}
pose (f := jacobi_iter A1 A2 b).
assert (CONGR_f: forall x x', Zlength x = N -> Forall2 strict_feq x x' -> Forall2 feq (f x) (f x')). {
  intros. apply jacobi_iter_congr; auto. rewrite H; auto.
}
apply semax_loop_unroll1
 with (P' := (EX y:vector Tdouble, EX s:ftype Tdouble, 
  PROP (Forall2 feq y (f x);
          feq s (dist2 x y))
  LOCAL (temp _maxiter (Vint (Int.sub (Int.repr maxiter) (Int.repr 1)));
    temp _y xp; temp _z yp; temp _t xp; temp _s (Vfloat s);
    temp _A1 A1p; temp _N (Vint (Int.repr N)); 
    gvars gv; temp _A2 A2p; temp _b bp; 
    temp _x xp; temp _acc (Vfloat acc))
  SEP (data_at shA1 (tarray tdouble N) (map Vfloat A1) A1p;
        crs_rep shA2 A2 A2p;
        data_at shb (tarray tdouble N) (map Vfloat b) bp;
        data_at shx (tarray tdouble N) (map Vfloat x) xp;
        data_at shy (tarray tdouble N) (map Vfloat y) yp;
     FRZL FR1))%assert)
 (Q := (EX y:vector Tdouble, EX s:ftype Tdouble, 
  PROP (Forall2 feq y (f x); 
          feq s (dist2 x y);
          stop s acc = true; maxiter>1)
  LOCAL (temp _maxiter (Vint (Int.repr (maxiter -1)));
    temp _y xp; temp _z yp; temp _t xp; temp _s (Vfloat s);
    temp _A1 A1p; temp _N (Vint (Int.repr N)); 
    gvars gv; temp _A2 A2p; temp _b bp; 
    temp _x xp; temp _acc (Vfloat acc))
  SEP (data_at shA1 (tarray tdouble N) (map Vfloat A1) A1p;
        crs_rep shA2 A2 A2p;
        data_at shb (tarray tdouble N) (map Vfloat b) bp;
        data_at shx (tarray tdouble N) (map Vfloat x) xp;
        data_at shy (tarray tdouble N) (map Vfloat y) yp;
     FRZL FR1))%assert).
-
forward_call (shA1,shA2,shb,  shx, shy, A1p, A1, A2p, A2, bp, b, xp, x, yp).
Intros a; destruct a as [y s]. unfold fst,snd in H,H0|-*.
forward. forward. forward. forward.
Exists y s; entailer!!.
-
Intros y s.
forward_if (temp _t'3 (Val.of_bool (stop s acc))).
  { forward.
    entailer!!.
   change (Float.cmp Cgt s acc) with ((s>acc)%F64).
   unfold stop.
   replace (Binary.is_finite _ _ _) with true; auto.
   destruct s; try discriminate; reflexivity.
  } 
  { forward.
    entailer!!. unfold stop.
   replace (Binary.is_finite _ _ _) with false; auto.
   clear - H1.
   destruct s; try discriminate; try reflexivity.
  }
 rewrite sub_repr.
 forward_if (temp _t'4 (Val.of_bool (stop s acc &&  Z.gtb maxiter 1))).
  { forward. change 1024 with (femax Tdouble) in H1.  rewrite H1. 
    entailer!!. simpl andb.
    destruct (Z.gtb_spec maxiter 1).
    rewrite Int.eq_false. reflexivity.
   intro Hx. apply repr_inj_unsigned in Hx; try rep_lia.
   replace (maxiter - 1) with 0 by lia.
   rewrite Int.eq_true. reflexivity.
  }
  { change 1024 with (femax Tdouble) in H1.  rewrite H1.
    forward. entailer!!. rewrite H1. reflexivity.
  }
 forward_if.
 + forward. Exists y s. entailer!!.
   rewrite andb_true_iff in H1; destruct H1; auto.
 + forward. Exists 1%nat y s.
   entailer!!.
   unfold jacobi. fold A1. fold A2. fold f.
   destruct (Z.to_nat maxiter) eqn:?H; [ lia | ].
   simpl. 
   destruct n. simpl iter_stop. unfold fst, snd. split; auto.
   rewrite <- H; auto.
   rewrite andb_false_iff in H1.
   destruct H1; [ | lia].
   change 1024 with (femax Tdouble) in H1.
   iter_stop_S.
   rewrite H in H0.
  rewrite (stop_mor _ _ _ H0 _ _ FINacc) in H1. rewrite H1.
   split; auto.
-

Intros fx s.

forward_loop 
  (EX n:nat, EX y: vector Tdouble, EX s: ftype Tdouble,
   PROP (0 <= Z.of_nat n <= maxiter-1;
             option_rel (Forall2 feq) (iter_stop_n dist2 f n acc x) (Some y);
             Forall finite y)
   LOCAL (temp _A1 A1p; temp _y (choose n xp yp); temp _z (choose n yp xp);
   temp _N (Vint (Int.repr N)); gvars gv;
   temp _A2 A2p; temp _b bp; temp _x xp; temp _acc (Vfloat acc);
   temp _maxiter (Vint (Int.repr (maxiter- (Z.of_nat n))));
   temp _s (Vfloat s))
   SEP (FRZL FR1;
   data_at_ (choose n shx shy) (tarray tdouble N) (choose n xp yp); 
   crs_rep shA2 A2 A2p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at (choose n shy shx) (tarray tdouble N) (map Vfloat y) (choose n yp xp);
   data_at shA1 (tarray tdouble N)  (map Vfloat A1) A1p))%assert.
+
Exists (S O) fx s; entailer!!.
split.
simpl.
change (andb _ _) with (stop (dist2 x (f x)) acc).
 rewrite H in H0.
  rewrite (stop_mor _ _ _ H0 _ _ FINacc) in H1. rewrite H1.
 constructor.  symmetry; auto.
 unfold stop in H1. rewrite andb_true_iff in H1. destruct H1 as [? _].
 apply finite_is_finite in H1.
 rewrite H0 in H1.
 apply finite_dist2_e2 in H1; auto.
 symmetry. rewrite H. rewrite LENx. apply Zlength_jacobi_iter; auto.
+
clear dependent s.
Intros n y s.
inv H1. rename H4 into H1.
progress change float with (ftype Tdouble) in *.
rename H2 into FINy.
destruct (iter_stop_n dist2 f n acc x) eqn:?K; inv H1.
forward_call (shA1,shA2,shb, choose n shy shx, choose n shx shy,
                       A1p, A1, A2p, A2, bp, b, choose n yp xp,
                         y,   choose n xp yp).
unfold choose; destruct (Nat.odd n); auto.
clear s.
Intros a. destruct a as [fy s]. unfold fst, snd in *.
fold f in H1.
forward.
forward.
forward.
forward.
forward_if (temp _t'3 (Val.of_bool (stop s acc))).
  { forward. 
    entailer!!.
   change (Float.cmp Cgt ?s acc) with ((s>acc)%F64).
   unfold stop.
   replace (Binary.is_finite _ _ _) with true; auto.
   destruct s; try discriminate; reflexivity.
  } 
  { forward.
    entailer!!.
    unfold stop.
   replace (Binary.is_finite _ _ _) with false; auto.
    destruct s; try discriminate; try reflexivity.
  }
 rewrite sub_repr. rewrite <- Z.sub_add_distr.
 forward_if (temp _t'4 (Val.of_bool (stop s acc &&  Z.gtb maxiter (Z.of_nat n+1)))).
  { forward. rewrite H4. 
    entailer!!. 
    destruct (Z.gtb_spec maxiter (Z.of_nat n+1)).
    rewrite Int.eq_false. reflexivity.
    intro Hx; apply repr_inj_unsigned in Hx; rep_lia.
    replace (_ - _) with  0 by lia.
    rewrite Int.eq_true. reflexivity.
  }
  { rewrite H4.
    forward.
    rewrite H4. entailer!!.
  }
assert (LENv :=  K).
  apply iter_stop_n_Zlength with (N := matrix_rows A2) in LENv; auto.
  2: intros; unfold f; rewrite Zlength_jacobi_iter; auto.
assert (LENy : Zlength y = matrix_rows A2) by (rewrite <- H6; auto).
fold N in LENv, LENy |-*.
assert (EQyv: Forall2 strict_feq y v) by (apply strict_floatlist_eqv_i1; auto; symmetry; auto).

forward_if.
*
forward.
Exists (S n) fy s.
rewrite !choose_S.
entailer!!.
rewrite andb_true_iff in H4.
destruct H4.
destruct (Z.gtb_spec maxiter (Z.of_nat n + 1)); try discriminate. clear H5.
simpl.   

assert (FINs: finite s). {
  unfold stop in H4. rewrite andb_true_iff in H4. destruct H4.
   apply finite_is_finite; auto.
}
split3; [ | | f_equal; f_equal; lia].
-- simpl. rewrite K.
  change (andb _ _) with (stop (dist2 v (f v)) acc).
  rewrite <- H6 in H2.
  rewrite (CONGR_f  y v) in H1 by auto.
  rewrite H1 in H2.
  rewrite (stop_mor _ _ _ H2 _ _ FINacc) in H4 by auto. rewrite H4.
 constructor; symmetry; auto.
--
rewrite H2 in FINs.
apply finite_dist2_e2 in FINs; auto.
  rewrite H1. unfold f. rewrite Zlength_jacobi_iter; auto.
*
forward.
Exists (S n) fy s.
rewrite !choose_S.
entailer!!.
unfold jacobi. fold A1. fold A2. fold f.
destruct (stop s acc) eqn:?H.
--
apply iter_stop_n_lem2 in K; auto.
replace (pred _) with n by lia.
rewrite K.
split.
rewrite H1 in H2.
rewrite H2. apply dist2_mor; auto. symmetry; auto. rewrite H1; apply CONGR_f; auto.
   rewrite H1 in H2.
  rewrite (CONGR_f  y v) in H2 by auto. 
  rewrite <- H6 in H2.
  rewrite (stop_mor _ _ _ H2 _ _ FINacc) in H5. apply H5.
--
pose (k := (pred (Z.to_nat maxiter) - n)%nat).
apply iter_stop_n_lem1 with (k:=k) in K; auto.
replace (pred _) with (n+k)%nat by lia.
rewrite K.
rewrite H1. rewrite H2.
split.
apply dist2_mor; auto. symmetry; auto. rewrite H1.
apply CONGR_f; auto.
apply CONGR_f; auto.
  rewrite <- H6 in H2. rewrite H1 in H2.
  rewrite (CONGR_f y v) in H2; auto.
  rewrite (stop_mor _ _ _ H2 _ _ FINacc) in H5. apply H5.
Qed.

Lemma body_jacobi2: semax_body Vprog Gprog f_jacobi2 jacobi2_spec.
Proof.
start_function.
forward_call.
rewrite matrix_rows_remove_diag; lia.
forward.
rewrite matrix_rows_remove_diag.
set (N := matrix_rows A) in *.
forward_call (tarray tdouble N, gv).
  entailer!. simpl. do 3 f_equal.  rep_lia.
  simpl. rep_lia.
Intros yp.
freeze FR1 := (mem_mgr gv) (malloc_token _ _ _).
eapply semax_seq'.
eapply jacobi2_the_loop; try eassumption; auto.
Intros n z s.
abbreviate_semax.
thaw FR1.
fold N.
progress change float with (ftype Tdouble).
freeze FR2 := - ( data_at_ _ _ (choose n xp yp))
                         (data_at _ _ _ (choose n yp xp)).
apply semax_seq' with
 (PROP ( )
   LOCAL (temp _A1 A1p; temp _y yp;
   temp _N (Vint (Int.repr N)); 
   gvars gv; temp _A2 A2p; temp _b bp; 
   temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
   SEP (FRZL FR2; 
       data_at_ Ews (tarray tdouble N) yp;
       data_at Ews (tarray tdouble N)  (map Vfloat z) xp)).
-
 unfold choose. destruct (Nat.odd n) eqn:ODD;
 forward_if; try contradiction.
 + forward_for_simple_bound N
        (EX i:Z, (PROP ( )
             LOCAL (temp _A1 A1p; temp _y xp; temp _z yp;
                temp _N (Vint (Int.repr N)); gvars gv; 
                temp _A2 A2p; temp _b bp; 
                temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
            SEP (FRZL FR2; 
                     data_at Ews (tarray tdouble N) 
                          (sublist 0 i (map Vfloat z) ++ Zrepeat Vundef (N-i)) xp;
                     data_at Ews (tarray tdouble N) (map Vfloat z) yp)))%assert.
  * rewrite sublist_nil, app_nil_l. entailer!. apply derives_refl.
  * forward. forward. entailer!. apply derives_refl'; f_equal.
     progress change float with (ftype Tdouble) in *.
     clear - H9 H0 H15. rewrite Zlength_map in H15. simpl.
     forget (matrix_rows A) as N. list_solve.
  * forward. entailer!. list_solve.
 + forward. entailer!!. 
 + forward. entailer!!.
-
 thaw FR2.
 abbreviate_semax.
 forward_call free_spec_sub (yp, gv).
 saturate_local. destruct yp; try contradiction; simpl. cancel.
 forward.
 Exists z s.
 entailer!!.
Qed.



