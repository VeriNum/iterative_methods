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

Definition the_loop : statement.
let c := constr:(f_jacobi2) in
let c := eval red in c in 
match c with context [Sloop ?a ?b] => match a with context [Sset _maxiter] => idtac end;
 exact (Sloop a b)
end.
Defined.

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
assert (COLS2 :=  matrix_cols_remove_diag _ COLS).
assert (FINA1: Forall finite (diag_of_matrix A))
  by (apply diag_of_matrix_prop; auto).
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
set (A1 := diag_of_matrix A) in *.
assert (LENA1: Zlength A1 = N). {
  unfold A1, N, A2.
   rewrite ?Zlength_map, Zlength_diag_of_matrix, matrix_rows_remove_diag; auto.
}
pose (f := jacobi_iter A1 A2 b).
pose (resid := jacobi_residual A1 A2 b).
assert (f_Proper: Proper (Forall2 feq ==> Forall2 feq) f)
  by (apply jacobi_iter_mor_Proper; auto).
assert (resid_mor_Proper: Proper (Forall2 feq ==> Forall2 feq) resid)
  by (apply jacobi_residual_mor_Proper; auto).
apply semax_loop_unroll1
 with (P' := (EX y:vector Tdouble, EX s:ftype Tdouble, 
  PROP (Forall2 feq y (f x);
          feq s (norm2 (resid x)))
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
          feq s (norm2 (resid x));
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
   rewrite H0. rewrite H.
   unfold jacobi. fold A1. fold A2. fold f. fold resid.
   destruct (Z.to_nat maxiter) eqn:?H; [ lia | ].
   simpl. 
   destruct n. simpl iter_stop. reflexivity.
   iter_stop_S.
   rewrite andb_false_iff in H1.
   destruct H1; [ | lia].
   red in FINacc.
   rewrite (stop_mor _ _ _ H0 _ _ FINacc) in H1. (* BUG?  Why doesn't it 
                       work to simply write [rewrite H0 in H1] ? *)
   rewrite H1.
   reflexivity.
-
 Intros fx s.
 forward_loop 
  (EX n:nat, EX y: vector Tdouble, EX s: ftype Tdouble,
   PROP (0 <= Z.of_nat n <= maxiter-1;
             option_rel (Forall2 feq) (iter_stop_n norm2 resid f n acc x) (Some y);
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
 * simpl.
   change (andb _ _) with (stop (norm2 (resid x)) acc).
   rewrite (stop_mor _ _ _ H0 _ _ FINacc) in H1. rewrite H1.
   constructor.  symmetry; auto.
 * unfold stop in H1. rewrite andb_true_iff in H1. destruct H1 as [? _].
 apply finite_is_finite in H1.
 rewrite H0 in H1.
 apply finite_norm2_e in H1.
 apply finres_jacobi in H1; try (rewrite ?Zlength_jacobi_iter; lia).
 fold f in H1.
 symmetry in H.
 eapply Forall_Forall2; try apply H1. apply H.
 intros. rewrite H4 in H3; auto. 
+
clear dependent s.
Intros n y s.
inv H1. rename H4 into H1.
progress change float with (ftype Tdouble) in *.
rename H2 into FINy.
destruct (iter_stop_n norm2 resid f n acc x) eqn:?K; inv H1.
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
assert (LENv: Zlength v = N). {
  eapply iter_stop_n_Zlength in K; try eassumption.
   intros; unfold f; rewrite Zlength_jacobi_iter; auto.
   intros; apply f_Proper; eauto with typeclass_instances.
   intros; eapply finres_jacobi; eauto; rewrite ?Zlength_jacobi_iter; lia.
}
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
  change (andb _ _) with (stop (norm2 (resid v)) acc).
  fold resid in H2. rewrite <- H6 in H2. rewrite <- H6 in H1.
  rewrite (stop_mor _ _ _ H2 _ _ FINacc) in H4 by auto. rewrite H4.
 constructor; symmetry; auto.
--
 rewrite H2 in FINs.
 apply finite_norm2_e in FINs.
 apply finres_jacobi in FINs; try (rewrite ?Zlength_jacobi_iter; lia).
 fold f in FINs.
 symmetry in H1.
 eapply Forall_Forall2; try apply H1; auto.
 intros. rewrite H8 in H5; auto. 
*
forward.
Exists (S n) fy s.
rewrite !choose_S.
entailer!!.
unfold jacobi. fold A1. fold A2. fold f.
fold resid in H2|-*.
rewrite <- H6 in H1, H2.
rewrite (stop_mor _ _ _ H2 _ _ FINacc) in H4 by auto.
rewrite H1, H2.
destruct (stop (norm2 (resid v)) acc) eqn:?H.
--
apply iter_stop_n_lem2 in K; auto.
replace (pred _) with n by lia.
rewrite K. reflexivity.
--
pose (k := (pred (Z.to_nat maxiter) - n)%nat).
apply iter_stop_n_lem1 with (k:=k) in K; auto.
replace (pred _) with (n+k)%nat by lia.
rewrite K. reflexivity.
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


