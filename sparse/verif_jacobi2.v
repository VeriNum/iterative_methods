Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
From Iterative.sparse Require Import jacobi sparse_model spec_sparse 
         spec_jacobi fun_model_lemmas vst_improvements.
Require Import Iterative.jacobi_iteration_bound.
Import RelationPairs.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Require Import VSTlib.spec_malloc.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Import Morphisms.

Definition functional_model_correctness :=
 forall 
   (A : matrix Tdouble)
   (b : vector Tdouble)
   (acc : ftype Tdouble)
   (maxiter : Z)
   (LENb : Zlength b = matrix_rows A)
   (H4 : jacobi_preconditions A b acc (Z.to_nat (maxiter - 1)))
   (H6 : 0 < matrix_rows A)
   (H7 : 0 < maxiter)
   (H : matrix_cols A (matrix_rows A))
   (H11 : Forall (Forall finite) A)
   (H5 : Forall finite (invert_diagmatrix (diag_of_matrix A)))
   (H12 : Forall finite b)
   (H14 : finite (acc * acc)%F64)
   (y : vector Tdouble)
   (s : ftype Tdouble)
   (H15 : feq s
        (fst
           (jacobi A b (Zrepeat (Zconst Tdouble 0) (matrix_rows A)) 
              (acc * acc)%F64 (Z.to_nat maxiter))))
   (H18 : (Forall2 feq @@2)%signature (s, y)
        (jacobi A b (Zrepeat (Zconst Tdouble 0) (matrix_rows A)) 
           (acc * acc)%F64 (Z.to_nat maxiter))),
  feq s (norm2 (jacobi_residual (diag_of_matrix A) (remove_diag A) b y)) /\
  BCMP Lt true s (acc * acc)%F64 = true.

(*
Print All Dependencies functional_model_correctness.
Print All Dependencies ftype.
*)
Lemma functional_model_correct: functional_model_correctness.
Proof.
intro; intros.
destruct (jacobi_n_jacobi _ _ _ _ H4) as [j [? [FINs [LT ?]]]].
set (x0 := Zrepeat _ _) in *.
set (x0nat := repeat _ _) in *.
assert (x0nat = x0). {
  unfold x0, x0nat. rewrite <- repeat_Zrepeat.
  f_equal. rewrite Zlength_correct in LENb.
  rewrite <- LENb.
  rewrite Nat2Z.id. auto.
}
clearbody x0nat; subst x0nat.
pose proof (jacobi_returns_residual A b x0 (acc*acc)%F64 (Z.to_nat maxiter-1)).
replace (S _) with (Z.to_nat maxiter) in H2 by lia.
replace (S _) with (Z.to_nat maxiter) in LT by lia.
replace (S _) with (Z.to_nat maxiter) in FINs by lia.
destruct (jacobi A b x0 (acc*acc)%F64 (Z.to_nat maxiter)) as [r2 xj].
subst r2; simpl fst in *.
red in H18. simpl snd in H18.
split.
rewrite H15.
assert (Forall finite (diag_of_matrix A))
    by (apply diag_of_matrix_prop; auto).
apply norm2_mor.
apply jacobi_residual_mor; auto.
symmetry; auto.
rewrite <- H15 in FINs.
rewrite <- LT at 2.
apply BCMP_mor; auto.
apply feq_strict_feq; auto.
Qed.

Lemma subsume_jacobi2: funspec_sub (snd jacobi2_spec) (snd jacobi2_highspec).
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros s [? ?].
destruct s as [[[[[[[[[[[shA1 shA2] shb] A] A1p] A2p] bp] b] xp] acc] maxiter] gv].
Exists (shA1,shA2,shb,A,A1p,A2p,bp,b,xp,
           (Zrepeat (Zconst Tdouble 0) (matrix_rows A)),BMULT acc acc,maxiter,gv).
Exists emp.
Intros. clear H.
unfold_for_go_lower; normalize.
simpl.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
assert_PROP (Zlength b = matrix_rows A) as LENb. {
  saturate_local. apply prop_right. rewrite Zlength_map in H5;  auto.
}
decompose [and] H; clear H.
decompose [and] (jacobi_iteration_bound_corollaries _ _ _ _ H4).
rewrite !prop_true_andp; auto.
repeat split; auto.
rewrite <- repeat_Zrepeat; apply Forall_repeat; auto.
intros.
apply derives_extract_prop; intro.
Intros y s.
Exists y s.
rewrite !prop_true_andp; auto.
cancel.
destruct H15.
red in H15. simpl in H15.
apply and_assoc. split; auto.
eapply functional_model_correct; eassumption.
Qed.

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
  (FR1 : list mpred)
  (csr: csr_matrix Tdouble)
  (Hcsr : csr_to_matrix csr (remove_diag A)),
semax (func_tycontext f_jacobi2 Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _y yp; temp _z xp; temp _N (Vint (Int.repr N));
   gvars gv; temp _A1 A1p; temp _A2 A2p; temp _b bp; 
   temp _x xp; temp _acc (Vfloat acc);
   temp _maxiter (Vint (Int.repr maxiter)))
   SEP (FRZL FR1; data_at_ shy (tarray tdouble N) yp;
   csr_rep shA2 csr A2p;
   data_at shA1 (tarray tdouble N)
     (map Vfloat (diag_of_matrix A)) A1p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at shx (tarray tdouble N) (map Vfloat x) xp))
  the_loop
  (normal_ret_assert
     (EX (n: nat) (z : vector Tdouble) (fz: vector Tdouble) (s : ftype Tdouble),
      PROP (RelProd feq (Forall2 feq) (s,z) (jacobi A b x acc (Z.to_nat maxiter));
                Forall2 feq fz (jacobi_iter (diag_of_matrix A) (remove_diag A) b z))
      LOCAL (temp _y (choose n xp yp); temp _z (choose n yp xp);
      temp _N (Vint (Int.repr (matrix_rows A))); gvars gv; 
      temp _A1 A1p; temp _A2 A2p; temp _b bp; temp _x xp; 
      temp _acc (Vfloat acc); temp _s (Vfloat s))
      SEP (FRZL FR1; 
         data_at (choose n shx shy) (tarray tdouble N) (map Vfloat z) (choose n xp yp);
         csr_rep shA2 csr A2p;
         data_at shb (tarray tdouble N) (map Vfloat b) bp;
         data_at (choose n shy shx) (tarray tdouble N) (map Vfloat fz) (choose n yp xp);
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
        csr_rep shA2 csr A2p;
        data_at shb (tarray tdouble N) (map Vfloat b) bp;
        data_at shx (tarray tdouble N) (map Vfloat x) xp;
        data_at shy (tarray tdouble N) (map Vfloat y) yp;
     FRZL FR1))%assert)
 (Q := (EX y:vector Tdouble, EX s:ftype Tdouble, 
  PROP (Forall2 feq y (f x); 
          feq s (norm2 (resid x));
          going s acc = true; maxiter>1)
  LOCAL (temp _maxiter (Vint (Int.repr (maxiter -1)));
    temp _y xp; temp _z yp; temp _t xp; temp _s (Vfloat s);
    temp _A1 A1p; temp _N (Vint (Int.repr N)); 
    gvars gv; temp _A2 A2p; temp _b bp; 
    temp _x xp; temp _acc (Vfloat acc))
  SEP (data_at shA1 (tarray tdouble N) (map Vfloat A1) A1p;
        csr_rep shA2 csr A2p;
        data_at shb (tarray tdouble N) (map Vfloat b) bp;
        data_at shx (tarray tdouble N) (map Vfloat x) xp;
        data_at shy (tarray tdouble N) (map Vfloat y) yp;
     FRZL FR1))%assert).
-
forward_call (shA1,shA2,shb,  shx, shy, A1p, A1, A2p, A2, csr, bp, b, xp, x, yp).
Intros a; destruct a as [y s]. unfold fst,snd in H,H0|-*.
forward. forward. forward. forward.
Exists y s; entailer!!.
-
Intros y s.
forward_if (temp _t'3 (Val.of_bool (going s acc))).
  { forward.
    entailer!!.
   change (Float.cmp Cge s acc) with ((s>=acc)%F64).
   unfold going.
   replace (Binary.is_finite _ _ _) with true; auto.
   simpl.
   unfold Val.of_bool, bool2val.
   destruct (s >= acc)%F64; try reflexivity.
   destruct s; try discriminate; reflexivity.
  } 
  { forward.
    entailer!!. unfold going.
   replace (Binary.is_finite _ _ _) with false; auto.
   clear - H1.
   destruct s; try discriminate; try reflexivity.
  }
 rewrite sub_repr.
 forward_if (temp _t'4 (Val.of_bool (going s acc &&  Z.gtb maxiter 1))).
  { destruct (going s acc); try discriminate.
    forward.
    entailer!!.
    simpl andb.
    destruct (Z.gtb_spec maxiter 1).
    rewrite Int.eq_false. reflexivity.
   intro Hx. apply repr_inj_unsigned in Hx; try rep_lia.
   replace (maxiter - 1) with 0 by lia.
   rewrite Int.eq_true. reflexivity.
  }
  { destruct (going s acc); try discriminate.
    forward. entailer!!. 
  }
 forward_if.
 + forward. Exists y s.
   destruct (going s acc); try discriminate.
   simpl in H1.
   entailer!!.
   apply Z.gtb_gt. destruct (maxiter >? 1); auto; discriminate.
 + forward. Exists 1%nat x y s.
   entailer!!.
   rewrite H0.
   unfold jacobi. fold A1. fold A2. fold f. fold resid.
   destruct (Z.to_nat maxiter) eqn:?H; [ lia | ].
   simpl. 
   destruct n. simpl iter_stop. reflexivity.
   iter_stop_S.
   replace (going _ acc) with (going s acc) by (rewrite H0; auto).
   destruct (going s acc); [ | reflexivity].
   destruct (maxiter >? 1) eqn:?H; try discriminate.
   lia.
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
   csr_rep shA2 csr A2p;
   data_at shb (tarray tdouble N) (map Vfloat b) bp;
   data_at (choose n shy shx) (tarray tdouble N) (map Vfloat y) (choose n yp xp);
   data_at shA1 (tarray tdouble N)  (map Vfloat A1) A1p))%assert.
+
Exists (S O) fx s; entailer!!.
split.
 * simpl.
   rewrite H0 in H1. rewrite H1.
   constructor.  symmetry; auto.
 * unfold going in H1. rewrite andb_true_iff in H1. destruct H1 as [? _].
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
                       A1p, A1, A2p, A2, csr, bp, b, choose n yp xp,
                         y,   choose n xp yp).
unfold choose; destruct (Nat.odd n); auto.
clear s.
Intros a. destruct a as [fy s]. unfold fst, snd in *.
fold f in H1.
forward.
forward.
forward.
forward.
forward_if (temp _t'3 (Val.of_bool (going s acc))).
  { forward. 
    entailer!!.
   change (Float.cmp Cge ?s acc) with ((s>=acc)%F64).
   unfold going.
   replace (Binary.is_finite _ _ _) with true; auto.
   simpl.
   unfold Val.of_bool, bool2val.
   destruct (s >= acc)%F64; try reflexivity.
   destruct s; try discriminate; reflexivity.
  } 
  { forward.
    entailer!!.
    unfold going.
   replace (Binary.is_finite _ _ _) with false; auto.
    destruct s; try discriminate; try reflexivity.
  }
 rewrite sub_repr. rewrite <- Z.sub_add_distr.
 forward_if (temp _t'4 (Val.of_bool (going s acc &&  Z.gtb maxiter (Z.of_nat n+1)))).
  { forward.
    destruct (going s acc); try discriminate.
    entailer!!. 
    destruct (Z.gtb_spec maxiter (Z.of_nat n+1)).
    rewrite Int.eq_false. reflexivity.
    intro Hx; apply repr_inj_unsigned in Hx; rep_lia.
    replace (_ - _) with  0 by lia.
    rewrite Int.eq_true. reflexivity.
  }
  { 
    destruct (going s acc); try discriminate.
    forward.
    entailer!!.
  }

assert (LENv: Zlength v = N). {
  eapply iter_stop_n_Zlength in K; try eassumption.
   intros; unfold f; rewrite Zlength_jacobi_iter; auto.
   intros; apply f_Proper; eauto with typeclass_instances.
   intros; eapply finres_jacobi; eauto; rewrite ?Zlength_jacobi_iter; lia.
}

assert (LENy : Zlength y = matrix_rows A2)
 by (rewrite <- H6; auto).
fold N in LENv, LENy |-*.

assert (EQyv: Forall2 strict_feq y v) by (apply strict_floatlist_eqv_i1; auto; symmetry; auto).

forward_if.
*
forward.
Exists (S n) fy s.
rewrite !choose_S.
entailer!!.
destruct (going s acc) eqn:GOING; try discriminate.
destruct (Z.gtb_spec maxiter (Z.of_nat n + 1)); try discriminate.
clear H4.
simpl.
assert (FINs: finite s). {
  unfold going in GOING. rewrite andb_true_iff in GOING. destruct GOING.
   apply finite_is_finite; auto.
}
fold resid in H2.
split3; [ lia | | split; [ | f_equal; f_equal; lia]].
--
rewrite <- H6 in H2. rewrite H2 in GOING.

apply iter_stop_n_S in K; auto.
simpl in K.
destruct (going (norm2 (resid x)) acc); inv K.
rewrite H7. constructor.
rewrite <- H6 in H1. rewrite H1; auto.
-- 
 rewrite H1.
 rewrite H2 in FINs. 
 apply finite_norm2_e in FINs.
 apply finres_jacobi in FINs.
 auto.
 congruence. 
 rewrite Zlength_jacobi_iter; try lia.
*
forward.
Exists (S n) y fy s.
rewrite !choose_S.
entailer!!.
unfold jacobi. fold A1. fold A2. fold f.
fold resid in H2|-*.
rewrite <- H6 in H1, H2|-*.
rewrite H2 in H4|-*.
destruct (going (norm2 (resid v)) acc) eqn:?H.
--
apply iter_stop_n_lem2 in K; auto.
destruct (maxiter >? Z.of_nat n + 1) eqn:?H; try discriminate.
replace (Nat.pred _) with n by lia.
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
unfold csr_rep_abstract. 
Intros csr. rename H7 into Hcsr.
forward_call (shA2,A2p, remove_diag A,csr).
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
Intros n z fz s.
abbreviate_semax.
thaw FR1.
fold N.
progress change float with (ftype Tdouble).
freeze FR2 := - ( data_at _ _ _ (choose n xp yp))
                         (data_at _ _ _ (choose n yp xp)).
apply semax_seq' with
 (PROP ( )
   LOCAL (temp _A1 A1p; temp _y yp;
   temp _N (Vint (Int.repr N)); 
   gvars gv; temp _A2 A2p; temp _b bp; 
   temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
   SEP (FRZL FR2; 
       data_at Ews (tarray tdouble N)  (map Vfloat z) xp;
       data_at_ Ews (tarray tdouble N) yp)).
-
 assert_PROP (Zlength z = N /\ Zlength fz = N) as LEN
  by (entailer!; rewrite Zlength_map in*; auto).
 destruct LEN as [LENz LENfz].
 unfold choose. destruct (Nat.odd n) eqn:ODD;
 forward_if; try contradiction.
 + forward. entailer!!.
 + forward. entailer!!.
 + forward_for_simple_bound N
        (EX i:Z, (PROP ( )
             LOCAL (temp _A1 A1p; temp _y yp; temp _z xp;
                temp _N (Vint (Int.repr N)); gvars gv; 
                temp _A2 A2p; temp _b bp; 
                temp _x xp; temp _acc (Vfloat acc); temp _s (Vfloat s))
            SEP (FRZL FR2; 
                     data_at Ews (tarray tdouble N) 
                          (sublist 0 i (map Vfloat z) ++ sublist i N (map Vfloat fz)) xp;
                     data_at Ews (tarray tdouble N) (map Vfloat z) yp)))%assert.
  * rewrite sublist_nil, app_nil_l. entailer!. rewrite sublist_same by list_solve. apply derives_refl.
  * forward. forward. entailer!!. apply derives_refl'; f_equal.
     progress change float with (ftype Tdouble) in *.
     set (N := matrix_rows A).
     rewrite (sublist_split 0 i (i+1)) by list_solve.
     rewrite (sublist_split i (i+1) N) by list_solve.
     list_solve. list_simplify.
     replace (i0 - i + i) with i by lia. reflexivity.
  * entailer!!. apply derives_refl'. f_equal.
     rewrite sublist_nil. rewrite sublist_same by list_solve.
     list_solve. 
-
 thaw FR2.
 abbreviate_semax.
 forward_call free_spec_sub (yp, gv).
 saturate_local. destruct yp; try contradiction; simpl. cancel.
 forward.
 Exists z s.
 entailer!!.
 unfold csr_rep_abstract; Exists csr; entailer!!. 
Qed.



