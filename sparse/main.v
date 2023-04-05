Require Import VST.floyd.proofauto.
From Iterative Require Import floatlib jacob_list_fun_model.
Require Import Iterative.sparse.fun_model_lemmas.
Print Assumptions jacobi_n_jacobi.
From Iterative.sparse Require Import jacobi spec_sparse spec_jacobi verif_jacobi2 (* jacobi sparse_model spec_sparse 
         spec_jacobi fun_model_lemmas vst_improvements *).



Lemma main_jacobi: semax_body Vprog Gprog f_jacobi2 jacobi2_highspec.
Proof.
eapply semax_body_funspec_sub.
apply body_jacobi2.
apply subsume_jacobi2.
apply compute_list_norepet_e; reflexivity.
Qed.

Print Assumptions main_jacobi.

(*

Axioms required for the real numbers and functional-model-accuracy proofs:

ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~~P} + {~P}
ClassicalDedekindReals.sig_forall_dec
  : forall P : nat -> Prop,
    (forall n : nat, {P n} + {~P n}) -> {n : nat | ~P n} + {forall n : nat, P n}
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Epsilon.epsilon_statement
  : forall (A : Type) (P : A -> Prop),
    inhabited A -> {x : A | (exists x0 : A, P x0) -> P x}
Classical_Prop.classic : forall P : Prop, P \/ ~P

Classical axioms used in the VST proof:

Ensembles.Extensionality_Ensembles
  : forall (U : Type) (A B : Ensembles.Ensemble U), Ensembles.Same_set A B -> A = B
prop_ext : ClassicalFacts.prop_extensionality
Axioms.prop_ext : ClassicalFacts.prop_extensionality
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h

Additional axioms used in the VST proof; the first one of these is straightforward
 and ought to be proved in the next release of VST; the second and third are
 axiomatizations of certain C library functions (fma and malloc/free):

vst_improvements.clean_LOCAL_right_spec_bangbang
  : forall (gvar_ident : list ident) (Delta : tycontext) 
      (T1 : Maps.PTree.t val) (T2 : Maps.PTree.t (Ctypes.type * val))
      (GV : option globals) (P : list Prop) (Q : list localdef) 
      (R : list mpred) (S : mpred.environ -> mpred) (S' : mpred),
    fold_right andb true (map (legal_glob_ident Delta) gvar_ident) = true ->
    local2ptree Q = (T1, T2, [], GV) ->
    clean_LOCAL_right Delta T1 T2 GV S S' ->
    (ENTAIL Delta, PROPx P (RETURN ( ) (SEPx R))%assert3 |-- liftx S') ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- S
spec_math.c_function
  : forall (i : ident) (args : list type) (res : type)
      (f : klist.function_type (map RR args) R),
    {ff : klist.function_type (map ftype' args) (ftype res)
    | acc_prop args res (1 + 2 * spec_math.GNU_error i) 1
        (spec_math.vacuous_bnds_klist args) f ff}
M : spec_malloc.MallocAPD

*)

