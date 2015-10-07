(* (c) Copyright ? *)

(*****************************************************************************
  Verification of formula deductions in paper "Exact-Wiberg Algorithm for 
  Matrix Factorization with Missing Data" (ECCV 2014 submission)

  Main definitions:
        C :  ringType. Type of constants.
        E :  unitComAlgType C. Type of variables and matrix elements.
        D :  comBimodType E. The co-domain of differentiation operator.
       \d :  {linearDer E -> D}. The differentiation operator (derivation)
             on elements.
      \\d :  Matrix differentiation, which is just element-wise 
             differentiation.
    m n r :  non-zero natural numbers
      W M :  'M[E]_(m,n). The weight and target matrix in the matrix 
             decomposition problem. They are lifted from 'M[C]_(m,n), 
             so they are constant.
        U :  'M[E]_(m,r)
        v :  C
       ~W == diag_mx (vec W)^T
       \m == vec M
       ~U == I *ol U
     eps1 == ~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m
        H == I - ~W *m ~U *m (~W *m ~U)^-v
       V* == (cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T
    R == W .* (M - U *m V*^T)
      ~V* == V* *o I
        T == trT _ _ _. The permutation matrix for transposing.
       v* == (~W *m ~U)^-v *m ~W *m \m
      ~WR == (W .* R) *o I
      A^+ == A^-0
       J1 == -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)
             The Jacobian matrix of eps1
       J2 == 0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + 
             ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m 
             ((W .* R)^T *o I) *m T.
             The Jacobian matrix of v*

  Main results: 
    vec_dot : forall V,
      vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T
      Corresponds to Equation (10)~(13)

    d_eps1_part1 : 
      \\d eps1 = 0 - H *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) - 
                ((~W *m ~U)^-v)^T *ml (I *ol (\\d U)^T) *mr (~W^T *m H *m ~W *m \m)
      Corresponds to Equation (20)~(26)

    to_vec_dot : 
      ~W^T *m H *m ~W *m \m = vec (W .* R)
      Corresponds to Equation (28)~(31) 

    d_eps1 : 
      \\d eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) 
                 *ml \\d (vec U)
      Corresponds to Equation (32)~(34) 

    d_vstar_part1 : 
      \\d v* = 0 - (~W *m ~U)^-v *m ~W *ml (I *ol \\d U) *mr 
               ((~W *m ~U)^-v *m ~W *m \m) + 
               ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *ml 
               (I *ol \\d U)^T *mr (~W^T *m (I - (~W *m ~U) *m (~W *m ~U)^-v) 
               *m ~W *m \m)
      Corresponds to Equation (36)~(40)

    d_vstar_part2 : 
      \\d v* = (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T) *ml vec (\\d U)
      Corresponds to Equation (40')~(48) 

    J2_simpl : 
      J2 = 0 - ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)
      Corresponds to Equation (49)~(52) 

    d_vstar : 
      \\d v* = - (((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)) *ml \\d (vec U)
      direct corollary from d_vstar_part2 and J2_simpl

    J1_J1 : 
      J1^T *m J1 = ~V*^T *m ~W^T *m H *m ~W *m ~V* + T^T *m ~WR *m ((~W *m ~U)^T *m (~W *m ~U))^^-1 *m ~WR^T *m T
      Corresponds to Equation (54)~(56) 

    J1_eps1 : 
      -J1^T *m eps1 = ~V*^T *m ~W^T *m H *m ~W *m \m
      Corresponds to Equation (57)~(58) 

    d_eps1_UV : 
      \\d eps1_UV = 0 - ~W *m ~U *ml \\d (vec V^T) - ~W *m (V *o I) *ml \\d (vec U)
      Corresponds to Equation (60)~(62) where
        V : 'M[E]_(n, r)
        eps1_UV == vec (W .* (M - U *m V^T))


  When instantiate the previous results with the following instantiation:
        p == r * m. The number of free variables (which is also the 
             number of elements of U).
        E :  funType p C. Single-value functions on C with up-to p arity.
             The vector of the p free variables are denoted as \x.
       \d :  {gradient E}. A gradient operator on E. This is where
             the Jacobian matrix is defined.
        U == cvec_mx \x. 
             (vec U) is the basis vector of the free variables, with 
             regard to which we want to compute the Jacobian matrices.
       \J == Jacob \d. The Jacobian matrix operator from \d.

  With this instantiation, we then have the following results:
    J_eps1 : 
      \J eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)

    J_vstar : 
      \J v* = -(((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m 
              ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T))

  All results are under the assumption: invertible (mupinv_core v (~W *m ~U)).
  Sometimes I write (0 - a *m b) instead of (- a *m b) because the unary minus 
  sign binds tighter than *m, which I find counter-intuitive.

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import matrix.
Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import bimodule.
Require Import derivation.
Require Import mxutil.
Import Notations.
Require Import mxmodule.
Import Notations.
Require Import mxdiff.
Import Notations.
Require Import example_appendix.
Import Notations.

Section Section3.

(* Constants *)
Variable C : ringType.
(* Variables and matrix elements *)
Variable E : unitComAlgType C.
(* Co-domain of differentiation operator *)
Variable D : comBimodType E.
Variable der : {linearDer E -> D}.
Notation "\d" := (LinearDer.apply der).
Notation "\\d" := (map_mx \d).

(* All dimensions are non-zero. All matrices are non-empty. *)
Variable m' n' r' : nat.
Local Notation m := m'.+1.
Local Notation n := n'.+1.
Local Notation r := r'.+1.

(* W : weight matrix 
   M : target matrix 
   They are constant matrices, and are lifted to participate in matrix operations.
*)
Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
Variable U : 'M[E]_(m, r).
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).
(* Regularization rate *)
Variable v : C.
Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).
Notation R := (W .* (M - U *m V*^T)).
Notation "~V*" := (V* *o I).
(* The permutation matrix for transposing *)
Notation T := (trT _ _ _).
Notation "v*" := ((~W *m ~U)^-v *m ~W *m \m).
Notation J2 := (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T).
Notation J1 := (-(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)).
Notation "~WR" := ((W .* R) *o I).

Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).

(* Corresponds to Equation (10)~(13) *)
Lemma vec_dot V : vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  rewrite !raddfB /=.
  by rewrite vec_kron !mulmxA.
Qed.

Lemma dmmr {p} (A : 'M[E]_(p, _)) : \\d (A *m \m) = \\d A *mr \m.
Proof.
  by rewrite -!lift_vec !dmcr.
Qed.

Lemma dmWr {p} (A : 'M[E]_(p, _)) : \\d (A *m ~W) = \\d A *mr ~W.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcr.
Qed.

Lemma dmWl {p} (A : 'M[E]_(_, p)) : \\d (~W *m A) = ~W *ml \\d A.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcl.
Qed.

(* Corresponds to Equation (20)~(26) *)
Lemma d_eps1_part1 : \\d eps1 = 0 - H *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) - ((~W *m ~U)^-v)^T *ml (I *ol (\\d U)^T) *mr (~W^T *m H *m ~W *m \m).
Proof.
  set goal := RHS.
  rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx.
  rewrite (dm_AmupinvA _ h_invertible). (* (22) *)
  rewrite dmWl (dm_lkron1mx _ _ U) !lmulmxA /=. (* (25) *)
  by rewrite /sym [in _^T + _]addrC !trmx_rmulmx !trmx_lmulmx !trmx_mul /= (trmx_lkron I (\\d U)) raddfB /= AmupinvA_sym !trmx1 !rmulmxDl opprD addrA !lrmulmxA !rmulmxA -!rmulmxA !mulmxA.
Qed.

Lemma to_Vstar : (~W *m ~U)^-v *m ~W *m \m = vec V*^T.
Proof.
  by rewrite (trmxK V*) cvec_mxK.
Qed.

(* Corresponds to Equation (28)~(31) *)
Lemma to_vec_dot : ~W^T *m H *m ~W *m \m = vec (W .* R).
Proof.
  set goal := RHS.
  rewrite mulmxBr !mulmxBl !mulmxA mulmx1.
  rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m) to_Vstar.
  rewrite -!mulmxA -mulmxBr !mulmxA -vec_dot.
  by rewrite tr_diag_mx -vec_elemprod.
Qed.

(* Corresponds to Equation (32)~(34) *)
Lemma d_eps1 : \\d eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) *ml \\d (vec U).
Proof.
  set goal := RHS.
  rewrite d_eps1_part1 to_vec_dot {1}to_Vstar.
  by rewrite -!lrmulmxA !lkron_shift (trmxK V*) !lmulmxA -trTPcrmul !lmulmxA sub0r -opprD -!(lmulmxDl _ _ (vec (\\d U))) -(map_vec _ U) -(lmulNmx _ (\\d _)).
Qed.

Lemma dmWTr {p} (A : 'M[E]_(p, _)) : \\d (A *m ~W^T) = \\d A *mr ~W^T.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx  map_trmx !dmcr.
Qed.

(* Corresponds to Equation (36)~(40) *)
Lemma d_vstar_part1 : \\d v* = 0 - (~W *m ~U)^-v *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *ml (I *ol \\d U)^T *mr (~W^T *m (I - (~W *m ~U) *m (~W *m ~U)^-v) *m ~W *m \m).
Proof.
  set goal := RHS.
  rewrite dmmr dmWr.
  rewrite (dm_mupinv _ h_invertible) 2!rmulmxDl 2!rmulmxBl !rmul0mx.
  by rewrite (map_trmx \d) trmx_mul dmWl dmWTr -(map_trmx \d) !(dm_lkron1mx _ _ U) /= !lrmulmxA !lmulmxA -!rmulmxA !mulmxA -trmx_mul -[in _^T *m _ *m _]mulmxA.
Qed.

(* Corresponds to Equation (40')~(48) *)
Lemma d_vstar_part2 : \\d v* = (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T) *ml vec (\\d U).
Proof.
  set goal := RHS.
  rewrite d_vstar_part1 trmx_lkron trmx1.
  rewrite to_Vstar to_vec_dot.
  rewrite -!lrmulmxA !lkron_shift (trmxK V*) !lmulmxA.
  by rewrite -trTPcrmul !lmulmxA sub0r addrC -!(lmulmxBl _ _ (vec (\\d U))) addrC -sub0r.
Qed.

(* Corresponds to Equation (49)~(52) *)
Lemma J2_simpl : J2 = 0 - ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T).
Proof.
  set goal := RHS.
  rewrite -{1}fold_mupinv sub0r addrC -opprB -!(mulmxA _^^-1) -mulmxBr.
  by rewrite [in _ - _]trmx_mul [in ~U^T]trmx_kron trmx1 -sub0r.
Qed.

Lemma d_vstar : \\d v* = - (((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)) *ml \\d (vec U).
Proof.
  set goal := RHS.
  by rewrite d_vstar_part2 J2_simpl sub0r -(map_vec _ U).
Qed.

Hypothesis v_0 : v = 0.

Notation "A ^+" := (A^-0) (at level 3, format "A ^+").

Lemma mulpinvmx m n (A : 'M[E]_(m,n)) : invertible (mupinv_core 0 A) -> A^+ *m A = I.
Proof.
  rewrite unlock /mupinv /mupinv_core lscale0mx addr0.
  by move => h; rewrite -(mulmxA _^^-1) mulVmx.
Qed.

Lemma pinv_pinv m n (A : 'M[E]_(m,n)) : invertible (mupinv_core 0 A) -> A^+ *m A^+^T = (A^T *m A)^^-1.
Proof.
  move => h.
  by rewrite [in _^+^T]unlock /mupinv /mupinv_core /= lscale0mx addr0 !trmx_mul !trmxK !mulmxA (mulpinvmx h) mul1mx trmx_inv !trmx_mul !trmxK.
Qed.

Lemma pinvWU_WU : (~W *m ~U)^+ *m ~W *m ~U = I.
Proof.
  move: h_invertible; rewrite v_0 => h.
  by rewrite -mulmxA (mulpinvmx h).
Qed.

Lemma WU_H_0 : (~W *m ~U)^+ *m H = 0.
Proof.
  by rewrite mulmxBr mulmx1 !mulmxA pinvWU_WU mul1mx v_0 addrN.
Qed.

Lemma trmx_kronmx1 (R : comRingType) m1 n1 m2 (A : 'M[R]_(m1,n1)) : (A *o I)^T = A^T *o (I : 'M_m2).
Proof. by rewrite trmx_kron trmx1. Qed.

Lemma J1_simpl : J1 = -(H *m ~W *m ~V* + ((~W *m ~U)^+)^T *m ~WR^T *m T).
Proof.
  set goal := RHS.
  by rewrite [in (_^-v)^T]v_0 -[in (W .* R)^T *o _]trmx_kronmx1.
Qed.

Lemma H_H : H^T *m H = H.
Proof.
  by rewrite !raddfB /= AmupinvA_sym !trmx1 mulmx1 mulmxBl mul1mx -!mulmxA ![in _^-v *m _]mulmxA v_0 pinvWU_WU !mulmxA !mulmx1 addrN subr0.
Qed.

Lemma pinvWU_pinvWU : (~W *m ~U)^+ *m (~W *m ~U)^+^T = ((~W *m ~U)^T *m (~W *m ~U))^^-1.
Proof.
  move: h_invertible; rewrite v_0 => h.
  by rewrite (pinv_pinv h).
Qed.

(* This notation works better with Latex *)
Notation "{( A )^+}" := (A^-0) (at level 3).

(* Corresponds to Equation (54)~(56) *)
Lemma J1_J1 : J1^T *m J1 = ~V*^T *m ~W^T *m H *m ~W *m ~V* + T^T *m ~WR *m ((~W *m ~U)^T *m (~W *m ~U))^^-1 *m ~WR^T *m T.
Proof.
  set goal := RHS.
  rewrite J1_simpl [in _^T] raddfN /= mulNmx mulmxN opprK [in _^T] raddfD /= !trmx_mul (trmxK ~WR) (trmxK _^+) [_ *m (_ + _)]mulmxDl mulmxDr mulmxDr !mulmxA !addrA.
  rewrite -!(mulmxA _ _ H) WU_H_0 -!(mulmxA _ _ _^+^T) -[H^T *m _^+^T]trmx_mul WU_H_0 !mulmxA trmx0 !mulmx0 !mul0mx !addr0.
  by rewrite -!(mulmxA _ _ H) H_H -(mulmxA _ _ _^+^T) pinvWU_pinvWU.
Qed.

(* Corresponds to Equation (57)~(58) *)
Lemma J1_eps1 : -J1^T *m eps1 = ~V*^T *m ~W^T *m H *m ~W *m \m.
Proof.
  set goal := RHS.
  rewrite -mulmxBl -mulmx1Bl J1_simpl raddfN /= opprK raddfD /= !trmx_mul (trmxK ~WR) (trmxK _^+) !mulmxA !mulmxDl.
  by rewrite -!(mulmxA _ _ H) H_H -!(mulmxA _ _ H) WU_H_0 !mulmx0 !mul0mx !addr0 !mulmxA.
Qed.

Variable V : 'M[E]_(n, r).
Notation eps1_UV := (vec (W .* (M - U *m V^T))).

(* Corresponds to Equation (60)~(62) *)
Lemma d_eps1_UV : \\d eps1_UV = 0 - ~W *m ~U *ml \\d (vec V^T) - ~W *m (V *o I) *ml \\d (vec U).
Proof.
  set goal := RHS.
  rewrite vec_elemprod !raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx dmWl.
  by rewrite vec_kron dmM /= (dm_lkron1mx _ _ U) /= lkron_shift [in _ *o _](trmxK V) -(map_vec _ U) lmulmxDr !lmulmxA [in _ *ml _ + _]addrC opprD addrA.
Qed.

End Section3.

Require Import nfun.

Section Jacobian.

(* All dimensions are non-zero. All matrices are non-empty. *)
Variable m' n' r' : nat.
Notation m := m'.+1.
Notation n := n'.+1.
Notation r := r'.+1.
(* The number of free variables, which is the number of elements of U *)
Notation p := (r * m)%nat.

Variable C : ringType.
Variable E : funType p C.
Variable d : {gradient E}.
Notation "\d" := (Gradient.apply d).
Notation "\\d" := (map_mx \d).

Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
(* (vec U) is the basis vector of the free variables *)
Definition  U : 'M[E]_(m, r) := cvec_mx \x.
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).
Variable v : C.
Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).
Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).
Notation R := (W .* (M - U *m V*^T)).
Notation "~V*" := (V* *o I).
Notation T := (trT _ _ _).

Notation "\J" := (Jacob \d).

Lemma J_eps1 : \J eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T).
Proof.
  by apply jacob_intro; rewrite (d_eps1 _ _ h_invertible) cvec_mxK.
Qed.

Notation "v*" := ((~W *m ~U)^-v *m ~W *m \m).

Lemma J_vstar : \J v* = -(((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)).
Proof.
  by apply jacob_intro; rewrite (d_vstar _ _ h_invertible) cvec_mxK.
Qed.

End Jacobian.

Section Section4.

(* All dimensions are non-zero. All matrices are non-empty. *)
Variable m' n' r' : nat.
Notation m := m'.+1.
Notation n := n'.+1.
Notation r := r'.+1.
(* The number of free variables, which is the number of elements of U and V *)
Notation p := (r * m + n * r)%nat.

Variable C : ringType.
Variable E : funType p C.
Variable d : {gradient E}.
Notation "\d" := (Gradient.apply d).
Notation "\\d" := (map_mx \d).

Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
Variable U : 'M[E]_(m, r).
Variable V : 'M[E]_(n, r).
(* Now both U and V are the free variables *)
Hypothesis UV_x : col_mx (vec U) (vec V^T) = \x.
Notation "~W" := (diag_mx (vec W)^T).
Notation "~U" := (I *o U).
Notation "~V" := (V *o I).
Notation eps := (vec (W .* (M - U *m V^T))).
Notation H a := (I - ~W *m ~U *m (~W *m ~U)^-a).
Notation "\J" := (Jacob \d).

Lemma J_eps : \J eps = - row_mx (~W *m ~V) (~W *m ~U).
Proof.
  apply jacob_intro.
  rewrite -UV_x d_eps1_UV /=.
  symmetry; set goal := RHS.
  by rewrite map_col_mx lmulNmx lmul_row_col addrC opprD -sub0r.
Qed.

Variable lambda : C.
Notation J := (\J eps).
Variable delta : 'cV[E]_p.
Hypothesis Levenberg : (J^T *m J + lambda *ml: I) *m delta = -J^T *m eps.
Variable dU : 'M[E]_(m, r).
Variable dV : 'M[E]_(n, r).
Hypothesis UV_delta : col_mx (vec dU) (vec dV^T) = delta.

Lemma JT_J_I : J^T *m J + lambda *ml: I = block_mx (~V^T *m ~W^T *m ~W *m ~V + lambda *ml: I) (~V^T *m ~W^T *m ~W *m ~U) (~U^T *m ~W^T *m ~W *m ~V) (~U^T *m ~W^T *m ~W *m ~U + lambda *ml: I).
Proof.
  set goal := RHS.
  rewrite J_eps !raddfN /= mulNmx opprK tr_row_mx mul_col_row scalar_mx_block lscale_block_mx add_block_mx !lscalemx0 !addr0.
  by subst goal; rewrite !trmx_mul !mulmxA.
Qed.

Lemma H_sym a : (H a)^T = H a.
Proof.
  by rewrite raddfB /= AmupinvA_sym trmx1.
Qed.

Hypothesis h_invertible : invertible (mupinv_core lambda (~W *m ~U)).

Lemma futher_damping_U : (~V^T *m ~W^T *m H lambda *m ~W *m ~V + lambda *ml: I) *m vec dU = ~V^T *m ~W^T *m (H lambda)^T *m eps.
Proof.
  set goal := _ = _.
  move: Levenberg.
  rewrite JT_J_I -UV_delta [in J^T]J_eps -raddfN /= opprK tr_row_mx [in R in _ =  R] mul_col_mx.
  move => h; pose (Schur_complement h).
  edestruct a as [h1 h2].
  by move: h_invertible; rewrite /mupinv_core trmx_mul !mulmxA.
  by rewrite !trmx_mul !mulmxA !trmxK.
  clear a h h2.
  subst goal; symmetry; set goal := RHS.
  set goal1 := RHS in h1.
  set from := LHS.
  have step1: from = goal1.
  subst from.
  rewrite H_sym !mulmxBr mulmx1 mulmxBl unlock /mupinv /mupinv_core.
  by subst goal1; rewrite !trmx_mul !mulmxA.
  rewrite step1 -h1.
  subst goal; symmetry; set goal := RHS.
  rewrite unlock /mupinv /mupinv_core !mulmxBr mulmx1 !mulmxBl -addrA [in - _ + _]addrC addrA.
  by subst goal; rewrite !trmx_mul !mulmxA !trmxK.
Qed.

End Section4.