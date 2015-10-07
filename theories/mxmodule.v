(* (c) Copyright ? *)

(*****************************************************************************
  This file generalizes some of the matrix operations in matrix.v and mxutil.v. 
  These operations were previously only defined on ring-element matrices and 
  are now generalized to module-element matrices ('generalize' in the sense that
  a ring is also an Lmodule on itself). 

  These operations are defined on zmodType:
          gdiag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.
               a%:gM == the scalar matrix with a's on the main diagonal.
      delta_mx a i j == the matrix with a 1 in row i, column j and 0 elsewhere.  

  These operations are defined on (left/right/bi) modules:
            a *ml: A == equivalent to (map_mx *:%R). a : R and A : 'M[V]_(m,n),
                        where V : lmodType R, R : ringType.
             A *ml B == the matrix product of A and B, where A : 'M[R]_(m,n)
                        and B : 'M[V]_(n,p). V : lmodType R.              
             A *mr B == the matrix product of A and B, where A : 'M[V]_(m,n)
                        and B : 'M[R]_(n,p). V : rmodType R.     
          llin1_mx f == the m x n matrix that emulates via *ml
                        a (linear) function f : 'rV[R]_m -> 'rV[V]_n on ROW VECTORS
           llin_mx f == the (m1 * n1) x (m2 * n2) matrix that emulates, via the   
                        *ml on the mxvec encodings, a linear     
                        function f : 'M[R]_(m1, n1) -> 'M[V]_(m2, n2)      
             A *ol B == Left Kronecker product of A and B. Its type is 
                        'M[R]_(m1,n1) -> 'M[V]_(m2,n2) -> 'M[V]_(m1*m2,n1*n2). 
                        Its characteristic properties are:
                        (1) in terms of rvec:
                          lkronP : rvec C *ml (A *ol B) = rvec (A^T *m C *ml B)
                        (2) in terms of vec:
                          lkronPc : vec (A *mr B *mr C) = (C^T *ol A) *mr vec B
                        Another viewpoint of left Kronecker product is:
                          | a11 a12 |        | a11*ml:B  a12*ml:B |
                          |         | *o B = |                    |
                          | a21 a22 |        | a21*ml:B  a22*ml:B |
       flatten_mx A == flatten a column vector of row vectors to a matrix. 
                       'cV['rV_n]_m -> 'M_(m,n)

  Module-element matrices form Lmodule structures with both *ml: and *ml as the
  scale function. To register those canonical structures, the former canonical
  structure will be infered if the matrix type if tagged with ^s (e.g. 
  'M[V]_(m,n)^s) and the latter canonical structure will be infered with tag ^m
  (e.g. 'M[V]_(m,n)^m). If no tag is present, the canonical structure registered
  by matrix.v, with scalemx as the scale function, will be infered.
  Rmodule and Bimodule canonical structures are also registered for tag ^m and
  comRing-element matrices without tag.
                        
******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp.

Import GroupScope.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import matrix.

Require Import mxutil.
Import Notations.
Require Import bimodule.

Section ComRingElem.

Variable R : comRingType.
Variable m n : nat.

Canonical matrix_rmodType := Eval hnf in RmodType R 'M[R]_(m,n) (RmoduleFromComm.RmodMixin_from_comm (matrix_lmodType R m n)).

Lemma lrassoc (a : R) (A : 'M[R]_(m, n)) (b : R) : a *: (A :* b) = a *: A :* b.
Proof.
  apply/matrixP => i j; rewrite !mxE.
  by rewrite !mulrA (mulrC a b).
Qed.

Canonical matrix_bimodType := Eval hnf in BimodType R R 'M[R]_(m, n) lrassoc.

Lemma lrcomm (a : R) (A : 'M[R]_(m, n)) : A :* a = a *: A.
Proof.
  by apply/matrixP => i j; rewrite !mxE.
Qed.

Canonical matrix_comBimodType := Eval hnf in ComBimodType R 'M[R]_(m, n) lrcomm.

End ComRingElem.

(* Generalized matrix multiplication A * B = C, where A, B and C can have different element types, and C's elements only needs to be Zmodule *)
Section GeneralMul.

Variable U V : Type.
Variable Z : zmodType.
Variable mul : U -> V -> Z.

Fact gmulmx_key : unit. Proof. by []. Qed.
Definition gmulmx m n p (A : 'M[U]_(m, n)) (B : 'M[V]_(n, p)) : 'M[Z]_(m, p) :=
  \matrix[gmulmx_key]_(i, k) \sum_j (mul (A i j) (B j k)).

End GeneralMul.

(* Generalized diagonal matrix *)
Section GeneralDiag.

(* The elements need to be Zmodule because we need '0' *)
Variable V : zmodType.
Variable n : nat.

Fact gdiag_mx_key : unit. Proof. by []. Qed.
Definition gdiag_mx (d : 'rV[V]_n) :=
  \matrix[gdiag_mx_key]_(i, j) (if i == j then d 0 i else 0).

Fact gscalar_mx_key : unit. Proof. by []. Qed.
Definition gscalar_mx x : 'M[V]_n :=
  \matrix[gscalar_mx_key]_(i , j) (if i == j then x else 0).
Notation "x %:gM" := (gscalar_mx x) (at level 8): ring_scope.

Lemma gdiag_const_mx a : gdiag_mx (const_mx a) = a%:gM :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Variable m : nat.

Fact gdelta_mx_key : unit. Proof. by []. Qed.
Definition gdelta_mx x i0 j0 : 'M[V]_(m, n) :=
  \matrix[gdelta_mx_key]_(i, j) (if (i == i0) && (j == j0) then x else 0).

Lemma matrix_sum_gdelta (A : 'M_(_,_)) :
  A = \sum_(i < m) \sum_(j < n) gdelta_mx (A i j) i j.
Proof.
apply/matrixP => i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE !eqxx. 
rewrite !big1 ?addr0 //= => [i' | j']; rewrite eq_sym => /negbTE diff.
by rewrite summxE big1 // => j' _; rewrite !mxE diff.  
by rewrite !mxE eqxx diff.
Qed.

End GeneralDiag.

Local Notation "x %:gM" := (gscalar_mx _ x) (at level 8): ring_scope.

Lemma scalar_gscalar (R : ringType) n (x : R) : x%:M = x%:gM :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE; case: (i == j). Qed.

Lemma delta_gdelta (R : ringType) m n (x : R) i j : x *: delta_mx i j = gdelta_mx x i j :> 'M_(m, n).
Proof. 
  apply/matrixP=> ii jj; rewrite !mxE.
  case (_ && _). 
  by rewrite mulr1.
  by rewrite mulr0.
Qed.

Section LmoduleElem.

Variable R : ringType.
Variable V : lmodType R.

Fact lscalemx_key : unit. Proof. by []. Qed.
Definition lscalemx m n x (A : 'M[V]_(m,n)) := \matrix[lscalemx_key]_(i, j) (x *: A i j).
Local Notation "x *ml: A" := (lscalemx x A) (at level 40) : ring_scope.

(* Since matrix.v already registered matrix_lmodType for (matrix, Lmodule.sort), here we use a tag to register lscale_lmodType for (stag, Lmodule.sort) *)
Definition stag M : Type := M.
Local Notation "M ^s" := (stag M) (at level 8, format "M ^s") : type_scope.

(* The Lmodule structure for matrix whose scale is lscale *)
Section LmoduleForLscale.

Variable m n : nat.

Lemma lscale1mx (A : 'M[V]_(m,n)) : 1 *ml: A = A.
Proof. by apply/matrixP=> i j; rewrite !mxE scale1r. Qed.

Lemma lscalemxA x y (A : 'M[V]_(m,n)) : x *ml: (y *ml: A) = (x * y) *ml: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerA. Qed.

Lemma lscalemxDl x y (A : 'M[V]_(m,n)) : (x + y) *ml: A = x *ml: A + y *ml: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDl. Qed.

Lemma lscalemxDr x (A B : 'M[V]_(m,n)) : x *ml: (A + B) = x *ml: A + x *ml: B.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDr. Qed.

Lemma trmx_lscalemx c (A : 'M[V]_(m,n)) : (c *ml: A)^T = c *ml: A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma lscalemx0 c : c *ml: 0 = 0 :> 'M[V]_(m,n).
Proof. by apply/matrixP=> i j; rewrite !mxE scaler0. Qed.

Lemma lscale0mx A : 0 *ml: A = 0 :> 'M[V]_(m,n).
Proof. by apply/matrixP=> i j; rewrite !mxE scale0r. Qed.

Definition lscale_lmodMixin := 
  LmodMixin lscalemxA lscale1mx lscalemxDr (fun v a b => lscalemxDl a b v).

Canonical lscale_lmodType :=
  Eval hnf in LmodType R 'M[V]_(m, n)^s lscale_lmodMixin.

End LmoduleForLscale.

Section StructuralLinear.

Definition lswizzle_mx := swizzle_mx.
Lemma lswizzle_mx_is_scalable m n p q f g k :
  scalable (@lswizzle_mx V m n p q f g k : 'M_(m,n)^s -> 'M_(p,q)^s).
Proof. by move=> a A; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical lswizzle_mx_scalable m n p q f g k :=
  AddLinear (@lswizzle_mx_is_scalable m n p q f g k).

Notation "[ 'linear' fUV 'of' f 'as' g ]" := (@GRing.Linear.clone _ _ _ _ (Phant fUV) f g _ _ idfun id)
   (at level 0, format "[ 'linear' fUV 'of' f 'as' g ]") : form_scope.

Local Notation SwizzleLin op := [linear 'M_(_,_)^s -> 'M_(_,_)^s of op as lswizzle_mx _ _ _].

Definition ltrmx := @trmx.
Canonical ltrmx_linear m n := SwizzleLin (@ltrmx _ m n).
Definition lrow := @row.
Canonical lrow_linear m n i := SwizzleLin (@lrow _ m n i).
Definition lcol := @col.
Canonical lcol_linear m n j := SwizzleLin (@lcol _ m n j).
Definition lrow' := @row'.
Canonical lrow'_linear m n i := SwizzleLin (@lrow' _ m n i).
Definition lcol' := @col'.
Canonical lcol'_linear m n j := SwizzleLin (@lcol' _ m n j).
Definition lrow_perm := @row_perm.
Canonical lrow_perm_linear m n s := SwizzleLin (@lrow_perm _ m n s).
Definition lcol_perm := @col_perm.
Canonical lcol_perm_linear m n s := SwizzleLin (@lcol_perm _ m n s).
Definition lxrow := @xrow.
Canonical lxrow_linear m n i1 i2 := SwizzleLin (@lxrow _ m n i1 i2).
Definition lxcol := @xcol.
Canonical lxcol_linear m n j1 j2 := SwizzleLin (@lxcol _ m n j1 j2).
Definition llsubmx := @lsubmx.
Canonical llsubmx_linear m n1 n2 := SwizzleLin (@llsubmx _ m n1 n2).
Definition lrsubmx := @rsubmx.
Canonical lrsubmx_linear m n1 n2 := SwizzleLin (@lrsubmx _ m n1 n2).
Definition lusubmx := @usubmx.
Canonical lusubmx_linear m1 m2 n := SwizzleLin (@lusubmx _ m1 m2 n).
Definition ldsubmx := @dsubmx.
Canonical ldsubmx_linear m1 m2 n := SwizzleLin (@ldsubmx _ m1 m2 n).
Definition lvec_mx := @vec_mx.
Canonical lvec_mx_linear m n := SwizzleLin (@lvec_mx _ m n).
Definition lmxvec {R m n} := @mxvec R m n : 'M_(_,_)^s -> 'M_(_,_)^s.
Definition lmxvec_is_linear m n := @can2_linear _ (lscale_lmodType _ _) (lscale_lmodType _ _) (@lvec_mx_linear _ _) (@lmxvec _ _ _ : 'M_(_,_)^s -> 'M_(_,_)^s) (@vec_mxK V m n) mxvecK.
Canonical lmxvec_linear m n := AddLinear (@lmxvec_is_linear m n).

End StructuralLinear.

(* lmulx *)
Definition lmulmx := gmulmx (@GRing.scale _ V).
Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.

Lemma lmulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) : A *ml (B *ml C) = A *m B *ml C.
Proof.
apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j *: (B j k *: C k l)))).
  by apply: eq_bigr => j _; rewrite mxE scaler_sumr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE scaler_suml /=.
by apply: eq_bigr => k _; rewrite scalerA.
Qed.

Lemma lmul_diag_mx m n d (A : 'M_(m, n)) :
  gdiag_mx d *ml A = \matrix_(i, j) (d 0 i *: A i j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
rewrite mxE eq_sym.
move/negbTE->.
by rewrite scale0r.
Qed.

Lemma lmul_mx_diag m n (A : 'M_(m, n)) d :
  A *ml gdiag_mx d = \matrix_(i, j) (A i j *: d 0 j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
rewrite mxE eq_sym.
move/negbTE->.
by rewrite scaler0.
Qed.

Lemma lmul_scalar_mx m n a (A : 'M_(m, n)) : a%:gM *ml A = a *ml: A.
Proof.
by rewrite -gdiag_const_mx lmul_diag_mx; apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma lmul1mx m n (A : 'M_(m, n)) : 1%:M *ml A = A.
Proof. by rewrite scalar_gscalar lmul_scalar_mx lscale1mx. Qed.

Lemma lmulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *ml B = A1 *ml B + A2 *ml B.
Proof.
apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE -scalerDl.
Qed.

Lemma lmulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *ml (B1 + B2) = A *ml B1 + A *ml B2.
Proof.
apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite mxE scalerDr.
Qed.

Lemma lmulNmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : - A *ml B = - (A *ml B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE scaleNr.
Qed.

Lemma lmulmxN m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : A *ml (- B) = - (A *ml B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE scalerN.
Qed.

Lemma lmul0mx m n p (A : 'M_(n, p)) : 0 *ml A = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 //= => j _; rewrite mxE scale0r.
Qed.

Lemma lmulmx0 m n p (A : 'M_(m, n)) : A *ml 0 = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 // => j _; rewrite mxE scaler0.
Qed.

Lemma lmulmxBl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) : (A1 - A2) *ml B = A1 *ml B - A2 *ml B.
Proof. by rewrite lmulmxDl lmulNmx. Qed.

Lemma lmulmxBr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *ml (B1 - B2) = A *ml B1 - A *ml B2.
Proof. by rewrite lmulmxDr lmulmxN. Qed.

Lemma lmulmx1Br m n (A : 'M_m) (B : 'M[V]_(m,n)) : (I - A) *ml B = B - A *ml B.
Proof. by rewrite lmulmxBl lmul1mx. Qed.

Lemma lmul_row_col m n1 n2 p (Al : 'M[R]_(m, n1)) (Ar : 'M_(m, n2))
                            (Bu : 'M[V]_(n1, p)) (Bd : 'M_(n2, p)) :
  row_mx Al Ar *ml col_mx Bu Bd = Al *ml Bu + Ar *ml Bd.
Proof.
apply/matrixP=> i k; rewrite !mxE big_split_ord /=.
congr (_ + _); apply: eq_bigr => j _; first by rewrite row_mxEl col_mxEu.
by rewrite row_mxEr col_mxEd.
Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma lscale_row_mx m n1 n2 a (A1 : 'M[V]_(m, n1)) (A2 : 'M_(m, n2)) :
  a *ml: row_mx A1 A2 = row_mx (a *ml: A1) (a *ml: A2).
Proof. by split_mxE. Qed.

Lemma lscale_col_mx m1 m2 n a (A1 : 'M[V]_(m1, n)) (A2 : 'M_(m2, n)) :
  a *ml: col_mx A1 A2 = col_mx (a *ml: A1) (a *ml: A2).
Proof. by split_mxE. Qed.

Lemma lscale_block_mx m1 m2 n1 n2 a (Aul : 'M[V]_(m1, n1)) (Aur : 'M_(m1, n2))
                                   (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)) :
  a *ml: block_mx Aul Aur Adl Adr
     = block_mx (a *ml: Aul) (a *ml: Aur) (a *ml: Adl) (a *ml: Adr).
Proof. by rewrite lscale_col_mx !lscale_row_mx. Qed.

(* Since matrix.v already registered matrix_lmodType for (matrix, Lmodule.sort), here we use a tag to register lmul_lmodType for (mtag, Lmodule.sort) *)
Definition mtag M : Type := M.
Local Notation "M ^m" := (mtag M) (at level 8, format "M ^m") : type_scope.

Canonical mtag_zmodType m n := [zmodType of 'M[V]_(m,n)^m].

(* The Lmodule structure for matrix whose scale is lmul *)
Section LmoduleForLmul.

Variable m' n : nat.
Notation m := m'.+1.

Definition lmul_lmodMixin := 
  LmodMixin (@lmulmxA m _ _ n) (@lmul1mx _ _) (@lmulmxDr _ _ _) (fun v a b => lmulmxDl a b v).

Canonical lmul_lmodType :=
  Eval hnf in LmodType 'M[R]_m 'M[V]_(m, n)^m lmul_lmodMixin.

Lemma scale_lmul (A : 'M_m) (B : 'M_(m,n)^m) : A *: B = A *ml B.
Proof. by []. Qed.

End LmoduleForLmul.

(* Correspondance between matrices and linear function on row vectors, in terms of lmulmx. *) 
Section LLinRowVector.

Variables m n : nat.

Fact llin1_mx_key : unit. Proof. by []. Qed.
Definition llin1_mx (f : 'rV[R]_m -> 'rV[V]_n) :=
  \matrix[llin1_mx_key]_(i, j) f (delta_mx 0 i) 0 j.

Variable f : {linear 'rV[R]_m -> 'rV[V]_n^s}.

Lemma lmul_rV_llin1 u : u *ml llin1_mx f = f u.
Proof.
rewrite {2}[u]matrix_sum_delta big_ord1 linear_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite linearZ !mxE.
Qed.

End LLinRowVector.

(* Correspondance between matrices and linear function on matrices. *) 
Section LLinMatrix.

Variables m1 n1 m2 n2 : nat.

Definition llin_mx (f : 'M[R]_(m1, n1) -> 'M[V]_(m2, n2)) :=
  llin1_mx (lmxvec \o f \o vec_mx).

Variable f : {linear 'M[R]_(m1, n1) -> 'M[V]_(m2, n2)^s}.

Lemma lmul_rV_llin u : u *ml llin_mx f = mxvec (f (vec_mx u)).
Proof. by rewrite lmul_rV_llin1. Qed.

Lemma lmul_vec_llin A : mxvec A *ml llin_mx f = mxvec (f A).
Proof. by rewrite lmul_rV_llin mxvecK. Qed.

Lemma mx_rV_llin u : vec_mx (u *ml llin_mx f) = f (vec_mx u).
Proof. by rewrite lmul_rV_llin mxvecK. Qed.

Lemma mx_vec_llin A : vec_mx (mxvec A *ml llin_mx f) = f A.
Proof. by rewrite lmul_rV_llin !mxvecK. Qed.

End LLinMatrix.

Lemma lscalelmulAl m n p a (A : 'M_(m, n)) (B : 'M_(n, p)) :
  a *ml: (A *ml B) = (a *: A) *ml B.
Proof.
apply/matrixP=> i k; rewrite !mxE scaler_sumr /=.
by apply: eq_bigr => j _; rewrite mxE scalerA.
Qed.

Section Lmulmxr.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[V]_(n, p).

Definition lmulmxr_head t B A := let: tt := t in A *ml B.
Local Notation lmulmxr := (lmulmxr_head tt).

Lemma lmulmxr_is_linear B : @GRing.Linear.axiom _ _ _ *:%R (lmulmxr B : 'M_(_,_) -> 'M_(_,_)^s) _ (erefl *:%R).
Proof. by move=> a A1 A2; rewrite /= lmulmxDl -lscalelmulAl. Qed.
Canonical lmulmxr_additive B := Additive (lmulmxr_is_linear B).
Canonical lmulmxr_linear B := Linear (lmulmxr_is_linear B).

End Lmulmxr.

End LmoduleElem.

Local Notation "x *ml: A" := (lscalemx x A) (at level 40) : ring_scope.
Local Notation "M ^s" := (stag M) (at level 8, format "M ^s") : type_scope.
Local Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.
Local Notation "A ^cm" := (A : 'M[_^c]_(_,_)) (at level 2).
Local Notation "M ^m" := (mtag M) (at level 8, format "M ^m") : type_scope.

Section LalgebraElem.

Variable R : ringType.
Variable V : lalgType R.

Lemma lscalemxAl m n p a (A : 'M[V]_(m, n)) (B : 'M_(n, p)) :
  a *ml: (A *m B) = (a *ml: A) *m B.
Proof.
apply/matrixP=> i k; rewrite !mxE scaler_sumr /=.
by apply: eq_bigr => j _; rewrite scalerAl mxE.
Qed.

Lemma scale_lscale m n (a : R) (A : 'M[V]_(m,n)) : a%:A *: A = a *ml: A.
Proof. by apply/matrixP=> i j; rewrite !mxE -scalerAl mul1r. Qed.

Variable m' : nat.
Notation m := m'.+1.

Canonical lscale_lalgType := Eval hnf in LalgType R 'M[V]_m^s (@lscalemxAl m m m : GRing.Lalgebra.axiom (_ : 'M[V]_m^s -> _ -> _)).

End LalgebraElem.

Lemma trmx_mul_c (R : ringType) m n p (A : 'M[R]_(m,n)) (B : 'M_(n,p)) : (A *m B)^T = B^cm^T *m A^cm^T.
Proof.
  apply/matrixP=> i l; rewrite !mxE.
  by apply eq_bigr => j ?; rewrite !mxE.
Qed.

Local Notation "M ^m" := (mtag M) (at level 8, format "M ^m") : type_scope.

Section RmoduleElem.

Variable R : ringType.
Variable V : rmodType R.

Definition rmulmx := gmulmx (@rscale _ V).

Notation "A *mr B" := (rmulmx A B) (at level 40, left associativity, format "A  *mr  B") : ring_scope.

Lemma rmulmx_lmulmx m n p (A : 'M_(m,n)) (B : 'M_(n,p)) : A *mr B = (B^cm^T *ml A^T)^T.
Proof.
apply/matrixP=> i l; rewrite !mxE.
by apply eq_bigr => j ?; rewrite !mxE.
Qed.

Lemma rmulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) : A *mr (B *m C) = A *mr B *mr C.
Proof.
  rewrite !rmulmx_lmulmx; f_equal.
  rewrite trmxK lmulmxA; f_equal.
  by rewrite (trmx_mul_c B C).
Qed.

Lemma rmulmxAR m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) : A *mr B *mr C = A *mr (B *m C).
Proof. by rewrite rmulmxA. Qed.

Lemma rmulmx1 m n (A : 'M_(m, n)) : A *mr 1%:M = A.
Proof. 
  by rewrite rmulmx_lmulmx trmx1 lmul1mx trmxK.
Qed.

Lemma rmulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *mr B = A1 *mr B + A2 *mr B.
Proof.
  by rewrite !rmulmx_lmulmx raddfD /= lmulmxDr raddfD /=.
Qed.

Lemma rmulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *mr (B1 + B2) = A *mr B1 + A *mr B2.
Proof.
  by rewrite !rmulmx_lmulmx raddfD /= lmulmxDl raddfD /=.
Qed.

Lemma rmulNmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : - A *mr B = - (A *mr B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE /rscale scalerN.
Qed.

Lemma rmulmxN m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : A *mr (- B) = - (A *mr B).
Proof.
apply/matrixP=> i k; rewrite !mxE -sumrN.
by apply: eq_bigr => j _; rewrite mxE /rscale scaleNr.
Qed.

Lemma rmul0mx m n p (A : 'M_(n, p)) : 0 *mr A = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 //= => j _; rewrite mxE /rscale scaler0.
Qed.

Lemma rmulmx0 m n p (A : 'M_(m, n)) : A *mr 0 = 0 :> 'M_(m, p).
Proof.
by apply/matrixP=> i k; rewrite !mxE big1 // => j _; rewrite mxE /rscale scale0r.
Qed.

Lemma rmulmxBr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *mr (B1 - B2) = A *mr B1 - A *mr B2.
Proof. by rewrite rmulmxDr rmulmxN. Qed.

Lemma rmulmxBl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) : (A1 - A2) *mr B = A1 *mr B - A2 *mr B.
Proof. by rewrite rmulmxDl rmulNmx. Qed.

Lemma rmulmx1Br m n (A : 'M_(m,n)) B : A *mr (I - B) = A - A *mr B.
Proof. by rewrite rmulmxBr rmulmx1. Qed.

(* The Rmodule structure for matrix whose scale is rmul *)
Section RmoduleForRmul.

Variable m n' : nat.
Notation n := n'.+1.

Definition rmul_mixin :=  RmodMixin (@rmulmxA m _ _ n) (@rmulmx1 _ _) (@rmulmxDl _ _ _) (@rmulmxDr _ _ _).

Canonical rmul_rmodType := Eval hnf in RmodType _ 'M[V]_(m, n)^m rmul_mixin.

Lemma rscale_rmul (A : 'M_(m,n)^m) (B : 'M_n) : A :* B = A *mr B.
Proof. by []. Qed.

End RmoduleForRmul.

End RmoduleElem.

Notation "A *mr B" := (rmulmx A B) (at level 40, left associativity, format "A  *mr  B") : ring_scope.

Section BimoduleElem.

Variable R : ringType.
Variable V : bimodType R R.

Lemma lrmulmxA m n p q (A : 'M[R]_(m, n)) (B : 'M[V]_(n, p)) (C : 'M_(p, q)) : A *ml (B *mr C) = A *ml B *mr C.
Proof.
apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j *: (B j k :* C k l)))).
  by apply: eq_bigr => j _; rewrite mxE scaler_sumr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE /rscale scaler_sumr /=.
by apply: eq_bigr => k _; rewrite scalerlA.
Qed.

Section Bimodule.

Variable m' n' : nat.
Notation m := m'.+1.
Notation n := n'.+1.

Canonical lrmul_bimodType := Eval hnf in BimodType _ _ 'M[V]_(m, n)^m (@lrmulmxA _ m n _).

End Bimodule.

End BimoduleElem.

Section ComBimoduleElem.

Variable R : ringType.
Variable V : comBimodType R.

Lemma trmx_lmulmx m n p (A : 'M_(m,n)) (B : 'M[V]_(n,p)) : (A *ml B)^T = B^T *mr A^T.
Proof.
apply/matrixP=> i l; rewrite !mxE.
by apply eq_bigr => j ?; rewrite !mxE lrscaleC.
Qed.

Lemma trmx_rmulmx m n p (A : 'M[V]_(m,n)) (B : 'M_(n,p)) : (A *mr B)^T = B^T *ml A^T.
Proof.
apply/matrixP=> i l; rewrite !mxE.
by apply eq_bigr => j ?; rewrite !mxE lrscaleC.
Qed.

End ComBimoduleElem.

Section KroneckerProduct.

Variable R : comRingType.
Variable V : lmodType R.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[V]_(m2,n2).

Notation lmulmxr := (lmulmxr_head tt).

(* Left Kronecker product *)
Definition lkron A B := llin_mx ((lmulmxr B) \o (mulmx A^T)).
Local Notation "A *ol B" := (lkron A B) (at level 40).

(* The characteristic property of Kronecker product, in terms of rvec *)
Lemma lkronP A B C : rvec C *ml (A *ol B) = rvec (A^T *m C *ml B).
  by rewrite lmul_vec_llin.
Qed.

End KroneckerProduct.

Local Notation "A *ol B" := (lkron A B) (at level 40).

Section DeltaMxTheory.

Variable R : comRingType.
Variable V : lmodType R.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[V]_(m2,n2).

Lemma rowElmul m n i (A : 'M[V]_(m, n)) : row i A = delta_mx 0 i *ml A.
Proof.
apply/rowP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx scale1r.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) scale0r.
Qed.

Lemma rowcolElmul i j A B : A *m delta_mx i j *ml B = col i A *ml row j B.
Proof.
  by rewrite rowElmul colE !lmulmxA -(mulmxA _ (delta_mx i 0)) mul_delta_mx.
Qed.

Lemma cVlmulrV m n (c : 'cV_m) (r : 'rV[V]_n) i j : (c *ml r) i j = c i 0 *: r 0 j.
Proof.
  by rewrite !mxE big_ord1.
Qed.

Lemma collmulrowP i j A B ii jj : (col j A *ml row i B) ii jj = A ii j *: B i jj.
Proof.
  by rewrite cVlmulrV !mxE.
Qed.

End DeltaMxTheory.

Section LkronE.

Variable R : comRingType.
Variable V : lmodType R.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[V]_(m2,n2).

Lemma lkronE A B i1 i2 j1 j2 : (A *ol B) (mxvec_index i1 i2) (mxvec_index j1 j2) = A i1 j1 *: B i2 j2.
Proof.
  by rewrite !mxE /= mxvecE vec_mx_delta rowcolElmul collmulrowP !mxE.
Qed.

End LkronE.

Section Basics.

Variable R : comRingType.
Variable V : lmodType R.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[V]_(m2,n2).

Lemma trmx_lkron A B : (A *ol B)^T = (A^T *ol B^T).
Proof.
  apply/matrixP=> i j.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite mxE !lkronE !mxE.
Qed.

Lemma lkron0mx B : (0 : 'M_(m1,n1)) *ol B = 0.
Proof.
  apply/matrixP=> i j; rewrite !mxE /= trmx0 !mul0mx lmul0mx /=.
  case/mxvec_indexP: j => x y.
  by rewrite mxvecE !mxE.
Qed.

Lemma lkronmx0 A : A *ol (0 : 'M[V]_(m2,n2)) = 0.
Proof.
  apply/matrixP=> i j; rewrite !mxE /= lmulmx0 /=.
  case/mxvec_indexP: j => x y.
  by rewrite mxvecE !mxE.
Qed.

End Basics.

Section KronPColumn.

Variable R : comRingType.
Variable V : comBimodType R.

Lemma kronPrmul m1 n1 m2 n2 (A : 'M_(m1,n1)) (B : 'M_(m2,n2)) (C : 'M[V]_(_,_)) : rvec C *mr (A *o B) = rvec (A^T *ml C *mr B).
Proof.
  apply/rowP => k.
  case/mxvec_indexP: k => x y.
  rewrite mxvecE mxE (reindex _ (curry_mxvec_bij _ _)) /=.
  transitivity (\sum_k \sum_j A^T x k *: C k j :* B j y).
  rewrite pair_bigA /=.  
  apply: eq_bigr => [[i j]] /= _.
  by rewrite kronE mxvecE scaleAr [in C i j :* _]lrscaleC mxE.
  rewrite exchange_big /= !mxE.
  apply: eq_bigr => j _.
  rewrite !mxE /rscale scaler_sumr.
  by apply: eq_bigr => i _.
Qed.

Variables m1 n1 m2 n2 : nat.

(* The characteristic property of Kronecker product, in terms of vec *)
Lemma lkronPc (A : 'M[V]_(m1,n1)) B (C : 'M_(m2,n2)) : vec (A *mr B *mr C) = (C^T *ol A) *mr vec B.
Proof.
  by rewrite !trmx_rmulmx !lmulmxA -lkronP !trmx_lmulmx trmx_lkron trmxK.
Qed.

Lemma kronPclmul (A : 'M_(m1,n1)) (B : 'M[V]_(_,_)) (C : 'M_(m2,n2)) : vec (A *ml B *mr C) = (C^T *o A) *ml vec B.
Proof.
  by rewrite !trmx_rmulmx !trmx_lmulmx !lrmulmxA -kronPrmul !trmx_rmulmx trmx_kron trmxK.
Qed.

End KronPColumn.

(* Corollaries from the characteristic properties *)
Section Corollaries.

Variable R : comRingType.
Variable V : comBimodType R.
Variables m n r : nat.
Implicit Types A : 'M[V]_(m,n).
Implicit Types B : 'M[R]_(n,r).

Corollary vec_lkron A B : vec (A *mr B) = (I *ol A) *mr vec B.
Proof.
  by rewrite -(rmulmx1 (A *mr B)) lkronPc trmx1.
Qed.

Corollary vec_kron_lmul A B : vec (A *mr B) = (B^T *o I) *ml vec A.
Proof.
  by rewrite -(@lmul1mx R _ _ _ (A *mr B)) lrmulmxA kronPclmul.
Qed.

Corollary lkron_shift A B : (I *ol A) *mr vec B = (B^T *o I) *ml vec A.
Proof.
  by rewrite -vec_lkron vec_kron_lmul.
Qed.

End Corollaries.

Definition to_pair m n (k : 'I_(m * n)) : 'I_m * 'I_n :=
  match mxvec_indexP k with
    | IsMxvecIndex i j => (i, j)
  end.

Lemma inj_prod_eq (a1T a2T rT : eqType) (f : a1T -> a2T -> rT) : injective (prod_curry f) -> forall x1 x2 y1 y2, (f x1 x2 = f y1 y2) -> ((x1 = y1) /\ (x2 = y2)).
Proof.
  move => inj x1 x2 y1 y2 fe.
  have /= inj2 := inj (_, _) (_, _).
  by case/inj2: fe => -> ->.
Qed.

Section RightKroneckerProduct.

Variable R : comRingType.
Variable V : rmodType R.
Variable m1 n1 m2 n2 : nat.
Implicit Types (A : 'M[V]_(m1,n1)) (B : 'M[R]_(m2,n2)).

(* Right Kronecker product *)
Definition rkron A B := 
  \matrix_(i < m1 * m2, j < n1 * n2) 
   let ii := to_pair i in
   let jj := to_pair j in
   A ii.1 jj.1 :* B ii.2 jj.2.

Local Notation "A *or B" := (rkron A B) (at level 40).

Lemma rkronE A B i1 i2 j1 j2 : (A *or B) (mxvec_index i1 i2) (mxvec_index j1 j2) = A i1 j1 :* B i2 j2.
Proof.
  rewrite !mxE /to_pair /=.
  case hi: _ / mxvec_indexP => [ii1 ii2].
  case hj: _ / mxvec_indexP => [jj1 jj2].
  (* Search _ "{ on _ , bijective _ }". *)
  have /= VV := inj_prod_eq (bij_inj (onT_bij (curry_mxvec_bij _ _))).
  by case/VV: hi => -> ->; case/VV: hj => -> ->.
Qed.

Lemma rkronPc A B C : (A *or B) *mr vec C = vec (A *mr C^T *mr B^T)^T.
Proof.
  apply/matrixP => i j.
  case/mxvec_indexP: i => i1 i2.
  rewrite mxE ord1 trmxK mxE mxvecE (reindex _ (curry_mxvec_bij _ _)) /=.
  transitivity (\sum_k \sum_j A i1 k :* C^T k j :* B^T j i2).
  rewrite pair_bigA /=.  
  apply: eq_bigr => [[ii jj]] /= _.
  by rewrite rkronE mxE mxvecE !mxE -!scaleAr mulrC.
  rewrite exchange_big /= !mxE.
  apply: eq_bigr => jj _.
  rewrite !mxE /rscale scaler_sumr.
  by apply: eq_bigr => ii _.
Qed.

Lemma rkron0mx B : (0 : 'M_(m1,n1)) *or B = 0.
Proof.
  apply/matrixP=> i j.
  case/mxvec_indexP: i => i1 i2.
  case/mxvec_indexP: j => j1 j2.
  by rewrite rkronE !mxE /rscale scaler0.
Qed.

Lemma rkronmx0 A : A *or (0 : 'M_(m2,n2)) = 0.
Proof.
  apply/matrixP=> i j.
  case/mxvec_indexP: i => i1 i2.
  case/mxvec_indexP: j => j1 j2.
  by rewrite rkronE !mxE /rscale scale0r.
Qed.

End RightKroneckerProduct.

Section Gdelta.

Variable V : zmodType.

Lemma vec_mx_gdelta x m n i j :
  vec_mx (gdelta_mx x 0 (mxvec_index i j)) = gdelta_mx x i j :> 'M[V]_(m, n).
Proof.
by apply/matrixP=> i' j'; rewrite !mxE /= [_ == _](inj_eq enum_rank_inj).
Qed.

End Gdelta.

Section LinRightAction.

Variable R : ringType.
Variable E : rmodType R.

Section Simulate.

Variable m1 n1 m2 n2: nat.
Variable f : 'M[R]_(m1,n1) -> 'M[R]_(m2,n2).
Variable g : 'M[E]_(m1,n1) -> 'M[E]_(m2,n2).
Definition simulate := forall x i j ii jj, g (gdelta_mx x i j) ii jj = x :* f (delta_mx i j) ii jj.

End Simulate. 

Section LinRowAction.

Variable m n : nat.

Variable f : {linear 'rV[R]_m -> 'rV[R]_n}.
Variable g : {additive 'rV[E]_m -> 'rV[E]_n}.
Hypothesis sim : simulate f g.

Lemma rmul_rV_lin1 u : u *mr lin1_mx f = g u.
Proof.
rewrite {2}[u]matrix_sum_gdelta big_ord1 raddf_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite !mxE sim.
Qed.

End LinRowAction.

Section LinMatrixAction.

Variables m1 n1 m2 n2 : nat.

Variable f : {linear 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)}.
Variable g : {additive 'M[E]_(m1,n1) -> 'M[E]_(m2,n2)}.
Hypothesis sim : simulate f g.

Lemma sim' : simulate (mxvec \o f \o vec_mx) (mxvec \o g \o vec_mx).
Proof.
  move => x i j ii jj. 
  rewrite /= !ord1.
  case/mxvec_indexP: j => j1 j2.
  case/mxvec_indexP: jj => jj1 jj2.
  by rewrite !mxvecE vec_mx_gdelta vec_mx_delta sim.
Qed.

Lemma rmul_rV_lin u : u *mr lin_mx f = mxvec (g (vec_mx u)).
Proof. 
  by rewrite (rmul_rV_lin1 sim') /=.
Qed.

Lemma rmul_vec_lin A : mxvec A *mr lin_mx f = mxvec (g A).
Proof. by rewrite rmul_rV_lin mxvecK. Qed.

Lemma mx_rV_lin_r u : vec_mx (u *mr lin_mx f) = g (vec_mx u).
Proof. by rewrite rmul_rV_lin mxvecK. Qed.

Lemma mx_vec_lin_r A : vec_mx (mxvec A *mr lin_mx f) = g A.
Proof. by rewrite rmul_rV_lin !mxvecK. Qed.

End LinMatrixAction.

End LinRightAction.

Section CommMx.

Variable R : comRingType.
Variable E : comBimodType R.

Section Row.

Variable m n : nat.

Lemma sim : simulate (@trmx R m n) (@trmx E m n).
Proof.
  move => x i j ii jj. 
  rewrite !mxE.
  case (_ && _).
  by rewrite /rscale scale1r.
  by rewrite /rscale scale0r.
Qed.

(* Characteristic properties *)
Lemma trTPrmul (A : 'M[E]_(m,n)) : rvec A *mr (trT _ _ _)^T = rvec A^T.
  by rewrite trmxK (rmul_vec_lin sim) /=.
Qed.

End Row.

Lemma trTPcrmul m n (A : 'M[E]_(m,n)) : (trT _ _ _) *ml vec A = vec A^T.
Proof.
  by apply trmx_inj; rewrite !trmx_lmulmx (trmxK (rvec A^T)) trTPrmul !trmxK.
Qed.

End CommMx.

(* flatten a column vector of row vectors to a matrix *)
Definition flatten_mx T m n (A : 'cV['rV[T]_n]_m) := \matrix_(i,j) A i 0 0 j.

Lemma flatten_mx11 T n (A : 'M['rV[T]_n]_1) : flatten_mx A = A 0 0.
Proof. by apply/matrixP => i j; rewrite !mxE !ord1. Qed.

Lemma flatten_lmul (R : ringType) m n p (A : 'M[R]_(m,n)) (B : 'cV['rV[R]_p]_n) : flatten_mx (A *ml B) = A *m flatten_mx B.
Proof.
  apply/matrixP => i j.
  rewrite !mxE summxE.
  apply eq_bigr => k _.
  by rewrite !mxE.
Qed.

Lemma flattenD {V : zmodType} m n A B : flatten_mx (A + B) = flatten_mx A + flatten_mx B :> 'M[V]_(m, n).
Proof.
  by apply/matrixP => i j; rewrite !mxE.
Qed.

Module Notations.

Notation "M ^s" := (stag M) (at level 8, format "M ^s") : type_scope.
Notation "M ^m" := (mtag M) (at level 8, format "M ^m") : type_scope.
Notation "x %:gM" := (gscalar_mx x) (at level 8): ring_scope.
Notation "x *ml: A" := (lscalemx x A) (at level 40) : ring_scope.
Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.
Notation "A *mr B" := (rmulmx A B) (at level 40, left associativity, format "A  *mr  B") : ring_scope.
Notation "A *ol B" := (lkron A B) (at level 40) : ring_scope.
Notation "A *or B" := (rkron A B) (at level 40).

End Notations.