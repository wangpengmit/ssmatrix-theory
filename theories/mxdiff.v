(* (c) Copyright ? *)

(*****************************************************************************
  Matrix derivation (differentiation).

 lift_to E A == lift A : 'M[R]_(m,n) to 'M[E]_(m,n), where E : lalgType R.
                Matrix derivation is commutative with multiplication by a 
                (lifted) constant matrix.
      lift A == lift_to _ A

  All the following results are parametrized on f : {derMorph R -> V}, which is
  a derivation on the elements. Derivation on matrices are simply defined as
  (map_mx f). V : bimodType R R. The following notations are used:
          \d == f
         \\d == map_mx f

  The main results about matrix derivation are:
        dmM :      \\d (A *m B) = \\d A *m B + A *m \\d B
        dmI :             \\d I = 0
       dmcs :     \\d (c *ml: A) = c *: 1 *ml: \\d A      
    dmscale : \\d (c *ml: A) = (c *ml: I) *ml \\d A
        dmc :      \\d (lift C) = 0
       dmcl : \\d (lift C *m A) = lift C *ml \\d A 
              (and the symmetric version dmcr)
  dm_lrkron : \\d (A *o B) = \\d A *or B + A *ol \\d B
dm_lkron1mx : \\d (I *o A) = I *ol \\d A
dm_rkronmx1 : \\d (A *o I) = \\d A *or I

  \\d on non-empty square matrices inherit the derMorh, derAdd and linearDer 
  structure from \d.

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import matrix.

Require Import mxutil.
Import Notations.
Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.

Section Ring.

(* Element type *)
Variable E : ringType.
Variable D : bimodType E E.
Variable der : {derAdd D}.

Notation "\d" := der.
Notation "\\d" := (@map_mx _ _ \d _ _).

Section AnyMatrix.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

(* Matrix derivation is derivative (has Lebniz product rule) for matrix multiplication *)
Lemma dmM A B : \\d (A *m B) = \\d A *mr B + A *ml \\d B.
Proof.
  by apply/matrixP => i k; rewrite !mxE !raddf_sum -big_split; apply eq_bigr => j; rewrite /= !mxE derM.
Qed.

End AnyMatrix.

Lemma dmI n : \\d I = 0 :> 'M_n.
Proof.
  apply: (addIr (\\d (I *m I))).
  by rewrite add0r {1}mul1mx dmM lmul1mx rmulmx1.
Qed.

(*here*)

Section SquareMatrix.

Variable n' : nat.
Local Notation n := n'.+1.

(* Can only register for DerMorph here because DerMorph is only defined for rings, not graded rings *)
Canonical dm_der := DerMorphFor 'M[D]_n^m (@dmM n n n).
(* Now that \\d has a canonical DerMorph structure, and since it already has a canonical Additive structure thanks to map_mx_additive, packDerAdd will automatically generate a DerAdd structure *)
Canonical dm_derAdd := packDerAdd 'M[D]_n^m \\d.

End SquareMatrix.

End Ring.

Section Lalgebra.

Variable R : ringType.
Variable E : lalgType R.
Variable D : bimodType E E.
Variable der : {linearDer E -> D}.

Notation "\d" := der.
Notation "\\d" := (@map_mx _ _ \d _ _).

Lemma dmcs m c (A : 'M[E]_m) : \\d (c *ml: A) = c%:A *ml: \\d A .
Proof. by apply/matrixP => i j; rewrite !mxE linearZ /=. Qed.

Lemma dmscale m c (A : 'M[E]_m) : \\d (c *ml: A) = (c *ml: I) *ml \\d A.
Proof. 
  by rewrite dmcs -lmul_scalar_mx -scalar_gscalar -scalemx1 scale_lscale.
Qed.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma dmscale' c (A : 'M[E]_n^s) : \\d (c *: A) = c *: (1 : 'M[E]_n^s) *: (\\d A : 'M[D]_n^m).
Proof. by rewrite dmscale. Qed.

Canonical dm_linear := AddScale ('M[E]_n^s -> 'M[D]_n^m) dmscale'.

End Lalgebra.

Section DerKronProd.

Variable E : comRingType.
Variable D : comBimodType E.
Variable der : {derAdd D}.
Notation "\d" := (DerAdd.apply der).
Notation "\\d" := (map_mx \d).


Section Main.

Lemma dmdelta m n i j : \\d (delta_mx i j) = 0 :> 'M[D]_(m,n).
Proof.
  apply/matrixP=> i' j'; rewrite !mxE /=.
  case (_ && _).
  - by rewrite der1.
  - by rewrite der0.
Qed.

Variable m1 n1 m2 n2 : nat.
Implicit Types A : 'M[E]_(m1,n1).
Implicit Types B : 'M[E]_(m2,n2).

(* Matrix derivation is also derivative (has Lebniz product rule) for Kronecker product, like it is for matrix multiplication *)
Lemma dm_lrkron A B : \\d (A *o B) = \\d A *or B + A *ol \\d B.
Proof.
  apply/matrixP => i j.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite mxE kronE mxE lkronE rkronE derM !mxE.
Qed.

End Main.

Section Corollaries.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m,n).

Lemma dm_lkron1mx A : \\d (I *o A) = (I : 'M_(r,_)) *ol \\d A.
Proof.
  by rewrite dm_lrkron dmI rkron0mx add0r.
Qed.

Lemma dm_rkronmx1 A : \\d (A *o I) = \\d A *or (I : 'M_(_,r)).
Proof.
  by rewrite dm_lrkron dmI lkronmx0 addr0.
Qed.

End Corollaries.

End DerKronProd.

(* Lift a matrix of 'M[R]_(m,n) into 'M[E]_(m,n), where E : lalgTyp R *)
Section Lift.

Variable R : ringType.
Variable E : lalgType R.
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Implicit Types D : 'M[R]_(n,r).

Notation lift := (map_mx (in_alg E)).

Lemma lift_mul C D : lift (C *m D) = lift C *m lift D.
Proof.
  apply/matrixP=> i j; rewrite !mxE raddf_sum.
  apply eq_bigr => k.
  by rewrite !mxE -scalerAl mul1r scalerA.
Qed.

Lemma lift_vec C : lift (vec C) = vec (lift C).
  by rewrite map_vec.
Qed.

End Lift.

Local Notation lift := (map_mx (in_alg _)).
Local Notation lift_to E := (map_mx (in_alg E)).

(* Matrix derivation is commutative with multiplication by a (lifted) constant matrix *)
Section DmLift.

Variable R : ringType.
Variable E : algType R.
Variable V : bimodType E E.
Variable der : {linearDer E -> V}.
Notation "\d" := (LinearDer.apply der).
Notation "\\d" := (map_mx \d).
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Implicit Types D : 'M[R]_(n,r).

Lemma dmc C : \\d (lift_to E C) = 0.
Proof.
  by apply/matrixP=> i j; rewrite !mxE linearZ /= /cscale der1 scaler0.
Qed.

Lemma dmcl C (A : 'M[E]_(_, r)) : \\d (lift C *m A) = lift C *ml \\d A.
Proof.
  by rewrite dmM dmc rmul0mx add0r.
Qed.

Lemma dmcr (A : 'M[E]_(r, _)) C : \\d (A *m lift C) = \\d A *mr lift C.
Proof.
  by rewrite dmM dmc lmulmx0 addr0.
Qed.

End DmLift.

Module Notations.

Notation lift_to E := (map_mx (in_alg E)).
Notation lift := (map_mx (in_alg _)).

End Notations.
