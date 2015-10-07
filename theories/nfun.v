(* (c) Copyright ? *)

(*****************************************************************************
  This file defines the algebra of finite-arity functions and the gradient
  operator on them.

  * Fun (the algebra of n-arity functions, which is a unital commutative algebra, 
    with n formal arguments (or variables), and a composition (or substitution/
    application/binding) operation):  
         funType n R == interface type for an Fun structure with     
                        arity n and scalars of type R; R must have a ringType  
                        structure.                                       
   FunMixin arg comp == builds an Fun mixin from an n-length column vector of 
                        formal arguments and a composition operation. 
                        Each formal argument x_i can be seen as a n-arity 
                        function that returns the namesake argument, i.e. 
                        x_i = fun x1 x2 ... xn => xi.
                  \x == the vector of formal arguments (the "basis vector"). The
                        ambient funType structure is infered.
                \x_i == the i-th formal argument, i.e. the i-th element of \x
              f \o v == the composition of f with an n-length column vector of
                        functions v. (f : E, v : 'cV[E]_n, E : funType n
                        R). This operation returns an n-arity function which is
                        f with x_i replaced by v_i, for all i at the same
                        time. Using the parallel substitution notation, it means
                        f[v_1/x_1, v_2/x_2, ..., v_n/x_n]. We choose total
                        parallel substitution as the primitive operation because
                        partial and/or sequential substitution can be achieved
                        by it with some of v's elements being formal arguments,
                        and in this way we don't need to specify which arguments
                        are to be substituted for.
             A \\o v == map_mx (fun f => f \o v) A. The induced composition of 
                        a matrix of functions. 


  * Gradient (the gradient operator, which is a linear derivation from a function
    to a row vector of functions, called its partial derivatives):  
        {gradient E} == the interface type. Coercible to {linearDer E -> 'rV[E]_n}.
                        The resulting row vector of functions is call the (row)
                        gradient vector or the partial derivative vector. E :
                        funType n R.
                        Since a gradient is a total function from E to 'rV[E]_n,
                        E should be interrepted as infinitely differentiable 
                        functions.
           Jacob d u == flatten_mx (map_mx d u). The Jacobian matrix of a column 
                        vector of functions, which is just the (row) gradient
                        vectors stacked together and flattened into a matrix. d
                        : {gradient E}, u : 'cV[E]_m.
GradientMixin dI dcomp == builds an Gradient mixin from lemmas about the operator's
                        behavior on the basis vector and on function composition.
                        dI : J \x = I.
                        dcomp : forall f v, d (f \o v) = (d f \\o v) *m J v.
                        where J := Jacob d.
    packGradient V m == packs a Gradient mixin into a Gradient structure

  The following lemmas use notations J := (Jacob d) and \\d := (map_mx d).

  This lemma can be used to "read off" the Jacobian matrix from a 
  canonical form:
     jacob_intro : \\d u = A *ml \\d \x -> J u = A

  There are two view to express the chain rules. The first is in terms of (J v):
           chain : d (f \o v) = (d f \\o v) *m J v
     jacob_chain : J (u \\o v) = (J u \\o v) *m J v
  The second is in terms of (\\d v):
          chain2 : d (f \o v) = ((d f \\o v) *ml \\d v) 0 0
    jacob_chain2 : \\d (u \\o v) = (J u \\o v) *ml \\d v

  The first view is analogous to the single-variable derivative chain rule:
    f(g(x))' = f'(g(x)) * g'(x)
    or
    (f \o g)' = (f' \o g) * g'
  The second view is in the usual vector function differentiation format:
    df(v)=J(f,v)*dv

  The (0,0) indexing in chian2 is because the result of (row * col) is a 1x1 
  matrix, not a scalar.                        
                        
******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.
Require Import zmodp.

Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.
Import GRing.

Require Import matrix.
Require Import mxutil.
Import Notations.
Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.

(* The algebraic structure of (up-to) n-variable functions *)
Module Fun.

Section ClassDef.

(* maximum arity (number of formal variables) of each function *)
Variable n : nat.

Record mixin_of (T : ringType) := Mixin {
  (* base variables: x_1, x_2, ..., x_n *)
  arg : 'cV[T]_n;
  (* parallel compose/bind/subst/apply. 
     It is easier to define sequential substitution by parallel substitution, than the other way around. *)
  catcompose : 'cV[T]_n -> T -> T;
  _ : forall v, rmorphism (catcompose v)
}.

(* the underlying ring for constant values *)
Variable R : ringType.

Record class_of T := Class {
  base : UnitComAlgebra.class_of R T; 
  mixin : mixin_of (Ring.Pack base T)
}.

Local Coercion base : class_of >-> UnitComAlgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (@UnitAlgebra.class R phR bT) b =>
  fun m & phant_id m0 m => Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass xT.
Definition unitComAlgType := @UnitComAlgebra.Pack R phR cT xclass xT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
End ClassDef.

Module Exports.
Coercion base : class_of >-> UnitComAlgebra.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion unitComAlgType : type >-> UnitComAlgebra.type.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Canonical ringType.
Canonical unitRingType.
Canonical lmodType.
Canonical lalgType.
Canonical algType.
Canonical unitAlgType.
Canonical unitComAlgType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Canonical comRingType.
Canonical comUnitRingType.

Notation funType n R := (type n (Phant R)).
Notation FunType n R T a := (@pack n _ (Phant R) T _ a _ _ id _ id).
Notation FunMixin := Mixin.

End Exports.

End Fun.
Import Fun.Exports.

Definition basis n (R : ringType) (E : funType n R) := Fun.arg E.
Notation "\x" := (basis _) : ring_scope.
Definition arg n (R : ringType) (E : funType n R) i := basis E i 0.
Notation "'\x_' i" := (arg _ i) (at level 0, format "'\x_' i") : ring_scope.
Definition catcompose {n} {R : ringType} {E : funType n R} := Fun.catcompose E.
Notation "v \; f" := (catcompose v f) : ring_scope.
Notation "f \o v" := (catcompose v f) : ring_scope.
(* induced composition for a matrix of functions *)
Notation "v \\; A" := (map_mx (catcompose v) A) (at level 50).
Notation "A \\o v" := (map_mx (catcompose v) A) (at level 50).

Section FunTheory.

Variable n : nat.
Variable R : ringType.
Variable E : funType n R.
Variable v : 'cV[E]_n.

Lemma catcompose_is_rmorphism : rmorphism (catcompose v).
Proof.
  by case: E v => ? [] ? [].
Qed.

Canonical catcompose_rmorphism := RMorphism catcompose_is_rmorphism.

End FunTheory.

(* Gradient: a derivation operator defined by the partial derivatives *)
Module Gradient.

Section ClassDef.

Variable n : nat.
Variable R : ringType.
(* n-variable functions *)
Variable E : funType n R.

Section Mixin.

(* the gradient/derivation operator *)
Variable d : E -> 'rV[E]_n.
(* the Jacobian matrix of a vector of functions, which is just the gradients stacked together *)
Definition jacob m (v : 'cV[E]_m) := flatten_mx (map_mx d v).

Notation J := jacob.

Record mixin_of := Mixin {
  (* behavior of the derivation on base variables *)
  _ : J \x = I;
  (* behavior of the derivation on composition, which is the "chain rule" *)
  _ : forall f v, d (f \o v) = (d f \\o v) *m J v
}.

End Mixin.

Record class_of d := Class {
  base : linearDer d;
  mixin : mixin_of d
}.

Local Coercion base : class_of >-> LinearDer.class_of.
Local Coercion mixin : class_of >-> mixin_of.
                         
Structure map (phE : phant E) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phE : phant E) (d d2 : E -> 'rV[E]_n) (cF : map phE).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id d2 (apply cF) & phant_id fA class :=
  @Pack phE d fA.

Definition pack (fZ : mixin_of d) :=
   fun (bF : LinearDer.map (Phant (E -> 'rV[E]_n))) fA & phant_id (LinearDer.class bF) fA =>
   Pack phE (Class fA fZ).

Definition to_der := DerMorph class.
Definition to_add := Additive class.
Definition to_derAdd := DerAdd class.
Definition to_linear := Linear class.
Definition to_linearDer := LinearDer class.

End ClassDef.

Module Exports.
Notation gradient d := (class_of d).
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> LinearDer.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion to_linearDer : map >-> LinearDer.map.
Canonical to_der.
Canonical to_add.
Canonical to_linear.
Canonical to_derAdd.
Canonical to_linearDer.
Notation Gradient fA := (Pack (Phant _) fA).
Notation packGradient E fA := (@pack _ _ _ (Phant E) _ fA _ _ id).
Notation "{ 'gradient' E }" := (map (Phant E))
  (at level 0, format "{ 'gradient'  E }") : ring_scope.
Notation "[ 'gradient' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'gradient'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'gradient' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'gradient'  'of'  f ]") : form_scope.
Notation GradientMixin := Mixin.

Notation Jacob := jacob.

End Exports.

End Gradient.
Import Gradient.Exports.

Section GradientTheory.

Variables (n : nat) (R : ringType) (E : funType n R) (d : {gradient E}). 
Notation J := (Jacob d).
Notation "\\d" := (map_mx d).

Lemma fold_Jacob : forall m (v : 'cV_m), flatten_mx (\\d v) = J v.
Proof.
  by [].
Qed.

Lemma jacob_single f : J f%:M = d f.
Proof.
  by rewrite /Jacob flatten_mx11 !mxE eqxx.
Qed.

Section ChainRules.

Variables (m : nat) (u : 'cV[E]_m) (v : 'cV[E]_n).

(* analogous to the single-variable derivative base rule:
   x' = 1 *)
Lemma jacob_base : J \x = I.
Proof. by case: d => /= dd [] base []. Qed.

Lemma chain f : d (f \o v) = (d f \\o v) *m J v.
Proof. by case: d => /= dd [] base []. Qed.

(* another view of the chain rule lemmas, in the format of df(v)=J(f,v)*dv *)

(* the (0,0) indexing is because the result of (row * col) is a 1x1 matrix, not a scalar *)
Lemma chain2 f : d (f \o v) = ((d f \\o v) *ml \\d v) 0 0.
Proof.
  by rewrite chain -flatten_mx11 flatten_lmul.
Qed.

Lemma jacob_chain2 : \\d (u \\o v) = (J u \\o v) *ml \\d v.
Proof.
  apply/matrixP => i j.
  rewrite !mxE chain.
  apply/matrixP => ii jj.
  rewrite !mxE !ord1 !summxE.
  apply eq_bigr => k _.
  by rewrite !mxE.
Qed.

Lemma fold_jacob : flatten_mx (\\d u) = J u.
Proof. by []. Qed.

(* analogous to the single-variable derivative chain rule:
   f(g(x))' = f'(g(x)) * g'(x) or (f \o g)' = (f' \o g) * g' *)
Lemma jacob_chain  : J (u \\o v) = (J u \\o v) *m J v.
Proof.
  by rewrite /Jacob jacob_chain2 flatten_lmul.
Qed.

End ChainRules.

Variables (m : nat) (u : 'cV[E]_m).

Lemma jacob_intro A : \\d u = A *ml \\d \x -> J u = A.
Proof.
  by move => h; rewrite /Jacob h /= flatten_lmul /= fold_jacob jacob_base mulmx1.
Qed.

End GradientTheory.

Section Hessian.

Variables (n : nat) (R : ringType) (E : funType n R) (der : {gradient E}). 
Notation "\d" := (Gradient.apply der).
Notation J := (Jacob \d).
Notation "\\d" := (map_mx \d).

Definition Hessian f := J (\d f)^T.

Lemma fold_Hessian f : J (\d f)^T = Hessian f.
Proof. by []. Qed.

(* Generalized Hessian *)
Definition GHessian m (v : 'cV_m) := \\d (J v)^T.

Lemma fold_GHessian m (v : 'cV_m) : \\d (J v)^T = GHessian v.
Proof. by []. Qed.

Lemma GHessian_Hessian f : flatten_mx (GHessian f%:M) = Hessian f.
Proof.
  by rewrite /GHessian /Hessian /Jacob flatten_mx11 map_mxE scalar_mxE.
Qed.

Notation H := Hessian.
Notation GH := GHessian.

Notation "A \\\o v" := (map_mx (map_mx (catcompose v)) A) (at level 50).

Require Import mxdiff.

Notation "[ x ]" := (@scalar_mx _ 1 x).

Lemma ghessian_chain f v : GH [f \o v] = GH v *mr (\d f \\o v)^T + ((J v)^T *m (H f \\o v)) *ml \\d v.
Proof.
  set goal := RHS.
  by rewrite -map_scalar_mx /= /GHessian jacob_chain trmx_mul dmM /= !fold_GHessian map_trmx jacob_chain2 !lmulmxA jacob_single -/Hessian !fold_Hessian -map_trmx.
Qed.

Lemma hessian_chain f v : H (f \o v) = flatten_mx (GH v *mr (\d f \\o v)^T) + (J v)^T *m (H f \\o v) *m J v.
Proof.
  set goal := RHS.
  by rewrite -GHessian_Hessian ghessian_chain flattenD flatten_lmul !fold_Jacob.
Qed.

End Hessian.

Export Fun.Exports.
Export Gradient.Exports.