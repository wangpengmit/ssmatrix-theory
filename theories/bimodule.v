(* (c) Copyright ? *)

(*****************************************************************************
  Bimodule.

  * Rmodule (right module):  
          rmodType R == interface type for an Rmodule structure with     
                        scalars of type R; R must have a ringType        
                        structure.                                       
 RmodMixin scalA scalv1 scalDl scalDr == builds an Rmodule mixin from the   
                        algebraic properties of the scaling operation;   
                        the module carrier type must have a zmodType     
                        structure, and the scalar carrier must have a    
                        ringType structure.         
                        The essential difference between Rmodule and Lmodule
                        is the associativity rule: 
                          v :* (a * b) = v :* a :* b.
                        That means in a Rmodule it is the left operant of *
                        that acts on v first, while in a Lmodule it is the right
                        operant that acts first. Hence, a R-Rmodule is equivalent
                        (and coercible) to R^c-Lmodule, where R^c is the converse
                        ring of R, swapping left and right operant of *.
      RmodType R V m == packs the mixin v to build an Rmodule of type    
                        rmodType R. The carrier type V must have a       
                        zmodType structure.                              
              v :* a == v right-scaled by a, when v is in an Rmodule V and a   
                        is in the scalar Ring of V.                      


  * Bimodule (bimodule, both left module and right module, with a compatibility 
              property):  
       bimodType R S == interface type for a bimodule structure with     
                        left scalars of type R and right scalars of type S. 
                        Both R and S must have a ringType structure. 
 BimodType R S V scalA == packs scalA : forall a v b, a *: (v :* b) = a *: v :* b 
                        into a Bimodule of type bimodType R S. The carrier 
                        type V must have both lmodType R and rmodType S canonical 
                        structures.                                      


  * ComBimodule (commutative bimodule, bimodule whose left and right scale are
                 interchangeable):  
      comBimodType R == interface type for a ComBimodule structure with     
                        both left and right scalars of type R.
                        R must have a ringType structure. 
                        It coerces to bimodType R R.
 ComBimodType R V comm == packs comm : forall a v, v :* a = a *: v
                        into a ComBimodule of type comBimodType R. The carrier 
                        type V must have a bimodType R R canonical structure.


  * UnitComAlgebra (unit and commutative algebra):  
      unitComAlgType R == interface type for a UnitComAlgebra structure with     
                        scalars of type R.
                        R must have a ringType structure. 
 UnitComAlgType R A comm == packs comm : commutative *%R
                        into a UnitComAlgebra of type unitComAlgType R. The 
                        carrier type A must have a unitAlgType R canonical 
                        structure.
                        
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

(* Commutative Unit Algebra *)
Module UnitComAlgebra.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) := Class {
  base : UnitAlgebra.class_of R T;
  mixin : commutative (Ring.mul base)
}.

Local Coercion base : class_of >-> UnitAlgebra.class_of.
Definition base2 R (m : class_of R) := @ComUnitRing.Class _ (ComRing.Class (@mixin R m)) m.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
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
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
End ClassDef.

Module Exports.
Coercion base : class_of >-> UnitAlgebra.class_of.
Coercion base2 : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.

Notation unitComAlgType R := (type (Phant R)).
Notation UnitComAlgType R T a := (@pack _ (Phant R) T _ a _ _ id _ id).

End Exports.

End UnitComAlgebra.

Import UnitComAlgebra.Exports.


Local Notation "R ^cc" := (converse_ringType R) (at level 2, format "R ^cc") : type_scope.

(* Right module: a R Rmodule is just a R^c Lmodule *)
Module Rmodule.

Section ClassDef.

Variable R : ringType.
Definition class_of := (Lmodule.class_of R^cc).

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : Lmodule.mixin_of R^cc (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Lmodule.Class R^cc T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition lmodType :=@Lmodule.Pack R^cc (Phant _) cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Notation rmodType R := (type (Phant R)).
Notation RmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation "[ 'rmodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'rmodType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'rmodType'  R  'of'  T ]") : form_scope.
End Exports.

End Rmodule.
Import Rmodule.Exports.

Definition rscale {R : ringType} {V : rmodType R} (v : V) (b : R) : V := (b : _^c) *: v.
Notation ":*%R" := (@rscale _ _).
Notation "v :* b" := (rscale v b) (at level 40) : ring_scope.

Section RmoduleTheory.

Variables (R : ringType) (V : rmodType R).
Implicit Types (v : V).

Lemma scaleAr v a b : v :* (a * b) = v :* a :* b.
Proof.
  by rewrite /rscale scalerA.
Qed.

End RmoduleTheory.

(* Make a Rmodule from properties suitable for right-scale *)
Section MakeRmodule.

Variable R : ringType.
Variable V : zmodType.
Variable rscale : V -> R -> V.
Hypothesis rassoc : forall v a b, rscale v (a * b) = rscale (rscale v a) b.
Hypothesis rightid : forall v, rscale v 1 = v.
Hypothesis left_distr : forall v1 v2 a, rscale (v1 + v2) a = rscale v1 a + rscale v2 a.
Hypothesis right_distr : forall v a b, rscale v (a + b) = rscale v a + rscale v b.
Implicit Types a b : R^c.
Let lscale := (fun (a : R^c) v => rscale v a).
Lemma lassoc a b v : lscale a (lscale b v) = lscale (a * b) v.
Proof. by subst lscale; simpl; rewrite rassoc. Qed.

Lemma leftid : left_id 1 lscale.
Proof. by move => v; subst lscale; simpl; rewrite rightid. Qed.

Lemma rdist : right_distributive lscale +%R.
Proof. by move => a v1 v2; subst lscale; simpl; rewrite left_distr. Qed.

Lemma ldist v a b : lscale (a + b) v = lscale a v + lscale b v.
Proof. by subst lscale; simpl; rewrite right_distr. Qed.

Definition RmodMixin := @LmodMixin _ (Zmodule.Pack _ V) _ lassoc leftid rdist ldist.
Definition mk_rmodType := Eval hnf in RmodType _ _ RmodMixin.
Definition mk_c_lmodType := Eval hnf in LmodType _ _ RmodMixin.

End MakeRmodule.

Module RmoduleFromLmodule.
Section RmoduleFromLmodule.

Variable R : ringType.
Variable V : lmodType R.

Let rscale (v : V) (a : R^c) := (a : R) *: v.
Lemma rassoc : forall v a b, rscale v (a * b) = rscale (rscale v a) b.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scalerA.
Qed.

Lemma rightid : forall v, rscale v 1 = v.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scale1r.
Qed.

Lemma left_distr : forall v1 v2 a, rscale (v1 + v2) a = rscale v1 a + rscale v2 a.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scalerDr.
Qed.

Lemma right_distr : forall v a b, rscale v (a + b) = rscale v a + rscale v b.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scalerDl.
Qed.

Definition RmodMixin_from_lmod := RmodMixin rassoc rightid left_distr right_distr.
Definition rmod_from_lmod := Eval hnf in RmodType R^c V RmodMixin_from_lmod.

End RmoduleFromLmodule.
End RmoduleFromLmodule.

Module RmoduleFromComm.
Section RmoduleFromComm.

Variable R : comRingType.
Variable V : lmodType R.

Let rscale (v : V) (a : R) := a *: v.
Lemma rassoc : forall v a b, rscale v (a * b) = rscale (rscale v a) b.
Proof. 
  intros; subst rscale; simpl.
  by rewrite !scalerA mulrC.
Qed.

Lemma rightid : forall v, rscale v 1 = v.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scale1r.
Qed.

Lemma left_distr : forall v1 v2 a, rscale (v1 + v2) a = rscale v1 a + rscale v2 a.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scalerDr.
Qed.

Lemma right_distr : forall v a b, rscale v (a + b) = rscale v a + rscale v b.
Proof. 
  intros; subst rscale; simpl.
  by rewrite scalerDl.
Qed.

Definition RmodMixin_from_comm := RmodMixin rassoc rightid left_distr right_distr.
Definition rmod_from_comm := Eval hnf in RmodType R V RmodMixin_from_comm.

End RmoduleFromComm.
End RmoduleFromComm.


(* Bimodule : a R-S-bimodule is both a R-Lmodule and a S-Rmodule, with a compatibility property *)
Module Bimodule.

Section ClassDef.

Variable R S : ringType.

Definition axiom (V : Type) (lscale : R -> V -> V) (rscale : V -> S -> V) := forall a v b, lscale a (rscale v b) = rscale (lscale a v) b.

Record class_of (T : Type) : Type := Class {
  base : Rmodule.class_of S T;
  mixin : Lmodule.mixin_of R (Zmodule.Pack base T);
  ext : @axiom T (Lmodule.scale mixin) (@rscale S (Rmodule.Pack _ base T))
}.

Local Coercion base : class_of >-> Rmodule.class_of.
Definition base2 R m := Lmodule.Class (@mixin R m).
Local Coercion base2 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) (phS : phant S) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (phS : phant S) (T : Type) (cT : type phR phS).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR phS T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T lscale rscale (axT : @axiom T lscale rscale) :=
  fun bT b & phant_id (@Rmodule.class S phS bT) (b : Rmodule.class_of S T) =>
  fun mT m & phant_id (@Lmodule.class R phR mT) (@Lmodule.Class R T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (Phant S) (@Class T b m ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition to_zmodType := @Zmodule.Pack cT xclass xT.
Definition to_lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition to_rmodType := @Rmodule.Pack S phS cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Rmodule.class_of.
Coercion base2 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion to_zmodType : type >-> Zmodule.type.
Canonical to_zmodType.
Coercion to_lmodType : type >-> Lmodule.type.
Canonical to_lmodType.
Coercion to_rmodType : type >-> Rmodule.type.
Canonical to_rmodType.
Notation bimodType R S := (type (Phant R) (Phant S)).
Notation BimodType R S T a := (@pack _ _ (Phant R) (Phant S) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'bimodType' R ',' S 'of' T 'for' cT ]" := (@clone _ _ (Phant R) (Phant S) T cT _ idfun)
  (at level 0, format "[ 'bimodType'  R ',' S  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'bimodType' R ',' S 'of' T ]" := (@clone _ _ (Phant R) (Phant S) T _ _ id)
  (at level 0, format "[ 'bimodType'  R ',' S  'of'  T ]") : form_scope.

End Exports.

End Bimodule.
Import Bimodule.Exports.

Section BimoduleTheory.

Variables (R S : ringType) (V : bimodType R S).
Implicit Types (v : V).

Lemma scalerlA (a : R) v b : a *: (v :* b) = a *: v :* b.
Proof. 
  by case: V v => sort [] base mixin ext T v; rewrite /rscale /scale ext.
Qed.

End BimoduleTheory.


(* Commutative Bimodule : a bimodule whose left and right scale are interchangeable *)
Module ComBimodule.

Section ClassDef.

Variable R : ringType.

Definition mixin_of (V : bimodType R R) := 
  forall (a : R) (v : V), v :* a = a *: v.

Record class_of (T : Type) : Type := Class {
  base : Bimodule.class_of R R T;
  mixin : mixin_of (Bimodule.Pack _ _ base T)
}.

Local Coercion base : class_of >-> Bimodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Bimodule.Pack _ _ (Phant R) (Phant R) T b0 T)) :=
  fun bT b & phant_id (@Bimodule.class _ _ phR phR bT) b =>
  fun m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition to_zmodType := @Zmodule.Pack cT xclass xT.
Definition to_lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition to_rmodType := @Rmodule.Pack R phR cT xclass xT.
Definition to_bimodType := @Bimodule.Pack R R phR phR cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Bimodule.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion to_zmodType : type >-> Zmodule.type.
Canonical to_zmodType.
Coercion to_lmodType : type >-> Lmodule.type.
Canonical to_lmodType.
Coercion to_rmodType : type >-> Rmodule.type.
Canonical to_rmodType.
Coercion to_bimodType : type >-> Bimodule.type.
Canonical to_bimodType.
Notation comBimodType R := (type (Phant R)).
Notation ComBimodType R T a := (@pack _ (Phant R) T _ a _ _ id _ id).
Notation "[ 'comBimodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'comBimodType'  R 'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'comBimodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'comBimodType'  R  'of'  T ]") : form_scope.

End Exports.

End ComBimodule.
Import ComBimodule.Exports.

Section ComBimoduleTheory.

Variables (R : ringType) (V : comBimodType R).
Implicit Types (v : V).

Lemma lrscaleC (a : R) v : v :* a  = a *: v.
Proof. by case: V v => sort [] base. Qed.

End ComBimoduleTheory.


Export UnitComAlgebra.Exports.
Export Rmodule.Exports.
Export Bimodule.Exports.
Export ComBimodule.Exports.