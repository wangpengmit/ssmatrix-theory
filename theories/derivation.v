(* (c) Copyright ? *)

(*****************************************************************************
  Derivation. This file defines the hierarchy of derivation morphisms. 

  * DerMorph (derivative morphism):  
         derMorph f == forall a b, f (a * b) = f a *: b + a :* f b.
                       It says f of type R -> V is derivative, i.e., enjoys 
                       the Lebniz product rule.
                       R must have a ringType canonical structure.
                       V must have a (bimodType R R) canonical structure.
  {derMorph R -> V} == the interface type for a Structure (keyed on     
                       a function f : R -> V) that encapsulates the     
                       derivative property.
DerMorphFor V der_f == packs der_f : derMorph f into an derMorph
                       function structure of type {derMorph R -> V}.    
     DerMorph der_f == DerMorphFor _ der_f

  Properties of derMorph f: 
                derM : f (a * b) = f a *: b + a :* f b
                der1 : f 1 = 0
                der0 : f 0 = 0
                derV : a \is a GRing.unit -> f (a^-1) = - a^-1 * f a / a
                       where a : R and R : unitRingType


  * DerAdd (derivative and additive):  
    {derAdd R -> V} == the interface type for a Structure (keyed on     
                       a function f : R -> V) that encapsulates the     
                       derivative and additive property.
     packDerAdd V f == packs the DerMorph and Additive canonical structures on
                       f into a DerAdd structure


  * LinearDer (derivative and linear):  
 {linearDer A -> V} == the interface type for a Structure (keyed on     
                       a function f : A -> V) that encapsulates the     
                       derivative and linear property. 
                       It coerces to {linear A -> V | cscale}.
                       A must have a (lalgType R) canonical structure, where 
                       R : ringType.
                       V must have a (bimodType A A) canonical structure.
         cscale r v == r *: 1 *: v. 
                       r : R, v : V, V : lmodType A, A : lalgType R.
 AddScale (A -> V) scale_f == packs the scalability property scale_f of f into an 
                       linearDer function structure of type {linearDer A -> V}.
                       scale_f should have type: 
                         forall (c : R) (v : A), f (c *: v) = c *: 1 *: f v.
                       f must already have a {derAdd A -> V} canonical structure.

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

Require Import bimodule.

(* Derivative morphism, a morphism that enjoys the Lebniz product rule: f (a * b) = f a * b + a * f b, where f : (R : ringType) -> (V : bimodType R R) *)
Module DerMorph.

Section ClassDef.

Variable R : ringType.
Variable V : bimodType R R.

Definition axiom (f : R -> V) := forall a b, f (a * b) = f a :* b + a *: f b.

Structure map (phV : phant V) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phV : phant V) (f g : R -> V) (cF : map phV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phV f fA.

End ClassDef.

Module Exports.
Notation derMorph f := (axiom f).
Coercion apply : map >-> Funclass.
Notation DerMorphFor V fA := (Pack (Phant V) fA).
Notation DerMorph fA := (DerMorphFor _ fA).
Notation "{ 'derMorph' V }" := (map (Phant V))
  (at level 0, format "{ 'derMorph'  V }") : ring_scope.
Notation "[ 'derMorph' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'derMorph'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'derMorph' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'derMorph'  'of'  f ]") : form_scope.
End Exports.

End DerMorph.
Import DerMorph.Exports.

Section DerMorphTheory.

Variable R : ringType.
Variable V : bimodType R R.
Variable f : {derMorph V}.

Lemma derM a b : f (a * b) = f a :* b + a *: f b.
Proof. by case f. Qed.

Lemma der1 : f 1 = 0.
Proof.
  by apply: (addIr (f (1 * 1))); rewrite add0r {1}mul1r derM scale1r /rscale scale1r.
Qed.

Lemma der0 : f 0 = 0.
Proof.
  by rewrite -(mul0r 0) derM /rscale !scale0r addr0.
Qed.

End DerMorphTheory.

Lemma addNRL {Z : zmodType} (x y : Z) : x + y = 0 -> x = -y.
  move => H.
  rewrite -sub0r.
  rewrite -H.
  rewrite addrK.
  by [].
Qed.

Section Inverse.

Variable R : unitRingType.
Variable V : bimodType R R.
Variable f : {derMorph V}.

Lemma derV x : x \is a GRing.unit -> f (x^-1) = - (x^-1 *: f x :* x^-1).
Proof.
  move => Hu.
  have He: x^-1 *: f (x / x) = 0 by rewrite (mulrV Hu) der1 scaler0.
  rewrite derM  scalerDr scalerlA scalerA (mulVr Hu) scale1r addrC in He.
  by apply addNRL.
Qed.

End Inverse.

Import GRing.

(* Derivative and additive morphism *)
Module DerAdd.

Section ClassDef.

Variable R : ringType.
Variable V : bimodType R R.
Implicit Types f : R -> V.

Record class_of f : Prop := Class {base : derMorph f; mixin : additive f}.

Local Coercion base : class_of >-> derMorph.
Local Coercion mixin : class_of >-> additive.

Structure map (phV : phant V) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phV : phant V) (f g : R -> V) (cF : map phV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phV f fA.

Definition pack f :=
   fun bT b & phant_id (@DerMorph.class R V phV bT) (b : derMorph f) =>
   fun mT m & phant_id (@Additive.class R V (Phant _) mT) m =>
   Pack phV (@Class f b m).

Definition to_der := DerMorph class.
Definition to_add := Additive class.

End ClassDef.

Module Exports.
Notation derAdd f := (class_of f).
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> derMorph.
Coercion mixin : class_of >-> additive.
Coercion to_der : map >-> DerMorph.map.
Canonical to_der.
Coercion to_add : map >-> Additive.map.
Canonical to_add.
Notation DerAdd fA := (Pack (Phant _) fA).
Notation packDerAdd V f := (@pack _ _ (Phant V) f _ _ id _ _ id).
Notation "{ 'derAdd' V }" := (map (Phant V))
  (at level 0, format "{ 'derAdd'  V }") : ring_scope.
Notation "[ 'derAdd' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'derAdd'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'derAdd' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'derAdd'  'of'  f ]") : form_scope.
End Exports.

End DerAdd.
Import DerAdd.Exports.

Module ConstScale.
Module Exports.
Section Def.

Variable R : ringType.
Variable A : lalgType R.
Variable V : lmodType A.
Definition cscale (r : R) (v : V) : V := r%:A *: v.

Lemma cscaleN1r : cscale (-1) =1 -%R.
Proof. by move => v; rewrite /cscale !scaleN1r. Qed.

Lemma cscalerBr a : additive (cscale a).
Proof. by move => v1 v2; rewrite /cscale !scalerBr. Qed.

(* Register that cscale has proper scale laws, required by linear_for *)
Canonical cscale_law := Scale.Law (erefl cscale) cscaleN1r cscalerBr.

End Def.
End Exports.
End ConstScale.
Import ConstScale.Exports.

(* Derivative and linear morphism *)
Module LinearDer.

Section ClassDef.

Variable R : ringType.
Variable A : lalgType R.
Variable V : bimodType A A.
Implicit Types f : A -> V.

Record class_of f : Prop := Class {base : derAdd f; mixin : Linear.mixin_of (@cscale _ _ _) f}.

Local Coercion base : class_of >-> derAdd.
Local Coercion mixin : class_of >-> Linear.mixin_of.
Definition base2 f (c : class_of f) := Linear.Class c c.
Local Coercion base2 : class_of >-> Linear.class_of.

Structure map (phAV : phant (A -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phAV : phant (A -> V)) (f g : A -> V) (cF : map phAV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phAV f fA.

Definition pack (fZ : forall (c : R) (v : A), f (c *: v) = c%:A *: f v) :=
   fun (bF : DerAdd.map (Phant V)) fA & phant_id (DerAdd.class bF) fA =>
   Pack phAV (Class fA fZ).

Definition to_der := DerMorph class.
Definition to_add := Additive class.
Definition to_linear := Linear class.
Definition to_derAdd := DerAdd class.

End ClassDef.

Module Exports.
Notation linearDer f := (class_of f).
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> derAdd.
Coercion base2 : class_of >-> Linear.class_of.
Coercion mixin : class_of >-> Linear.mixin_of.
Coercion to_der : map >-> DerMorph.map.
Canonical to_der.
Coercion to_add : map >-> Additive.map.
Canonical to_add.
Coercion to_linear : map >-> Linear.map.
Canonical to_linear.
Coercion to_derAdd : map >-> DerAdd.map.
Canonical to_derAdd.
Notation LinearDer fA := (Pack (Phant _) fA).
Notation AddScale fAV fZ := (@pack _ _ _ (Phant fAV) _ fZ _ _ id).
Notation "{ 'linearDer' fAV }" := (map (Phant fAV))
  (at level 0, format "{ 'linearDer'  fAV }") : ring_scope.
Notation "[ 'linearDer' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'linearDer'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'linearDer' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'linearDer'  'of'  f ]") : form_scope.
End Exports.

End LinearDer.
Import LinearDer.Exports.

Export DerMorph.Exports.
Export DerAdd.Exports.
Export LinearDer.Exports.
Export ConstScale.Exports.
