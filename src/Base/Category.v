
Require Import Coq.Program.Equality.
From mathcomp Require Import ssreflect.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Category.Base.Logic.

Set Universe Polymorphism.

Structure Category : Type :=
  {
    Obj: Type;
    Hom : Obj -> Obj -> Type;
    Hom_Id : forall X, Hom X X;
    Hom_comp : forall {X Y Z : Obj}, Hom Y Z -> Hom X Y -> Hom X Z;

    (* Conditions *)
    Hom_assoc : forall {X Y Z W}, forall (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y), Hom_comp (Hom_comp f g) h = Hom_comp f (Hom_comp g h);
    Hom_IdL : forall X Y, forall (f : Hom X Y), Hom_comp (Hom_Id Y) f = f;
    Hom_IdR : forall X Y, forall (f : Hom X Y), Hom_comp f (Hom_Id X) = f
  }.

Global Arguments Hom {c}.
Global Arguments Hom_comp {c} {X Y Z}.
Global Arguments Hom_assoc {c} {X Y Z W}.

Notation "g \o{ C } f" := (@Hom_comp C _ _ _ g f) (at level 60, right associativity).
Notation "g \o f" := (@Hom_comp _ _ _ _ g f) (at level 60, right associativity).
Notation "\Id_{ C } X" := (@Hom_Id C X) (at level 20, no associativity).
Notation "\Id X" := (@Hom_Id _ X) (at level 20, no associativity).

Section Isomorphism.

  Context {C : Category}.

  Definition isomorphism_pair {X Y : Obj C} (f : Hom X Y) (g : Hom Y X) :=
    (g \o f = \Id X) /\ (f \o g = \Id Y).
  
  Definition isomorphism {X Y : Obj C} (f : Hom X Y) :=
    exists g : Hom Y X, isomorphism_pair f g.

  Definition isomorphic : relation (Obj C) :=
    fun X Y => exists f : Hom X Y, isomorphism f.

  Lemma isomorphism_pair_unqR : forall {X Y : Obj C} (f : Hom X Y) (g1 g2 : Hom Y X),
      isomorphism_pair f g1 /\ isomorphism_pair f g2 -> g1 = g2.
  Proof.
    move => X Y f g1 g2 [[eqgf1 eqfg1] [eqgf2 eqfg2]].
    cut((g1 \o f) \o g1 = (g1 \o f) \o g2).
    {
      move: eqgf1 =>->.
      rewrite Hom_IdL.
      rewrite Hom_IdL.
      by [].
    }
    rewrite (Hom_assoc g1 f g1).
    rewrite (Hom_assoc g1 f g2).
    move: eqfg1 =>->.
    move: eqfg2 =>->.
    by [].
  Qed.

  Lemma isomorphism_pair_unqL : forall {X Y : Obj C} (f1 f2 : Hom X Y) (g : Hom Y X),
      isomorphism_pair f1 g /\ isomorphism_pair f2 g -> f1 = f2.
  Proof.
    move => X Y f1 f2 g [[eqgf1 eqfg1] [eqgf2 eqfg2]].
    cut(f1 \o (g \o f1) = f2 \o (g \o f1)).
    {
      move: eqgf1 =>->.
      rewrite Hom_IdR.
      rewrite Hom_IdR.
      by [].
    }
    rewrite <- (Hom_assoc f1 g f1).
    rewrite <- (Hom_assoc f2 g f1).
    move: eqfg1 =>->.
    move: eqfg2 =>->.
    by [].
  Qed.

  Lemma isomorphism_pair_id : forall X, isomorphism_pair (\Id X) (\Id X).
  Proof.
    move => X.
    by split; move: Hom_IdL =>->.
  Qed.
  
  Lemma isomorphism_id : forall X, isomorphism (\Id X).
  Proof.
    move => X.
    exists (\Id X).
    exact: isomorphism_pair_id.
  Qed.
  
  Instance isomorphic_reflexive : Reflexive isomorphic.
  Proof.
    intro X.
    exists (\Id X).
    exact (isomorphism_id X).
  Qed.

  Instance isomorphic_symmetric : Symmetric isomorphic.
  Proof.
    intros X Y isoH.
    destruct isoH as [f isoH].
    destruct isoH as [g [eqgf eqfg]].
    exists g.
    exists f.
    split; assumption.
  Qed.

  Instance isomorphic_transitive : Transitive isomorphic.
  Proof.
    intros X Y Z isoH1 isoH2.
    destruct isoH1 as [f1 [g1 [eqgf1 eqfg1]]].
    destruct isoH2 as [f2 [g2 [eqgf2 eqfg2]]].
    exists (f2 \o f1).
    exists (g1 \o g2).
    split.
    {
      rewrite (Hom_assoc g1).
      rewrite <- (Hom_assoc g2).
      rewrite eqgf2.
      rewrite Hom_IdL.
      rewrite eqgf1.
      reflexivity.
    } {
      rewrite (Hom_assoc f2).
      rewrite <- (Hom_assoc f1).
      rewrite eqfg1.
      rewrite Hom_IdL.
      rewrite eqfg2.
      reflexivity.
    }
  Qed.

  Global Program Instance isomorphic_equivalene : Equivalence isomorphic.

End Isomorphism.
    
Notation "x ~~~ y" := (@isomorphic _ x y) (at level 70, no associativity).
Notation "x ~~~ y 'in' C" := (@isomorphic C x y) (at level 70, y at next level, no associativity).


Section Hom_JMeq.

  Context {C : Category}.
  
  Definition HomId' {X Y : Obj C} (eqH : X = Y) : Hom X Y.
    rewrite <- eqH.
    exact (\Id X).
  Defined.

  Lemma HomId'_id: forall {X : Obj C} (eqH : X = X), HomId' eqH = \Id X.
  Proof.
    move => X eqH.
    rewrite /HomId' /=.
    rewrite /eq_rect.
    rewrite(_:eqH = eq_refl).
    reflexivity.
    apply: p_proof_irrelevance.
  Qed.

  Lemma HomId'_sym_id : forall {X Y : Obj C} (eq1 : Y = X) (eq2 : X = Y),
      HomId' eq1 \o HomId' eq2 = \Id X.
  Proof.
    move => X Y eq1 eq2.
    subst.
    repeat rewrite HomId'_id.
    rewrite Hom_IdL.
    reflexivity.
  Qed.    

  Definition Hom_eq' {X1 X2 Y1 Y2 : Obj C} (f1 : Hom X1 Y1) (f2 : Hom X2 Y2) :=
    exists eqX : X1 = X2, exists eqY : Y1 = Y2, HomId' eqY \o f1 = f2 \o HomId' eqX.
    
  Lemma Hom_eq'_refl : forall {X Y : Obj C} (f : Hom X Y), Hom_eq' f f.
  Proof.
    move => X Y f.
    rewrite /Hom_eq'.
    exists (eq_refl X).
    exists (eq_refl Y).
    repeat rewrite HomId'_id.
    rewrite Hom_IdL.
    rewrite Hom_IdR.
    reflexivity.
  Qed.

  Lemma Hom_eq'_sym : forall {X1 X2 Y1 Y2 : Obj C} {f1 : Hom X1 Y1} {f2 : Hom X2 Y2}, Hom_eq' f1 f2 -> Hom_eq' f2 f1.
  Proof.
    move => X1 X2 Y1 Y2 f1 f2.
    move => [eqX [eqY eqH]].
    rewrite /Hom_eq'.
    exists (eq_sym eqX).
    exists (eq_sym eqY).
    subst.
    move: eqH.
    repeat rewrite HomId'_id.
    repeat rewrite Hom_IdL.
    repeat rewrite Hom_IdR.
    by [].
  Qed.

  Lemma Hom_eq'_trans : forall {X1 X2 X3 Y1 Y2 Y3 : Obj C} {f1 : Hom X1 Y1} {f2 : Hom X2 Y2} {f3 : Hom X3 Y3}, Hom_eq' f1 f2 -> Hom_eq' f2 f3 -> Hom_eq' f1 f3.
  Proof.
    move => X1 X2 X3 Y1 Y2 Y3 f1 f2 f3.
    move => [eqX1 [eqY1 eqH1]].
    move => [eqX2 [eqY2 eqH2]].
    exists (eq_trans eqX1 eqX2).
    exists (eq_trans eqY1 eqY2).
    move: eqH1 eqH2.
    subst.
    repeat rewrite HomId'_id.
    repeat rewrite Hom_IdL.
    repeat rewrite Hom_IdR.
    by move =>-> =>->.
  Qed.

  Lemma Hom_eq'_jmeq {X1 X2 Y1 Y2 : Obj C} :
    forall(f1 : Hom X1 Y1) (f2 : Hom X2 Y2),
      (Hom_eq' f1 f2) -> f1 ~= f2.
  Proof.
    move => f1 f2.
    case => eqX.
    case => eqY.
    subst.
    repeat rewrite HomId'_id.
    rewrite Hom_IdL.
    rewrite Hom_IdR.
    move =>->.
    reflexivity.
  Qed.

  Lemma Hom_eq'_eq {X Y : Obj C} :
    forall(f1 f2 : Hom X Y),
      (Hom_eq' f1 f2) -> f1 = f2.
  Proof.
    move => f1 f2.
    move/ Hom_eq'_jmeq.
    exact: JMeq_eq.
  Qed.

  Lemma eq_Hom_eq' {X Y : Obj C} :
    forall(f1 f2 : Hom X Y),
      f1 = f2 -> (Hom_eq' f1 f2).
  Proof.
    move => f1 f2 =>->.
    exact: Hom_eq'_refl.
  Qed.
  
End Hom_JMeq.

  