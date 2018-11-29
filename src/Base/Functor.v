Require Import Coq.Program.Equality.
From Coq.Logic Require Import JMeq EqdepFacts.
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category.

Open Scope equiv_scope.

Structure Functor (C D : Category) : Type :=
  {
    FApp : Obj C -> Obj D;
    FAppH : forall {X Y : Obj C}, Hom X Y -> Hom (FApp X) (FApp Y);

    (* Conditions *)
    FAppH_comp_eq : forall {X Y Z : Obj C} (f : Hom Y Z) (g : Hom X Y), FAppH (f \o g) = (FAppH f) \o (FAppH g);
    Functor_id_eq : forall {X : Obj C}, FAppH (\Id X) = \Id (FApp X)
  }.

Global Arguments FApp {C D}.
Global Arguments FAppH {C D} f {X Y}.
Global Arguments FAppH_comp_eq {C D} f {X Y Z}.

Lemma ToFunctorEq :
  forall {C D : Category} (F G : Functor C D),
    (forall {X Y : Obj C} (f : Hom X Y), Hom_eq' (FAppH F f) (FAppH G f)) ->
    F = G.
Proof.
  move => C D.
  case => AppF AppHF compeqF ideqF.
  case => AppG AppHG compeqG ideqG.
  rewrite /=.
  move => cond.
  have: AppF = AppG.
  {
    apply: functional_extensionality.
    move => X.
    move: (cond X X (\Id X)).
    case.
    by [].
  }
  move => eqApp.
  subst.
  have: AppHF = AppHG.
  {
    apply: functional_extensionality_dep => X.
    apply: functional_extensionality_dep => Y.
    apply: functional_extensionality => f.
    case: (cond _ _ f).
    move => eqX.
    case.
    move => eqY.
    repeat rewrite HomId'_id.
    rewrite Hom_IdL.
    rewrite Hom_IdR.
    by [].
  }
  move => eqApp.
  subst.
  have: (compeqF = compeqG /\ ideqF = ideqG).
  {
    split; exact: p_proof_irrelevance.
  }
  case.
  move =>-> =>->.
  by [].
Qed.  


      