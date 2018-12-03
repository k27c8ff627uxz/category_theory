From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import DiscreteCat Univ.FunctorComp Univ.FunctorCategory Product.ProductCategory Product.FunctorCurrying.

Set Universe Polymorphism.

Section Projection.

  Variable C D : Category.

  Program Definition ProjFunc1 : Functor (ProductCat C D) C :=
    {|
      FApp := fun P => fst P;
      FAppH := fun P1 P2 fp => fst fp
    |}.

  Program Definition ProjFunc2 : Functor (ProductCat C D) D :=
    {|
      FApp := fun P => snd P;
      FAppH := fun P1 P2 fp => snd fp
    |}.

End Projection.

Lemma Curry_to_IdFunctor (C : Category) :
  IdFunctor C = FApp (FunctorCurrying (ProjFunc2 Cat1 C)) I.
Proof.
  apply: ToFunctorEq.
  move => X Y f.
  unfold Hom_eq'.
  rewrite /=.
  exists (eq_refl X).
  exists (eq_refl Y).
  rewrite /=.
  rewrite Hom_IdL.
  rewrite Hom_IdR.
  reflexivity.
Qed.  
  
Lemma Curry_to_ConstFunctor (C D : Category) :
  ToConstFunctor D C = FunctorCurrying (ProjFunc1 C D).
Proof.
  apply: ToFunctorEq.
  move => X Y f.
  unfold Hom_eq'.
  have: (forall A, FApp (ToConstFunctor D C) A = FApp (FunctorCurrying (ProjFunc1 C D)) A).
  {
    move => A.
    rewrite /=.
    unfold Currying.Curry.
    rewrite /=.
    apply: ToFunctorEq.
    rewrite /=.
    move => _ _ _.
    exact: Hom_eq'_refl.
  }
  move => eqF.
  exists (eqF X).
  exists (eqF Y).
  apply: ToNatTranEq.
  apply: functional_extensionality_dep.
  move => Z.
  rewrite /=.
  repeat rewrite NApp_HomId'_eq.
  rewrite /=.
  rewrite Hom_IdL.
  rewrite Hom_IdR.
  reflexivity.
Qed.
