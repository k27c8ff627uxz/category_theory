From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import DiscreteCat Univ.FunctorComp Univ.FunctorCategory Comma.CommaCat.

Set Universe Polymorphism.

Definition SliceCat {C : Category} (X : Obj C) : Category :=
  CommaCat
    (IdFunctor C)
    (ConstFunctor Cat1 X)
.

Definition CosliceCat {C : Category} (X : Obj C) : Category :=
  CommaCat
    (ConstFunctor Cat1 X)
    (IdFunctor C)
.
