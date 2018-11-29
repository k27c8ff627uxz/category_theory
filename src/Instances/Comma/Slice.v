From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import DiscreteCat Univ.FunctorComp Univ.FunctorCategory Comma.CommaCat.

Definition SliceCat {C : Category} (X : Obj C) : Category :=
  CommaCat
    (IdFunctor C)
    (FApp (ConstFunctor C Cat1) X)
.

Definition CosliceCat {C : Category} (X : Obj C) : Category :=
  CommaCat
    (FApp (ConstFunctor C Cat1) X)
    (IdFunctor C)
.
