From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Product.ProductCategory Comma.CommaCat.

Section CommaFunc.

  Context {C D E : Category}.
  Variable (F : Functor C E).
  Variable (G : Functor D E).

  Program Definition CommaFunctor : Functor (ProductCat C D) (CommaCat F G) :=
    {|
      FApp := fun X => pair (FApp F (fst X)) (FApp G (snd X))
    |}.
  

sfda
  