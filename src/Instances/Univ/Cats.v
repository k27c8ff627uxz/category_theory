
From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Univ.FunctorComp.

Set Universe Polymorphism.

Program Definition Cats : Category :=
  {|
    Obj := Category;
    Hom := fun (C D : Category) => Functor C D;
    Hom_Id := fun (C : Category) => IdFunctor C;
    Hom_comp := fun (C1 C2 C3 : Category) => fun (F1 : Functor C2 C3) (F2 : Functor C1 C2) => Functor_Comp F1 F2
  |}.
Next Obligation.
Proof.
  exact: Functor_Comp_assoc.
Qed.
Next Obligation.
  exact: Functor_Comp_IdL.
Qed.
Next Obligation.
  exact: Functor_Comp_IdR.
Qed.

