From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

Program Definition IdFunctor (C : Category) : Functor C C :=
  {|
    FApp := fun X => X;
    FAppH := fun X Y => fun f => f
  |}.

Program Definition Functor_Comp {C1 C2 C3 : Category} (F : Functor C2 C3) (G : Functor C1 C2) : Functor C1 C3 :=
  {|
    FApp := fun (X : Obj C1) => FApp F (FApp G X : Obj _);
    FAppH := fun (X Y : Obj C1) => fun (f : Hom X Y) => FAppH F (FAppH G f)
  |}.
Next Obligation.
  rewrite FAppH_comp_eq.
  rewrite FAppH_comp_eq.
  reflexivity.
Qed.
Next Obligation.
  rewrite Functor_id_eq.
  rewrite Functor_id_eq.
  reflexivity.
Qed.

Lemma Functor_Comp_assoc : forall {C1 C2 C3 C4 : Category} (F1 : Functor C3 C4) (F2 : Functor C2 C3) (F3 : Functor C1 C2),
    Functor_Comp (Functor_Comp F1 F2) F3 = Functor_Comp F1 (Functor_Comp F2 F3).
Proof.
  move => C1 C2 C3 C4 F1 F2 F3.
  apply: ToFunctorEq => X Y f /=.
  exact: Hom_eq'_refl.
Qed.

Lemma Functor_Comp_IdL :
  forall {C D : Category} (F : Functor C D),
    Functor_Comp (IdFunctor D) F = F.
Proof.
  move => C D F.
  apply: ToFunctorEq => X Y f /=.
  exact: Hom_eq'_refl.
Qed.

Lemma Functor_Comp_IdR :
  forall {C D : Category} (F : Functor C D),
    Functor_Comp F (IdFunctor C) = F.
Proof.
  move => C D F.
  apply: ToFunctorEq => X Y f /=.
  exact: Hom_eq'_refl.
Qed.

