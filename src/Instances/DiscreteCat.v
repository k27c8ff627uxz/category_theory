From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Program Definition DiscreteCat (A : Type) : Category :=
  {|
    Obj := A;
    Hom := fun x y => x = y;
  |}.

Lemma DiscreteCat_Hom_eq :
  forall {A : Type},
  forall {X Y : Obj (DiscreteCat A)},
  forall (f g : Hom X Y), f = g.
Proof.
  move => A X Y.
  unfold Hom.
  simpl.
  move => f g.
  exact: p_proof_irrelevance.
Qed.

Definition Cat0 := DiscreteCat False.

Definition Cat1 := DiscreteCat True.
Definition Cat1Obj : Obj Cat1 := I.

Lemma Cat1Obj_eq :
  forall (X Y : Obj Cat1), X = Y.
Proof.
  case.
  case.
  reflexivity.
Qed.

Lemma Cat1Hom_eq :
  forall {X Y : Obj Cat1} (f g : Hom X Y), f = g.
Proof.
  move => X Y f g.
  exact: DiscreteCat_Hom_eq.
Qed.
