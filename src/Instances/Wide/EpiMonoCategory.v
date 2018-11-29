From mathcomp Require Import ssreflect.

From Category.Base Require Import Logic Category Functor NatTran epi_mono.
From Category.Instances Require Import Wide.WideSubCategory.

Set Universe Polymorphism.

Program Definition EpiCategory (C : Category) : Category :=
  WideSubcategory (fun (X Y : Obj C) => fun (f : Hom X Y) => epi f) _.
Next Obligation.
Proof.
  split.
  move => X.
  exact: id_epi.
  move => X Y Z f g.
  exact: epi_comp.
Qed.

Program Definition MonoCategory (C : Category) : Category :=
  WideSubcategory (fun (X Y : Obj C) => fun (f : Hom X Y) => mono f) _.
Next Obligation.
Proof.
  split.
  move => X.
  exact: id_mono.
  move => X Y Z f g.
  exact: mono_comp.
Qed.
  