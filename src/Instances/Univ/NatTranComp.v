From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Univ.FunctorComp.

Program Definition NatTran_Id {C D : Category} (F : Functor C D) : NatTran F F :=
  {|
    NApp := fun (X : Obj C) => \Id (FApp F X)
  |}.
Next Obligation.
  rewrite Hom_IdL.
  rewrite Hom_IdR.
  reflexivity.
Qed.

Program Definition NatTran_Vertical_Comp {C D : Category} {F1 F2 F3 : Functor C D} (N1 : NatTran F2 F3) (N2 : NatTran F1 F2) : NatTran F1 F3 :=
  {|
    NApp := fun (X : Obj C) => NApp N1 X \o NApp N2 X
  |}.
Next Obligation.
  rewrite <- Hom_assoc.
  rewrite (NatTran_rectangle F2 F3).
  rewrite (Hom_assoc (NApp N1 Y) _ (NApp N2 X)).
  rewrite (NatTran_rectangle F1 F2).
  rewrite <- Hom_assoc.
  reflexivity.
Qed.

Lemma NatTran_Vertical_Comp_compat {C D : Category} {F1 F2 F3 : Functor C D} (N1 : NatTran F2 F3) (N2 : NatTran F1 F2) :
  forall X, NApp (NatTran_Vertical_Comp N1 N2) X = NApp N1 X \o NApp N2 X.
Proof.
  move => X.
  by rewrite /=.
Qed.

Lemma NatTran_Vertical_Comp_assoc {C D : Category} {F1 F2 F3 F4 : Functor C D} :
  forall (N1 : NatTran F3 F4) (N2 : NatTran F2 F3) (N3 : NatTran F1 F2),
    NatTran_Vertical_Comp (NatTran_Vertical_Comp N1 N2) N3 = NatTran_Vertical_Comp N1 (NatTran_Vertical_Comp N2 N3).
Proof.
  move => N1 N2 N3.
  apply: ToNatTranEq.
  rewrite /=.
  apply: functional_extensionality_dep.
  move => X.
  exact: Hom_assoc.
Qed.
  
Lemma NatTran_Vertical_Comp_IdL {C D : Category} {F1 F2 : Functor C D} :
  forall (N : NatTran F1 F2), NatTran_Vertical_Comp (NatTran_Id F2) N = N.
Proof.
  move => N.
  apply: ToNatTranEq.
  rewrite /=.
  apply: functional_extensionality_dep.
  move => X.
  move: Hom_IdL =>->.
  reflexivity.
Qed.

Lemma NatTran_Vertical_Comp_IdR {C D : Category} {F1 F2 : Functor C D} :
  forall (N : NatTran F1 F2), NatTran_Vertical_Comp N (NatTran_Id F1) = N.
Proof.
  move => N.
  apply: ToNatTranEq.
  rewrite /=.
  apply: functional_extensionality_dep.
  move => X.
  move: Hom_IdR =>->.
  reflexivity.
Qed.




Program Definition NatTran_Horizontal_Comp {C D E : Category} {F1 G1 : Functor D E} {F2 G2 : Functor C D} (N1 : NatTran F1 G1) (N2 : NatTran F2 G2) : NatTran (Functor_Comp F1 F2) (Functor_Comp G1 G2) :=
  {|
    NApp := fun (X : Obj C) => (NApp N1 (FApp G2 X)) \o (FAppH F1 (NApp N2 X))
  |}.
Next Obligation.
Proof.
  rewrite <- (NatTran_rectangle F1 _ N1).
  rewrite <- (Hom_assoc (FAppH G1 _) (FAppH G1 _)).
  rewrite <- (FAppH_comp_eq G1).
  rewrite Hom_assoc.
  rewrite <- (FAppH_comp_eq F1).
  rewrite (NatTran_rectangle _ G1 N1).
  rewrite (NatTran_rectangle _ G2 N2).
  reflexivity.
Qed.
