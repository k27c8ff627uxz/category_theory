
From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Relations.Relation_Definitions.
From Category.Base Require Import Logic Category Functor NatTran.
From Category.Instances Require Import Univ.NatTranComp.

Set Universe Polymorphism.

Program Definition FunctorCategory (C D : Category) : Category :=
  {|
    Obj := Functor C D;
    Hom := fun (F1 F2 : Functor C D) => NatTran F1 F2;
    Hom_Id := fun (F1 : Functor C D) => NatTran_Id F1;
    Hom_comp := fun (F1 F2 F3 : Functor C D) => fun (N1 : NatTran F2 F3) (N2 : NatTran F1 F2) => NatTran_Vertical_Comp N1 N2                                                
  |}.
Next Obligation.
Proof.
  exact: NatTran_Vertical_Comp_assoc.
Qed.
Next Obligation.
  exact: NatTran_Vertical_Comp_IdL.
Qed.
Next Obligation.
  exact: NatTran_Vertical_Comp_IdR.
Qed.


Section NaturalEquivalence.
  
  Context {C D : Category}.
  Context {F1 F2 : Functor C D}.
  
  Definition NaturalEquivalence (N1 : NatTran F1 F2) := @isomorphism (FunctorCategory C D) _ _ N1.

  Lemma ToNaturalEquivalence : forall N1,
      (forall X, isomorphism (NApp N1 X)) -> NaturalEquivalence N1.
  Proof.
    move => N1 cond.
    have: (forall (X : Obj C), exists! (h : Hom (FApp F2 X) (FApp F1 X)), isomorphism_pair (NApp N1 X) h).
    {
      move => X.
      move: (cond X).
      case.
      move => h pair_Nx.
      exists h.
      split.
      {
        destruct pair_Nx.
        by split.
      } {
        move => h' pair_Nh'.
        apply: (isomorphism_pair_unqR (NApp N1 X)).
        by split.
      }
    }
    move => Cond.
    apply (dependent_unique_choice (Obj C) (fun X => Hom (FApp F2 X) (FApp F1 X))) in Cond.
    move: Cond.
    case.
    move => NApp2 ispair.
    have: (forall (X Y : Obj C) (f : Hom X Y), FAppH F1 f \o (NApp2 X) = (NApp2 Y) \o FAppH F2 f).
    {
      move => X Y f.
      move: (NatTran_rectangle _ _ N1 _ _ f).
      move => HH.
      apply (f_equal (fun N => N \o (NApp2 X))) in HH.
      rewrite (Hom_assoc (FAppH F2 f) (NApp N1 X) (NApp2 X)) in HH.
      rewrite (proj2 (ispair X)) in HH.
      rewrite (Hom_IdR) in HH.
      move: HH =>->.
      rewrite <- (Hom_assoc (NApp2 Y) _ (NApp2 X)).
      rewrite <- (Hom_assoc (NApp2 Y) (NApp N1 Y)).
      rewrite (proj1 (ispair Y)).
      rewrite Hom_IdL.
      reflexivity.
    }
    move => NApp2_cond.
    set (Build_NatTran _ _ _ _ NApp2 NApp2_cond) as N2.
    exists N2.
    split; rewrite /=; apply ToNatTranEq; unfold NatTran_Vertical_Comp; rewrite /=; apply: functional_extensionality_dep; move => X; move: (ispair X); case; by [].
  Qed.

  Lemma OfNaturalEquivalence : forall N1,
      NaturalEquivalence N1 -> (forall X, isomorphism (NApp N1 X)).
  Proof.
    unfold NaturalEquivalence.
    move => N1.
    move => [N2 [eqN21 eqN12]].
    move => X.
    exists (NApp N2 X).
    split.
    {
      move: eqN21.
      rewrite /=.
      by apply/ (f_equal (fun N => NApp N X)).
    } {
      move: eqN12.
      rewrite /=.
      by apply/ (f_equal (fun N => NApp N X)).
    }
  Qed.

End NaturalEquivalence.

Lemma NApp_HomId'_eq {C D : Category} {F1 F2: Functor C D} (eqF : F1 = F2) X (eqFX : FApp F1 X = FApp F2 X) :
  NApp (@HomId' (FunctorCategory C D) _ _ eqF) X = HomId' eqFX.
Proof.
  subst.
  repeat rewrite HomId'_id.
  rewrite /=.
  reflexivity.
Qed.
  

Program Definition ConstFunctor (C D : Category) : Functor C (FunctorCategory D C) :=
  {|
    FApp := fun (X : Obj C) =>
             {|
               FApp := fun (Y : Obj D) => X;
               FAppH := fun Y1 Y2 => fun f => \Id X
             |};
    FAppH := fun X1 X2 => fun f =>
                            {|
                              NApp := fun Y => f
                            |}
  |}.
Next Obligation.
Proof.
  by rewrite Hom_IdL.
Qed.
Next Obligation.
  rewrite Hom_IdL.
  rewrite Hom_IdR.
  reflexivity.
Qed.
Next Obligation.
  apply: ToNatTranEq.
  rewrite /=.
  reflexivity.
Qed.
Next Obligation.
  apply: ToNatTranEq.
  rewrite /=.
  reflexivity.
Qed.  
    
