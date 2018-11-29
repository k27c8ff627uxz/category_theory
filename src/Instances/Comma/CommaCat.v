From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Module Comma.

  Section CommaSection.
    Context {C D E : Category}.
    Variable F : Functor C E.
    Variable G : Functor D E.
 
    Definition obj := {ff : (Obj C) * (Obj D) & Hom (FApp F (fst ff)) (FApp G (snd ff))}.
    Definition dom (ff : obj) : Obj C := fst (projT1 ff).
    Definition codom (ff : obj) : Obj D := snd (projT1 ff).
    Definition arrow (ff : obj) : Hom (FApp F (dom ff)) (FApp G (codom ff)) := projT2 ff.
    
    Definition hom : obj -> obj -> Type :=
      fun ff1 ff2  =>
        let X1 : Obj C := dom ff1 in
        let X2 : Obj C := dom ff2 in
        let Y1 : Obj D := codom ff1 in
        let Y2 : Obj D := codom ff2 in
        let f1 : Hom (FApp F X1) (FApp G Y1) := arrow ff1 in
        let f2 : Hom (FApp F X2) (FApp G Y2) := arrow ff2 in
        {gg : (Hom X1 X2) * (Hom Y1 Y2) | (FAppH G (snd gg)) \o f1 = f2 \o (FAppH F (fst gg))}.
    
    Definition hom_fst {ff1 ff2 : obj} (hh : hom ff1 ff2) : Hom (dom ff1) (dom ff2) :=
      fst (proj1_sig hh).
    
    Definition hom_snd {ff1 ff2 : obj} (hh : hom ff1 ff2) : Hom (codom ff1) (codom ff2) :=
      snd (proj1_sig hh).
    
    Lemma Tohom_eq :
      forall {ff1 ff2 : obj},
      forall (hh gg : hom ff1 ff2),
        hom_fst hh = hom_fst gg -> hom_snd hh = hom_snd gg -> hh = gg.
    Proof.
      move => ff1 ff2.
      move => [[hh1 hh2] condh].
      move => [[gg1 gg2] condg].
      rewrite /hom_fst /hom_snd /=.
      move => eqh eqg.
      subst.
      rewrite(_:condh = condg).
      reflexivity.
      exact: p_proof_irrelevance.
    Qed.
    
    Program Definition id (ff : obj) : hom ff ff :=
      pair (\Id (dom ff)) (\Id (codom ff)).
    Next Obligation.
    Proof.
      repeat rewrite Functor_id_eq.
      move: Hom_IdL =>->.
      move: Hom_IdR =>->.
      reflexivity.
    Qed.

    Program Definition comp (ff1 ff2 ff3 : obj) : (hom ff2 ff3) -> (hom ff1 ff2) -> (hom ff1 ff3) :=
      fun hh gg =>
        pair (hom_fst hh \o hom_fst gg) (hom_snd hh \o hom_snd gg).
    Next Obligation.
    Proof.
      repeat rewrite FAppH_comp_eq.
      rewrite (Hom_assoc _ _ (arrow ff1)).
      move: (proj2_sig gg) =>->.
      rewrite <- (Hom_assoc (arrow ff3)).
      move: (proj2_sig hh) =><-.
      rewrite Hom_assoc.
      reflexivity.
    Qed.
    
    


  End CommaSection.
End Comma.



Section Definitions.

  Context {C D E : Category}.
  Context {F : Functor C E}.
  Context {G : Functor D E}.
  
  Program Definition CommaCat : Category :=
  {|
        Obj := Comma.obj F G;
        Hom := Comma.hom F G;
        Hom_Id := Comma.id F G;
        Hom_comp := Comma.comp F G
  |}.
  Next Obligation.
  Proof.
    apply: Comma.Tohom_eq.
    {
      rewrite /Comma.comp /Comma.hom_fst /=.
      exact: Hom_assoc.
    } {
      rewrite /Comma.comp /Comma.hom_snd /=.
      exact: Hom_assoc.
    }
  Qed.
  Next Obligation.
  Proof.
    rewrite /Comma.id /Comma.comp.
    apply: Comma.Tohom_eq.
    {
      rewrite /Comma.hom_fst /=.
      exact: Hom_IdL.
    } {
      rewrite /Comma.hom_snd /=.
      exact: Hom_IdL.
    }
  Qed.
  Next Obligation.
    rewrite /Comma.id /Comma.comp.
    apply: Comma.Tohom_eq.
    {
      rewrite /Comma.hom_fst /=.
      exact: Hom_IdR.
    } {
      rewrite /Comma.hom_snd /=.
      exact: Hom_IdR.
    }
  Qed.

  Definition CommaDom (f : Obj CommaCat) : Obj C := Comma.dom F G f.
  Definition CommaCodom (f : Obj CommaCat) : Obj D := Comma.codom F G f.
  Definition ToArrow (f : Obj CommaCat) : Hom (FApp F (CommaDom f)) (FApp G (CommaCodom f)) := Comma.arrow F G f.
  Definition CommaHom_fst {f1 f2 : Obj CommaCat} (hh : Hom f1 f2) : Hom (CommaDom f1) (CommaDom f2) := Comma.hom_fst F G hh.
  Definition CommaHom_snd {f1 f2 : Obj CommaCat} (hh : Hom f1 f2) : Hom (CommaCodom f1) (CommaCodom f2) := Comma.hom_snd F G hh.
  Lemma ToCommaHomEq :
    forall {ff1 ff2 : Obj CommaCat},
    forall (hh gg : Hom ff1 ff2),
      CommaHom_fst hh = CommaHom_fst gg -> CommaHom_snd hh = CommaHom_snd gg -> hh = gg.
  Proof.
    move => ff1 ff2 hh gg eqf eqs.
    apply: Comma.Tohom_eq.
    assumption.
    assumption.
  Qed.

End Definitions.

Global Arguments CommaCat {C D E} (F G).
