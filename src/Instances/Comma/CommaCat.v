From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Set Universe Polymorphism.

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
      unfold Comma.comp.
      unfold Comma.hom_fst.
      rewrite /=.
      exact: Hom_assoc.
    } {
      unfold Comma.comp.
      unfold Comma.hom_fst.
      rewrite /=.
      exact: Hom_assoc.
    }
  Qed.
  Next Obligation.
  Proof.
    unfold Comma.id.
    unfold Comma.comp.
    apply: Comma.Tohom_eq.
    {
      unfold Comma.hom_fst.
      rewrite /=.
      exact: Hom_IdL.
    } {
      unfold Comma.hom_snd.
      rewrite /=.
      exact: Hom_IdL.
    }
  Qed.
  Next Obligation.
    unfold Comma.id.
    unfold Comma.comp.
    apply: Comma.Tohom_eq.
    {
      unfold Comma.hom_fst.
      rewrite /=.
      exact: Hom_IdR.
    } {
      unfold Comma.hom_snd.
      rewrite /=.
      exact: Hom_IdR.
    }
  Qed.

  Definition CommaDom (f : Obj CommaCat) : Obj C := Comma.dom F G f.
  Definition CommaCodom (f : Obj CommaCat) : Obj D := Comma.codom F G f.
  Definition OfCommaObj (f : Obj CommaCat) : Hom (FApp F (CommaDom f)) (FApp G (CommaCodom f)) := Comma.arrow F G f.
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

Definition ToCommaObj
           {C D E}
           (F : Functor C E) (G : Functor D E)
           (X : Obj C) (Y : Obj D) (f : Hom (FApp F X) (FApp G Y))
  : Obj (CommaCat F G) :=
  existT _ (pair X Y) f.

Lemma Eq_ToCommaObj
      {C D E}
      (F : Functor C E) (G : Functor D E) :
  forall (h : Obj (CommaCat F G)),
    h = (ToCommaObj F G (CommaDom h) (CommaCodom h) (OfCommaObj h)).
Proof.
  rewrite /=.
  unfold ToCommaObj, CommaDom, CommaCodom, OfCommaObj.
  unfold Comma.dom, Comma.codom, Comma.arrow.
  case.
  case.
  simpl.
  move => X Y p.
  reflexivity.
Qed.

Definition ToCommaHomCond
           {C D E}
           {F : Functor C E} {G : Functor D E}
           {X1 X2 : Obj C} {Y1 Y2 : Obj D}
           (h1 : Hom (FApp F X1) (FApp G Y1)) (h2 : Hom (FApp F X2) (FApp G Y2))
           (f : Hom X1 X2) (g : Hom Y1 Y2) :=
  (FAppH G g) \o h1 = h2 \o (FAppH F f).

Definition ToCommaHom
           {C D E}
           {F : Functor C E} {G : Functor D E}
           {X1 X2 : Obj C} {Y1 Y2 : Obj D}
           (h1 : Hom (FApp F X1) (FApp G Y1)) (h2 : Hom (FApp F X2) (FApp G Y2))
           (f : Hom X1 X2) (g : Hom Y1 Y2)
           (cond : ToCommaHomCond h1 h2 f g)
  : Hom (ToCommaObj F G X1 Y1 h1) (ToCommaObj F G X2 Y2 h2) :=
  exist _ (pair f g) cond.

Definition ToCommaHom'Cond
           {C D E}
           {F : Functor C E} {G : Functor D E}
           (h1 h2 : Obj (CommaCat F G))
           (f : Hom (CommaDom h1) (CommaDom h2))
           (g : Hom (CommaCodom h1) (CommaCodom h2)) :=
  (FAppH G g) \o (OfCommaObj h1) = (OfCommaObj h2) \o (FAppH F f).

Definition ToCommaHom'
           {C D E}
           {F : Functor C E} {G : Functor D E}
           (h1 h2 : Obj (CommaCat F G))
           (f : Hom (CommaDom h1) (CommaDom h2))
           (g : Hom (CommaCodom h1) (CommaCodom h2))
           (cond : ToCommaHom'Cond h1 h2 f g)
  : Hom h1 h2 :=
  exist _ (pair f g) cond.

Lemma CommaHom_Cond
      {C D E}
      {F : Functor C E} {G : Functor D E}
      {X1 X2 : Obj C} {Y1 Y2 : Obj D}
      {f1 : Hom (FApp F X1) (FApp G Y1)}
      {f2 : Hom (FApp F X2) (FApp G Y2)} :
  forall (ff : Hom (ToCommaObj F G X1 Y1 f1) (ToCommaObj F G X2 Y2 f2)),
    (FAppH G (CommaHom_snd ff)) \o f1 = f2 \o (FAppH F (CommaHom_fst ff)).
Proof.
  case.
  case.
  unfold Comma.dom.
  unfold Comma.codom.
  simpl.
  move => h1 h2 cond.
  unfold CommaHom_fst.
  unfold CommaHom_snd.
  unfold Comma.hom_fst.
  unfold Comma.hom_snd.
  simpl.
  assumption.
Qed.
