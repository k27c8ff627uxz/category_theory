From mathcomp Require Import ssreflect.
From Category.Base Require Import Logic Category Functor NatTran.

Section mono_epi.

  Context {C : Category}.
  
  Definition mono {X Y : Obj C} (f : Hom X Y) :=
    forall (A : Obj C) (g1 g2 : Hom A X), f \o g1 = f \o g2 -> g1 = g2.

  Definition epi {X Y : Obj C} (f : Hom X Y) :=
    forall (A : Obj C) (g1 g2 : Hom A X), f \o g1 = f \o g2 -> g1 = g2.

  Lemma iso_mono {X Y : Obj C}:
    forall (f : Hom X Y), isomorphism f -> mono f.
  Proof.
    move => f.
    case.
    move => g.
    case.
    move => eqgf eqfg.
    move => A g1 g2.
    move/ (f_equal (fun x => g \o x)).
    repeat rewrite <- Hom_assoc.
    move: eqgf =>->.
    repeat rewrite Hom_IdL.
    by [].
  Qed.

  Lemma id_mono {X : Obj C} :
    mono (\Id X).
  Proof.
    apply: iso_mono.
    exact: isomorphism_id.
  Qed.
    
  Lemma mono_comp {X Y Z : Obj C} :
    forall (f : Hom Y Z) (g : Hom X Y), mono f -> mono g -> mono (f \o g).
  Proof.
    move => f g.
    move => mono_f mono_g.
    move => A h1 h2.
    repeat rewrite Hom_assoc.
    move/ mono_f.
    exact: mono_g.
  Qed.

  Lemma iso_epi {X Y : Obj C}:
    forall (f : Hom X Y), isomorphism f -> epi f.
  Proof.
    move => f.
    case.
    move => g.
    case.
    move => eqgf eqfg.
    move => A g1 g2.
    move/ (f_equal (fun x => g \o x)).
    repeat rewrite <- Hom_assoc.
    move: eqgf =>->.
    repeat rewrite Hom_IdL.
    by [].
  Qed.

  Lemma id_epi {X : Obj C} :
    epi (\Id X).
  Proof.
    apply: iso_epi.
    exact: isomorphism_id.
  Qed.    
        
  Lemma epi_comp {X Y Z : Obj C} :
    forall (f : Hom Y Z) (g : Hom X Y), epi f -> epi g -> epi (f \o g).
  Proof.
    move => f g.
    move => mono_f mono_g.
    move => A h1 h2.
    repeat rewrite Hom_assoc.
    move/ mono_f.
    exact: mono_g.
  Qed.

End mono_epi.
