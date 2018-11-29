

Class Applyable (F : Type) (A : F -> Type) (B : forall (f : F), (A f) -> Type) :=
  {
    Apply : forall (f : F) (a : A f), (B f a)
  }.



           
Notation "% f a" := (Apply f a) (at level 10, f at next level).
