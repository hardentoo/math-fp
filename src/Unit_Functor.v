Require Export Category.

Section Unit_Functor.

  Variable objC : Set.
  Variable homC : objC -> objC -> Set.
  Context `{C : Category objC homC}.

  Variable objD : Prop.
  Variable homD : objD -> objD -> Prop.
  Context `{D : Category objD homD}.

  Definition Unit (A : objD) : C -> D := fun _ => A.
  Definition Unit_fmap (A : objD) (X Y : objC) (f : X -{ C }-> Y)
    : (A -{ D }-> A) := id.

  Definition Unit_Functor (A : objD) : Functor C D (Unit A).
    apply Build_Functor with (fmap := Unit_fmap A).
    (* fmap_respects *)   reflexivity.
    (* fun_identity *)    reflexivity.
    (* fun_composition *) intros. apply left_identity.
  Defined.

End Unit_Functor.