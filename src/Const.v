Require Export Monad.

Reserved Notation "x <+> y" (at level 65, right associativity).

Class Monoid (M : Type) :=
{ mempty : M
; mappend : M -> M -> M

; m_left_identity  : forall (x : M), mappend mempty x = x
; m_right_identity : forall (x : M), mappend x mempty = x
; m_associativity  : forall (x y z : M),
    mappend (mappend x y) z = mappend x (mappend y z)
}.

Notation "x <+> y" := (mappend x y) (at level 65, right associativity).

Module Const.

  Variable C : Type.
  Context `{Monoid C}.

  Inductive Const (A : Type) : Type := Const_ : C -> Const A.


  Definition Const_map {X Y} (f : X -> Y) (x : Const X) : Const Y :=
    match x with Const_ c => Const_ Y c end.
  Hint Unfold Const_map.

  Global Program Instance Const_Functor : Functor Const :=
  { fmap := @Const_map }.
  Obligation 1. ext_eq. compute. destruct x. reflexivity. Defined.
  Obligation 2. ext_eq. compute. destruct x. reflexivity. Defined.


  Definition Const_apply {X Y} (f : Const (X -> Y)) (x : Const X) : Const Y :=
    match f with
      Const_ a => match x with
        Const_ b => Const_ Y (a <+> b)
      end
    end.
  Hint Unfold Const_apply.

  Global Program Instance Const_Applicative : Applicative Const :=
  { is_functor := Const_Functor
  ; eta   := fun T _ => Const_ T mempty
  ; apply := @Const_apply
  }.
  Obligation 1.
    ext_eq. unfold Const_apply.
    destruct x. unfold id. f_equal.
    apply m_left_identity.
  Defined.
  Obligation 2.
    unfold Const_apply.
    destruct u. destruct v. destruct w. f_equal.
    rewrite m_left_identity.
    apply m_associativity.
  Defined.
  Obligation 3.
    f_equal.
    apply m_left_identity.
  Defined.
  Obligation 4.
    unfold Const_apply. destruct u.
    rewrite m_right_identity.
    rewrite m_left_identity.
    reflexivity.
  Defined.
  Obligation 5.
    ext_eq. unfold Const_apply.
    destruct x.
    rewrite m_left_identity.
    unfold Const_map.
    reflexivity.
  Defined.


  Definition Const_join {X} (x : Const (Const X)) : Const X :=
    match x with Const_ c => Const_ X c end.
  Hint Unfold Const_join.

  Global Program Instance Const_Monad : Monad Const :=
  { is_applicative := Const_Applicative
  ; mu := @Const_join
  }.
  Obligation 2.
    ext_eq. unfold Const_join, Const_map, compose.
    destruct x. unfold id. reflexivity.
  Defined.
  Obligation 3.
    ext_eq. unfold Const_join, compose.
    destruct x. unfold id.
  Admitted.
  Obligation 4.
    ext_eq. unfold Const_join, Const_map, compose.
    destruct x. reflexivity.
  Defined.

End Const.