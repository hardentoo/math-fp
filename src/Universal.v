Theorem universal : forall {X} (x : X), exists y, x = y.
Proof.
  intros. exists x. reflexivity.
Qed.

Theorem existential : forall {X} (x : X), exists y, x <> y.
Proof.
  intros. exists x. unfold not. intros.
Abort.

Theorem universal_inv : forall {X}, exists y, forall (x : X), x = y.
Proof.
  intros. eapply ex_intro. intros.
Abort.

Theorem existential_inv : forall {X}, exists y, forall (x : X), x <> y.
Proof.
  intros. eapply ex_intro. intros.
Abort.


Require Recdef.

Section Aleksey.

  Fixpoint map {a b : Set} (f : a -> b) (xs : list a) : list b :=
    match xs with
      | nil => nil
      | cons x x0 => cons (f x) (map f x0)
    end.

  Theorem map_preserves_length : forall {a b : Set} (f : a -> b) (xs : list a),
    length xs = length (map f xs).
  Proof.
    intros. induction xs as [| y ys].
      reflexivity.
      simpl. rewrite IHys. reflexivity.
  Defined.

  Function h (f : nat -> nat) (xs : list nat) {measure length xs} :=
    match map f xs with
      | nil => 0
      | cons y ys => y + h f ys
    end.
  Proof.
    intros.
    rewrite (map_preserves_length f xs).
    rewrite teq.
    auto.
  Qed.

End Aleksey.