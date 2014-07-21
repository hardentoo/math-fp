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
  intros.
Abort.

Theorem existential_inv : forall {X}, exists y, forall (x : X), x <> y.
Proof.
  intros.
Abort.
