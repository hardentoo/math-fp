Theorem universal : forall {X} (x : X), exists y, x = y.
Proof.
  intros. exists x. reflexivity.
Qed.

Theorem existential : forall {X} (x : X), exists y, x <> y.
Proof.
  intros. exists x.
Abort.