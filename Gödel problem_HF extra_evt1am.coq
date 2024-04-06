Lemma problem : forall (U : Type) (r : U -> U -> Prop), (exists x, forall y, r x y) -> (forall y, exists x, r x y).
Proof.
intros U r H.
intros y.
destruct H as [x Hx].
exists x.
apply Hx.
Qed.
