Lemma ex_dist_1 : forall (U : Type) (A B : U -> Prop),
(exists x, A x \/ B x) -> (exists x, A x) \/ (exists x, B x).
Proof.
intros U A B H.
destruct H as [x [HA | HB]].
left.
exists x. 
assumption.
right.
exists x.
assumption.
Qed.
