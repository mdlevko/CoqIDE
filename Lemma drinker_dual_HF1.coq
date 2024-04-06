Lemma drinker_dual : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ (forall x : U, ~ P x))
-> exists (x : U), (exists y : U, P y )-> P x.
Proof.
intros U P [K] H.
destruct H as [Hexists | Hforall].
destruct Hexists as [x Px].
exists x.
intros _.
exact Px.
exists K.
intros [y Py].
exfalso.
apply (Hforall y). 
exact Py.
Qed.
