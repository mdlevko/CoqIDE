Lemma deM_quant_4 : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ ~ (exists x : U, P x))
-> ~ (forall x : U, ~ P x)-> (exists x : U, P x).
Proof.
intros U P Hinhabited H Hforall.
destruct H as [Hexists | Hnotexists].
apply Hexists.
exfalso.
apply Hforall.
intros x H_Px.
apply Hnotexists.
exists x.
exact H_Px.
Qed.
