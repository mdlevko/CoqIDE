Lemma dec_1 : forall (U : Type) (P : U -> Prop),
  inhabited U -> ((forall x : U, P x) \/ (forall x : U, ~ P x))
  -> (forall x : U, P x) \/ (exists x : U, ~ P x).
Proof.
intros U P Hinhab H.
destruct H as [HforallP | HforallNotP].
left.
apply HforallP.
right.
destruct Hinhab as [K].
exists K.
apply HforallNotP.
Qed.
