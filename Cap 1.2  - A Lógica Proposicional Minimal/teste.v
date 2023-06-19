Lemma PIG: forall (P : nat -> Prop) (k : nat), P k -> 
(forall n, n >= k -> P n -> P (S n)) ->
forall n : nat, n >= k -> P n.
Proof.
  intros P k IH n H2.
  assert (H := nat_ind (fun n => n >= k -> P n)).
  generalize dependent n. apply H.
  - intro Hk. inversion Hk. subst.
  apply H1.
  - intros n H2 H3 in H1. assumption.
  + rewrite H0 in H1. assumption.
  + subst. apply IH.
    * assumtion.
    * apply H2. assumption.
Qed.