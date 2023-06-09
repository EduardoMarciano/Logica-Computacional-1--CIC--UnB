Lemma PIG: forall (P : nat -> Prop) (k : nat), P k -> 
(forall n, n >= k -> P n -> P (S n)) ->
forall n : nat, n >= k -> P n.
Proof.
  intros P k H1 IH n H2.
  assert (H := nat_ind (fun n => n >= k -> P n)).
  generalize dependent n. apply H.
  - intro Hk. inversion Hk. subst.
  apply H1.
  - intros n H2 H3. inversion H3.
    + rewrite H0 in H1. assumption.
    + subst. apply IH.
      * assumption.
      * apply H2. assumption.
Qed.