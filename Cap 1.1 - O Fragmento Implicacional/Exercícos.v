Section Capitulo2.
Variables p q r: Prop.

Lemma Exe1 : (p -> p -> q) -> p -> q.
Proof.
    intros.
    apply H.
    assumption.
    assumption.
Qed.

Lemma Exe2 : (p -> q) -> (p -> p -> q).
Proof.
    intro.
    intro.
    assumption.
Qed.

Variable t: Prop.
Lemma Exe3 : (q -> r -> t) -> (p -> q) -> p -> r -> t.
Proof.
    intro.
    intro.
    intro.
    apply H.
    apply H0.
    assumption.
Qed.

Lemma Exe4: (p -> q -> r) -> (p -> q) -> p -> r.
Proof.
    intros.
    apply H.
    assumption.
    apply H0.
    assumption.
Qed.

Lemma Exe5: (p -> q -> r) -> (q -> p -> r).
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.
End Capitulo2.