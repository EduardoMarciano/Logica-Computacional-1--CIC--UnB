Section Capitulo1.
Variables p q r: Prop.

Lemma Exe1 : (p -> p -> q) -> p -> q .
Proof.
    intros.
    apply H.
    assumption.
    assumption.
Admitted.

Lemma Exe2 : (p -> q) -> (p -> p -> q).
Proof.
    intros.
    apply H.
    assumption.
Admitted.

Variable t: Prop.
Lemma Exe3 : (q -> r -> t) -> (p -> q) -> p -> r -> t.
Proof.
    intros.
    apply H.
    apply H0.
    assumption.
    assumption.
Admitted.

Lemma Exe4: (p -> q -> r) -> (p -> q) -> p -> r.
Proof.
    intros.
    apply H.
    apply H1.
    apply H0.
    apply H1.
Admitted.

Lemma Exe5: (p -> q -> r) -> (q -> p -> r).
Proof.
  intros.
  apply H.
  apply H1.
  apply H0.
Admitted.
End Capitulo1.