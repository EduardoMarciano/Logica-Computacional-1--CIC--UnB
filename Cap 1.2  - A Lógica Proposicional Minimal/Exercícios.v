Section SubCapitulo2.
Variables p u: Prop.
Hypothesis H : p-> u.
Lemma Exe1: (~~p)->(~~u).
Proof.
  intro.
  intro.
  apply H0.
  intro.
  apply H1.
  apply H .
  assumption.

Qed.
End SubCapitulo2.

Section SubCapitulo2.
Variables p u: Prop.

Hypothesis Q1: ~~(p-> u).

Lemma Exe2: (~~p)->(~~u).
  Proof.
  intro.
  intro.
  apply Q1.
  intro.
  apply H.
  intro.
  apply H0.
  apply H1.
  assumption.
Qed.

End SubCapitulo2.

Section SubCapitulo2.
Variables p u: Prop.
Lemma Exe3: (((((p -> u) -> p) -> p) -> u) -> u).
Proof.
  intros.
  apply H.
  intro.
  apply H0.
  intro.
  apply H.
  intro.
  assumption.
Qed.
End SubCapitulo2.

Section SubCapitulo2.
Variables p u: Prop.

Hypothesis Q: p.
Hypothesis Q1: ~p.
Lemma Exe4: (~u).
Proof.
  intro.
  apply Q1.
  assumption.
Qed.