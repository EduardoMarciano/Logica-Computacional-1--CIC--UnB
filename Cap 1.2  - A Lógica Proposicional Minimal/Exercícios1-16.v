Section exercicio_min1.
Variables p q: Prop.

Hypothesis H : ~(p \/ q).
Lemma min1 : (~p) /\ (~q).

 Proof.
  split.
  - intro. apply H. left. assumption.
  -intro. apply H. right. assumption.
Qed.

End exercicio_min1.

Section exercicio_min2.
Variables p q: Prop.

Hypothesis H : (~p) /\ (~q).
Lemma min2 : ~(p \/ q).

 Proof.
  Admitted.

End exercicio_min2.

Section exercicio_min12.
Variables p u y: Prop.

Hypothesis H: (p\/u)/\(p\/y).
Lemma min12:  p\/(u/\y).

Proof.
  destruct H.
  destruct H0.
    - left. assumption.
    - destruct H1.
      + left. assumption.
      + right. split.
          * assumption.
          * assumption.
Qed.
End exercicio_min12.
