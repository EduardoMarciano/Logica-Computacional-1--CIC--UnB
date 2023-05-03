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
  apply H.
  
Qed.


End exercicio_min2.