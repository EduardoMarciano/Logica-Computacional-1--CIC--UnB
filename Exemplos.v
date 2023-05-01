Section Exemplos.
Variables p q r: Prop.
Hypothesis H : p.
Lemma Exe1 :  ~~p.
Proof.
    intro.
    contradiction.
Qed.
End Exemplos.

Section Exemplo_or_comm.
Variables p u: Prop.
Hypothesis H : p \/ u.
Lemma Exe2: u \/ p.
Proof.
  destruct H.
  -  right.
  assumption.
  - left. assumption.
Qed.



