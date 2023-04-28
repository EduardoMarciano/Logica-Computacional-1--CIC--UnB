Section Exemplos.
Variables p q r: Prop.
Hypothesis H : p.
Lemma Exe1 :  ~~p.
Proof.
    intro.
    apply H0.
    assumption.
Qed.


End Exemplos.

Section Exemplos.
Variables p u: Prop.
Hypothesis H : (~~p) -> (~~u).

Lemma Exe2 :  ~~(p->u).
Proof.
  intro.
  apply H0.
  intro.
  exfalso.
  apply H.
  intro.
  contradiction.
  intro.
  apply H0.
  intro.
  assumption.

Qed.
End Exemplos.