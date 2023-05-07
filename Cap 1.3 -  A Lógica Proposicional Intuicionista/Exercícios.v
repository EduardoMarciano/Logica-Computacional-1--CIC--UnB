Section Cap3.
Variables p u: Prop.
Hypothesis H : (~~p) -> (~~u).

Lemma Exe1 :  ~~(p->u).
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
End Cap3.

Section Cap3.
Variables p u: Prop.
Lemma Exe2 :  ~~(~~p->p).
Proof.
  intro.
  apply H.
  intro.
  exfalso.
  apply H0.
  intro.
  apply H.
  intro.
  assumption.
Qed.

Lemma Exe3 :  ~~(((p -> u) -> p) -> p).
Proof.
  intro.
  apply H.
  intro.
  apply H0.
  intro.
  exfalso.
  apply H.
  intro.
  assumption.
Qed.
End Cap3.