Section Negação.
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
End Negação.

Section Negação.
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
End Negação.

Section Negação.
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
End Negação.

Section Negação.
Variables p u: Prop.

Hypothesis Q: p.
Hypothesis Q1: ~p.
Lemma Exe4: (~u).

Proof.
  intro.
  apply Q1.
  assumption.

Qed.
End  Negação.

Section Conjunção.
Variables p u: Prop.

Hypothesis D: p /\ u.
Lemma Ex1: u /\ p.

Proof.
   split.
   apply D.
   apply D.

Qed.
End Conjunção.

Section Conjunção.
Variables p u: Prop.

Hypothesis D: (p /\ u) /\p.
Lemma Ex2: p /\ (u /\ p).

Proof.
  split.
  apply D.
  split.
  apply D.
  apply D.

Qed.
End Conjunção.

Section Dijunção.
Variables p q r: Prop.

Hypothesis H : (p \/ q) \/ r.
Lemma E1: p \/ (q \/ r ).
Proof.
  destruct H.
  -  destruct H0.
     -- left. assumption.
     -- right. left. assumption.
  -  right. right. assumption.
Qed.
End Dijunção.

Section exercicio_cp1.
Variables p q : Prop.
Hypothesis H : p -> ~q.
Lemma cp1 : q -> ~p.
Proof.
    intro.
    intro.
    apply H.
    assumption.
    assumption.
Qed.
End exercicio_cp1.



