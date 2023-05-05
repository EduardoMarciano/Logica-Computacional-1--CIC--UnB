Section ola.
Variables p u y: Prop.

Hypothesis H: (p\/u)/\(p\/y).
Lemma Ex1:  p\/(u/\y).

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
  
