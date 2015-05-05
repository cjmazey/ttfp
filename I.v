Theorem I1 : forall A B C : Prop,
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros A B C.
  intros a_imp_b b_imp_c.
  intros a.
  refine (b_imp_c _).
    refine (a_imp_b _).
      exact a.
Qed.

Theorem I2 : forall A B C : Prop,
    ((A \/ B) -> C) -> ((A -> C) /\ (B -> C)).
Proof.
  intros A B C.
  intros a_or_b_imp_c.
  refine (conj _ _).
    intros a.
    refine (a_or_b_imp_c _).
      exact (or_introl a).

    intros b.
    refine (a_or_b_imp_c _).
      exact (or_intror b).
Qed.

Theorem I3 : forall A B C : Prop,
    (A -> (B -> C)) -> ((A /\ B) -> C).
Proof.
  intros A B C.
  intros a_imp_b_imp_c.
  intros a_and_b.
  destruct a_and_b as [a b].
  refine (a_imp_b_imp_c _ _).
    exact a.

    exact b.
Qed.

Theorem I4a : forall A B : Prop,
    (A -> B) -> (~ B -> ~ A).
Proof.
  intros A B.
  intros a_imp_b not_b.
  intros a.
  refine (not_b _).
    refine (a_imp_b _).
      exact a.
Qed.

Theorem I4b : forall A : Prop,
    A -> ~ ~ A.
Proof.
  intros A.
  intros a.
  intros not_a.
  exact (not_a a).
Qed.
