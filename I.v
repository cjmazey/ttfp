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

Theorem I5 : forall A B : Prop,
    (A \/ B) -> ((A -> False) /\ (B -> False) -> False).
Proof.
  intros A B.
  intros a_or_b.
  intros not_a_and_not_b.
  destruct not_a_and_not_b as [not_a not_b].
  destruct a_or_b as [a | b].
    exact (not_a a).

    exact (not_b b).
Qed.

Theorem I6a : forall A B : Prop,
    (A -> B) /\ (A -> ~ B) -> ~ A.
Proof.
  intros A B.
  intros a_imp_b_and_a_imp_not_b.
  destruct a_imp_b_and_a_imp_not_b as [a_imp_b a_imp_not_b].
  intros a.
  refine (a_imp_not_b a _).
    exact (a_imp_b a).
Qed.

Theorem I6b : forall A B : Prop,
    A /\ ~ A -> B.
Proof.
  intros A B.
  intros a_and_not_a.
  destruct a_and_not_a as [a not_a].
  pose (proof_of_False := not_a a).
  case proof_of_False.
Qed.

Theorem I7a : forall A : Prop,
    (A \/ ~ A) -> (~ ~ A -> A).
Proof.
  intros A.
  unfold not.
  intros a_or_not_a.
  intros not_not_a.
  destruct a_or_not_a as [a | not_a].
    exact a.

    pose (proof_of_False := not_not_a not_a).
    case proof_of_False.
Qed.

Theorem I7b : forall A B : Prop,
    (not (not A) -> A) -> ((~ A -> B) /\ (~ A -> ~ B) -> A).
Proof.
  intros A B.
  intros not_not_a_imp_a.
  intros not_a_imp_b_and_not_a_imp_not_b.
  destruct not_a_imp_b_and_not_a_imp_not_b as [not_a_imp_b not_a_imp_not_b].
  refine (not_not_a_imp_a _).
    intros not_a.
    pose (b := not_a_imp_b not_a).
    pose (not_b := not_a_imp_not_b not_a).
    pose (proof_of_False := not_b b).
    case proof_of_False.
Qed.

Theorem I7c : forall A B : Prop,
    ((~ A -> B) /\ (~ A -> ~ B) -> A) -> (A \/ not A).
Proof.
  intros A B.
  intros cc.
  refine (or_intror _).
    intros a.
    assert (not_a_imp_b : ~ A -> B).
      intros not_a.
      pose (proof_of_False := not_a a).
      case proof_of_False.
    assert (not_a_imp_not_b : ~ A -> ~ B).
      intros not_a.
      pose (proof_of_False := not_a a).
      case proof_of_False.
