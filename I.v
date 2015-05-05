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

Definition EM (A : Prop) : Prop := A \/ ~ A.

Definition DN (A : Prop) : Prop := ~ ~ A -> A.

Definition CC (A B : Prop) : Prop := (~ A -> B) -> (~ A -> ~ B) -> A.

Theorem I7a : forall A : Prop,
    EM A -> DN A.
Proof.
  unfold EM, DN.
  intros A.
  intros a_or_not_a.
  intros not_not_a.
  destruct a_or_not_a as [a | not_a].
    exact a.

    pose (proof_of_False := not_not_a not_a).
    case proof_of_False.
Qed.

Theorem I7b : forall A B : Prop,
    DN A -> CC A B.
Proof.
  unfold DN, CC.
  intros A B.
  intros not_not_a_imp_a not_a_imp_b not_a_imp_not_b.
  refine (not_not_a_imp_a _).
    intros not_a.
    pose (b := not_a_imp_b not_a).
    pose (not_b := not_a_imp_not_b not_a).
    pose (proof_of_False := not_b b).
    case proof_of_False.
Qed.

Theorem I7c : forall (A : Prop),
    CC (A \/ ~ A) (~ A) -> EM A.
Proof.
  unfold CC, EM.
  intros A.
  intros cc.
  refine (cc _ _).
    refine (I4a A (A \/ ~ A) _).
      intros a. exact (or_introl a).

    refine (I4a (~ A) (A \/ ~ A) _).
      intros not_a. exact (or_intror not_a).
Qed.

Definition Pierce (A B : Prop) : Prop := ((A -> B) -> A) -> A.

Theorem I8 : forall (A B : Prop),
    EM A -> Pierce A B.
Proof.
  unfold EM, Pierce.
  intros A B.
  intros em.
  intros a_imp_b_imp_a.
  destruct em as [a | not_a].
    exact a.

    refine (a_imp_b_imp_a _).
      intros a.
      pose (proof_of_False := not_a a).
      case proof_of_False.
Qed.
