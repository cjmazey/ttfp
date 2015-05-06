(** * Chapter I *)

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

Definition I9 : Prop :=
  forall (x y : nat), exists (z : nat), x <> y -> x < z /\ z < y.

Module I10.
  Definition I10a (f : nat -> nat) : Prop :=
    forall (x y : nat), f x = f y -> x = y.

  Definition I10b (f : nat -> nat) : Prop :=
    forall (y : nat), exists (x : nat), f x = y.

  Definition I10c (f : nat -> nat) : Prop :=
    forall (x y : nat), x < y -> f x < f y.
End I10.


Module I11.
  Definition I11 (y : nat) : Prop :=
    forall (x : nat), x < y /\ forall (z : nat), y > z -> exists (x : nat), x > z.

  (** I11

    [y] is free.  the first [x] is bound by [forall x].  the second
    [x] is bound by [forall z]. both [z]s are bound by [forall z].j
   *)
End I11.


Module I12.
  Definition I12 : Prop :=
    forall (z : nat), exists (y : nat), z < y /\ y < z.

  (** I12

    Suppose [s = y + 1].  Then if [i12 : I12], [i12 s] would result in
    the capture of the [y] in [s] by [exists y].  We therefore replace [y]
    with [w] in [exists y] so that if [i12 : I12], then [i12 s] is [exists
    w, y + 1 < w /\ w < y + 1].
   *)

  Hypothesis i12 : I12.

  Variable y : nat.

  Check i12 (y + 1).  (* note how [y] is renamed to [y0] *)
End I12.


Module I13.
  Definition I13 (A : nat -> nat -> Prop) : Prop :=
    (forall (x : nat), exists (y : nat), A x y) -> (exists (y : nat), forall (x : nat), A x y).

  (** I13

    We must show

    (1) [exists y, forall x, A x y]

    on the assumption that

    (2)  [forall x, exists y, A x y].

    What can we do with (2)?  First, we can see that

    (3)  [exists y, A u y]

    where [u] is free.  Then, if we can derive some [P] from the _assumption_
    [A u y], where [y] does not occur free anywhere but [A u y], we can conclude [P]
    from (3) and dismiss the assumption [A u y].

    But now we are stuck--to show (1), we need first to show [forall u, A u y].  But
    we can not do this from the _assumption_ [A u y], since [u] must be arbitrary, i.e.,
    it must not appear in any assumptions from which we conclude [A u y] (which is itself
    the assumption in this case.)
   *)

  Hypothesis A : nat -> nat -> Prop.

  Theorem i13 : I13 A.
  Proof.
    unfold I13.
    intros H.
    refine (ex_intro (fun y => forall (x : nat), A x y) _ _).
      intros x.
      pose (H' := H x).
      refine (ex_ind _ H').
        intros x0.
        intros H''.
  Abort.
End I13.


Module I14.
  Hypothesis A : nat -> Prop.
  Hypothesis B : Prop.

  Definition P : Prop :=
    forall (x : nat), A x -> B.

  Definition Q : Prop :=
    (exists (x : nat), A x) -> B.

  Theorem I14a : P -> Q.
  Proof.
    unfold P, Q.
    intros f e.
    exact (ex_ind f e).
  Qed.

  Theorem I14b : Q -> P.

  Proof.
    unfold P, Q.
    intros p x Ax.
    refine (p _).
      exact (ex_intro _ x Ax).
  Qed.
End I14.
