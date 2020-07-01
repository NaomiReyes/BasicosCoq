(* Razonamiento automatizado 2020-2
   Loyola Cruz Luis Fernando.
   Reyes Granados Naomi Itzel.
   Tarea 5, Tácticas Lógica clásica*)

Require Import Classical.

Parameters (p q r s u v C:Prop)
           (A: Set)
           (a z:A)
           (P Q S B R: A -> Prop).


Check classic.

Check classic u.

Check classic (u\/v).

Check NNPP.

Check NNPP v.

Check NNPP (u -> v).


Lemma trans: forall P Q R :Prop, ((P\/Q->False)->R) /\ (R->False) -> ((P\/Q->False)->False).
Proof.
intros.
destruct H.
apply H1.
apply H.
assumption.
Qed.

Lemma syhi: forall P Q R :Prop, ((~(P \/ Q) -> R) /\ ~R) -> (P \/ Q).
intro.
intro.
intro.
unfold not.
intro.
destruct H.
cut (~~(P0 \/ Q0)).
intro.
apply NNPP.
assumption.
unfold not.
apply (trans P0 Q0 R0).
split.
assumption.
assumption.
Qed.

Theorem ej1: ((p->q) /\ (~(p \/ r) -> s) /\ (p \/ q -> r)) -> (~s -> r).
Proof.
unfold not.
intros.
destruct H.
destruct H1.
cut (p\/r).
intro.
destruct H3.
apply H2.
left.
assumption.
assumption.
apply (syhi p r s).
split.
unfold not.
assumption.
unfold not.
assumption.
Qed.

Theorem ej2: ((p/\~q) /\ (p -> ~q)) -> (~(p->q) /\ (q->~p)).
Proof.
unfold not.
intros.
destruct H.
destruct H.
split.
intro.
apply H0.
assumption.
apply H2.
assumption.
intros.
apply H1.
assumption.
Qed.

Theorem eje3: (forall x:A, P x -> ~B x) -> (R a -> (forall x:A, R x -> B x) -> ~P a).
Proof.
intros.
unfold not.
intro.
absurd (B a).
apply H.
assumption.
apply H1.
assumption.
Qed.


Theorem eje4: (((exists x:A, P x /\ ~Q x) -> (forall y:A, P y -> R y)) /\ (exists x:A, P x /\ S x) /\ (forall x:A, P x -> ~R x)) -> (exists x:A, S x /\ Q x).
Proof.
intros.
destruct H.
destruct H0.
destruct H0.
destruct H0.
exists x.
split.
assumption.
apply NNPP.
unfold not.
intro.
absurd (R x).
apply H1.
assumption.
apply H.
exists x.
split.
assumption.
unfold not.
assumption.
assumption.
Qed.
