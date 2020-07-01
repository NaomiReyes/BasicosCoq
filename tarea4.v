(* Razonamiento automatizado 2020-2
   Loyola Cruz Luis Fernando.
   Reyes Granados Naomi Itzel.
   Tarea 4, Tácticas básicas y negación clásica*)

Variables p q r s t x l m:Prop.
Variables U:Type.
Variables P Q: U -> Prop.
Variables R : U -> U -> Prop.
Variables a b : U.


Section LPyLPO.

Theorem DilemaC : (p -> q) -> (r -> s) -> p \/ r -> q \/ s. 
Proof.
intro.
intro.
intro.
destruct H1.
left.
apply H.
assumption.
right.
apply H0.
assumption.
Qed.


Theorem Distrib : p \/ (q /\ r) -> (p \/ q) /\ (p \/ r).
Proof.
intro.
split.
destruct H.
left.
assumption.
destruct H.
right.
assumption.
destruct H.
left.
assumption.
destruct H.
right.
assumption.
Qed.



Theorem Argumento1: ((x \/ p) /\ q -> l) /\
                    (m \/ q -> s /\ t) /\
                    ((s /\ t) /\ l -> x) /\
                    (p -> q) ->
                    (m /\ p -> x).
Proof.
intro.
destruct H.
destruct H0.
destruct H1.
intro.
destruct H3.
apply H1.
split.
apply H0.
left.
assumption.
apply H.
split.
right.
assumption.
apply H2.
assumption.
Qed.


Theorem Socrates: (forall x:U, P x -> Q x) /\ P a -> Q a.
Proof.
intro.
destruct H.
apply H.
assumption.
Qed.


Theorem DistrExistsConj: (exists x:U, P x /\ Q x) -> (exists x:U, P x) /\ (exists x:U, Q x).
Proof.
intro.
split.
destruct H.
destruct H.
exists x0.
assumption.
destruct H.
destruct H.
exists x0.
assumption.
Qed.


Theorem Argumento2: (forall y:U, P y -> Q y) -> (forall x:U, (exists y:U, P y /\ R x y) -> exists z:U, Q z /\ R x z).
Proof.
intro.
intros.
destruct H0.
destruct H0.
exists x1.
split.
apply H.
assumption.
assumption.
Qed.


End LPyLPO.


Section LogConst.

Theorem NegImp: (p -> q) -> (p -> ~q) -> ~p.
Proof.
heorem NegImp: (p -> q) -> (p -> ~q) -> ~p.
Proof.
intros.
unfold not.
intro.
absurd (q).
apply H0.
assumption.
apply H.
assumption.
Qed.

Theorem nonoTExc: ~~(p \/ ~p).
Proof.
unfold not.
intro.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.

Theorem dmorganO : ~ ( p \/ q ) <-> ~p /\ ~q.
Proof.
unfold iff.
split.
unfold not.
intro.
split.
intro.
apply H.
left.
assumption.
intro.
apply H.
right.
assumption.
unfold not.
intros.
destruct H.
destruct H0.
apply H.
assumption.
apply H1.
assumption.
Qed.

Theorem Argumento3: (forall x:U, P x -> Q x) /\
              (~ exists x:U, P x /\ Q x) ->
              ~ exists x:U, P x.
Proof.
unfold not.
intros.
destruct H.
destruct H0.
apply H1.
exists x0.
split.
assumption.
apply H.
assumption.
Qed.


End LogConst.
