(* Proyecto 2
   Reyes Granados Naomi Itzel
   Árboles Binarios *)

Require Import Nat.
Require Import List.
Require Import Arith Omega.
Require Import PeanoNat.
Require Import NZAxioms NZBase Decidable OrdersTac.
Require Import NAxioms NProperties OrdersFacts.

Section TREES.
Variable V: Type.

Parameters (A:Type).

Definition nodo := V.

(* Definicion de arboles binarios*)
Inductive tree: Type :=
  | N : nodo -> tree
  | T : tree -> tree -> tree.

(* Funcion potencia*)		   
Fixpoint pot n m :=
  match m with
  | 0 => 1
  | S p => (n)*(pot n p)
  end.

(* Función que nos regresa el número de hojas del árbol*)
Fixpoint size (t:tree) : nat :=
  match t with
  | N n => 1
  | T tr tl => (size tr) + (size tl)
  end.

(* Función que nos regresa el número de nodos internos del árbol*)
Fixpoint nsize (t:tree) : nat :=
  match t with
  |N n => 0
  |T t1 t2 => (nsize t1) + (nsize t2) + 1
  end.

(* Función que nos regresa la profundidad árbol*)
Fixpoint depth (t:tree) : nat :=
  match t with
  |N n => 0
  |T t1 t2 => 1 + (max (depth t1) (depth t2))
  end.

(* Función de orden superior que mapea una función f
   a los elementos de las hojas del árbol*)
Fixpoint maptree (f: V -> V) (t:tree): tree :=
  match t with
  |N n => N (f n)
  |T t1 t2 => T (maptree f t1) (maptree f t2)
  end.

(* Función de orden superior *)
Fixpoint foldbtree (f: V -> V -> V) (t:tree): V :=
  match t with
  |N n => n
  |T t1 t2 => f (foldbtree f t1) (foldbtree f t2)
  end.

(* Función que nos regresa una lista con todos los
   nodos del árbol*)  
Fixpoint subtrees (t:tree) : list (tree) :=
  match t with
  |N n => (N n)::nil
  |T t1 t2 => (subtrees t1) ++ ((T t1 t2)::(subtrees t2))
  end.

(* Función que regresa la longitud de una lista*)  
Fixpoint length (l:list tree) : nat :=
  match l with
  |nil => 0
  |(b::bs) => 1 + (length bs)
  end.

(* Función que nos regresa el natural más grande entre
   dos opciones*)
Fixpoint maximo (n:nat) (m:nat) : nat:=
  match n with
  |0 => m
  |S k => if (m <? (S k)) then (S k) else m
  end.
  
(* Función que nos dice si un árbol es una hoja*)  
Fixpoint esHoja (t:tree): Prop:=
  match t with
  |N n => True
  |T t1 t2 => False
  end.

(* Función que nos dice si un árbol no es una hoja*)
Fixpoint esInductivo (t:tree): Prop :=
  match t with
  |N n => False
  |T t1 t2 => True
  end.

(* Función que nos regresa el subárbol izquierdo*)
Fixpoint sacaIzquierdo (t:tree): tree :=
  match t with
  |N n => N n
  |T t1 t2 => t1
  end.
(* Función que nos regresa el subárbol derecho*)  
Fixpoint sacaDerecho (t:tree): tree :=
  match t with
  |N n => N n
  |T t1 t2 => t2
  end.

(* Demostración de que para todo árbol al menos tiene
   una hoja.*) 
Lemma lema0: forall t:tree, 1 <= (size t).
Proof.
intros.
induction t.
simpl.
trivial.
simpl.
rewrite -> IHt1.
apply le_plus_l.
Qed.

(* Demostación de que para todo natural a, 2^a será
   mayor o igua a 1*)
Lemma lema01: forall a:nat, 1 <= (pot 2 a).
Proof.
intros.
induction a.
simpl.
trivial.
simpl.
apply le_plus_trans.
apply IHa.
Qed.

(*Demostracion de que 2^(s n) = (2^n) + (2^n)*)
Lemma lema04: forall n:nat, pot 2 (S n)  = (pot 2 n) + (pot 2 n).
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc_reverse.
simpl.
trivial.
Qed.

(* Demostración de que la función length abre con la concatenación*)
Lemma lema11: forall l1 l2 : list (tree), length (l1++l2) = (length l1) + (length l2).
Proof.
intros.
induction l1.
simpl.
trivial.
simpl.
auto.
Qed.

(* Demostracion de que el sucesor es analogo a sumarle un elemento*)
Lemma lemma10: forall n : nat, S(n) = n+1.
Proof.
intros.
induction n.
auto.
simpl.
rewrite IHn.
trivial.
Qed.

(* Demostacion de untipo de asociatividad*)
Lemma asoc: forall n m k :nat, n+(m+k)=m+(n+k).
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite IHn.
rewrite plus_n_Sm.
trivial.
Qed.

(* Demostracion de neutro aditivo*)
Lemma sum0: forall n:nat, n+0 = n.
Proof.
intros.
induction n.
trivial.
simpl.
rewrite IHn.
trivial.
Qed.


(* Demostración de que se cumple la propiedad size t = nsize t + 1 
   para cualquier t árbol*)
Lemma lema1: forall t:tree, (size t) = (nsize t + 1).
Proof.
intro.
induction t.
simpl.
reflexivity.
simpl.
rewrite -> IHt1.
rewrite -> IHt2.
rewrite plus_assoc_reverse.
symmetry.
rewrite plus_assoc_reverse.
rewrite plus_assoc_reverse.
simpl.
symmetry.
rewrite Peano.plus_n_Sm.
reflexivity.
Qed.

(*Demostracion de que se cumple la propiedad de length (subtrees t) + 1 = 2*(size t)
  para cualquier t árbol.*)
Lemma lema2: forall t:tree, (length (subtrees t)) + 1 = 2*(size t).
Proof.
intros.
induction t.
simpl.
trivial.
simpl.
rewrite lema11.
simpl.
rewrite plus_assoc_reverse.
rewrite asoc.
rewrite IHt1.
rewrite lemma10.
rewrite IHt2.
simpl.
rewrite sum0.
rewrite asoc.
rewrite plus_assoc.
rewrite asoc.
rewrite sum0.
rewrite plus_assoc.
rewrite sum0.
rewrite plus_assoc.
rewrite asoc.
rewrite plus_assoc.
rewrite plus_assoc.
trivial.
Qed.

(* Demostración de que se cumple que para todo número que sea un sucesor 
   será mayor estricto que 0*)
Lemma lema12: forall n:nat, 0 < S n.
Proof.
intros.
induction n.
auto.
auto.
Qed.

Lemma lema13: forall n m k:nat, (k < n /\ m = k) -> m<n.
Proof.
intros.
destruct H.
rewrite H0.
apply H.
Qed.

(* Demostración de que si un árbol tiene profundidad 0 entonces es una hoja*)
Lemma lemma03: forall t:tree, (depth t = 0) -> (esHoja t).
Proof.
intro.
induction t.
simpl.
trivial.
simpl.
intro.
inversion H.
Qed.

(* Demostración de que si un árbol tiene profundidad mayor a 0
  entonces es un árbol con rama derecha e izquierda.*)
Lemma lema02: forall t:tree, (0 < depth t) -> (esInductivo t).
Proof.
intro.
induction t.
simpl.
intro.
inversion H.
simpl.
intro.
auto.
Qed.

(* Demostración de que si un árbol es una hoja
  entonces su prfundidad es 1*)
Lemma lema05: forall t:tree, (esHoja t) -> (size t = 1).
Proof.
intro.
induction t.
simpl.
auto.
simpl.
intro.
absurd (False).
contradict H.
apply H.
Qed.



(* Este lema ayudaria a terminar la demostración del lema 4
Lemma lema14: forall n m k:nat, (1 <= k /\ n <= m) -> 1+n <= m+k.
intro.
intro.
intro.
induction n.
intros.
destruct H.
induction m.
simpl.
apply H.
simpl.

Casi salia :C pero ya no me dio tiempo de terminar el
lema auxiliar anterior para el caso inductivo.

Lemma lema4: forall t:tree, (depth t) +1 <= (size t).
Proof.
intros.
(*remember (depth t).*)
induction t.
simpl.
trivial.
simpl.
destruct (Nat.max_dec (depth t1) (depth t2)).
rewrite e.
rewrite lemma10.
rewrite plus_assoc_reverse.
rewrite asoc.

Lema para ver que si es un árbol t con rama derecha e izquierda entonces
  la altura de cada lado siempre es menor que la del arbol t. Sería ocupado
  para demostrar el lema 3.
Lemma lema06: forall t:tree, (esInductivo t) -> ((depth (sacaIzquierdo t) < depth t) /\ (depth (sacaDerecho t) < depth t)).
Proof.
intro.
induction t.
simpl.
intro.
inversion H.
simpl.
intro.
split.
unfold lt.
simpl.
destruct (Nat.max_dec (depth t1) (depth t2)).
rewrite e.
trivial.
rewrite e.
rewrite lemma10.
auto.

Estaba en proceso, pero necesitaba mas cosas para terminar la demostración
en lo ultimo que me quede es que necesitaba el lema anterior.
Lemma lema3: forall t: tree, size t <= pot 2 (depth t).
intros.
remember (depth t).
induction n.
simpl.
assert (esHoja t).
apply lemma03.
rewrite Heqn.
reflexivity.
assert (size t = 1).
apply lema05.
apply H.
rewrite H0.
trivial.
assert (esInductivo t).
apply lema02.
rewrite <- Heqn.
apply lema12.*)


