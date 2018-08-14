(* T6: Lógica en Coq *)

Set Warnings "-notation-overridden,-parsing".
Require Export T5_Tacticas.

(* El contenido del tema es
   1. Introducción
   2. Conectivas lógicas 
      1. Conjunción 
      2. Disyunción  
      3. Falsedad y negación  
      4. Verdad
      5. Equivalencia lógica
      6. Cuantificación existencial  
   3. Programación con proposiciones 
   4. Aplicando teoremas a argumentos 
   5. Coq vs. teoría de conjuntos 
      1. Extensionalidad funcional
      2. Proposiciones y booleanos  
      3. Lógica clásica vs. constructiva  
   Bibliografía
 *)

(* =====================================================================
   § 1. Introducción 
   ================================================================== *)


(* ---------------------------------------------------------------------
   Ejemplo 1.1. Calcular el tipo de las siguientes expresiones
      3 = 3.
      3 = 4.
      forall n m : nat, n + m = m + n.
      forall n : nat, n = 2.
   ------------------------------------------------------------------ *)


Check 3 = 3.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

(* ---------------------------------------------------------------------
   Nota. El tipo de las fórmulas es Prop.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 1.2.3. Demostrar que 2 más dos es 4.
   ------------------------------------------------------------------ *)

Theorem suma_2_y_2:
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Nota. Usa la proposición '2 + 2 = 4'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 1.2.2. Definir la proposición 
      prop_suma: Prop
   que afirma que la suma de 2 y 2 es 4. 
   ------------------------------------------------------------------ *)

Definition prop_suma: Prop := 2 + 2 = 4.

(* ---------------------------------------------------------------------
   Ejemplo 1.2.3. Calcular el tipo de prop_suma
   ------------------------------------------------------------------ *)

Check prop_suma.
(* ===> prop_suma : Prop *)

(* ---------------------------------------------------------------------
   Ejemplo 1.2.4. Usando prop_suma, demostrar que la suma de 2 y 2 es 4.
   ------------------------------------------------------------------ *)

Theorem prop_suma_es_verdadera:
  prop_suma.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.3.1. Definir la proposición 
      es_tres (n : nat) : Prop
   tal que (es_tres n) se verifica si n es el número 3.
   ------------------------------------------------------------------ *)

Definition es_tres (n : nat) : Prop :=
  n = 3.

(* ---------------------------------------------------------------------
   Ejemplo 1.3.2. Calcular el tipo de las siguientes expresiones
      es_tres.
      es_tres 3.
      es_tres 5.
   ------------------------------------------------------------------ *)

Check es_tres.
(* ===> nat -> Prop *)

Check es_tres 3.
(* ===> Prop *)

Check es_tres 5.
(* ===> Prop *)

(* ---------------------------------------------------------------------
   Nota. Ejemplo de proposición parametrizada.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 1.4.1. Definir la función
      inyectiva {A B : Type} (f : A -> B) : Prop :=
   tal que (inyectiva f) se verifica si f es inyectiva.
   ------------------------------------------------------------------ *)

Definition inyectiva {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

(* ---------------------------------------------------------------------
   Ejemplo 1.4.2. Demostrar que la funcion sucesor es inyectiva; es
   decir, 
      inyectiva S.
   ------------------------------------------------------------------ *)

Lemma suc_iny: inyectiva S.
Proof.
  intros n m H. (* n, m : nat
                   H : S n = S m
                   ============================
                   n = m *)
  inversion H.  (* n, m : nat
                   H : S n = S m
                   H1 : n = m
                   ============================
                   m = m *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.5. Calcular los tipos de las siguientes expresiones
      3 = 5.
      eq 3 5.
      eq 3.
      @eq.
   ------------------------------------------------------------------ *)

Check (3 = 5).
(* ===> Prop *)

Check (eq 3 5).
(* ===> Prop *)

Check (eq 3).
(* ===> nat -> Prop *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(* ---------------------------------------------------------------------
   Notas.
   1. La expresión (x = y) es una abreviatura de (eq x y).
   2. Se escribe @eq en lugar de eq para ver los argumentos implícitos.
   ------------------------------------------------------------------ *)

(* =====================================================================
   § 2. Conectivas lógicas 
   ================================================================== *)

(* =====================================================================
   §§ 2.1. Conjunción 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.1. Demostrar que
      3 + 4 = 7 /\ 2 * 2 = 4.
   ------------------------------------------------------------------ *)

Example ej_conjuncion: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.         
  -              (* 
                    ============================
                    3 + 4 = 7 *)
    reflexivity. 
  -              (* 
                    ============================
                    2 * 2 = 4 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Notas.
   1. El símbolo de conjunción se escribe con /\
   2. La táctica 'split' sustituye el objetivo (P /\ Q) por los
   subobjetivos P y Q. 
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.2. Demostrar que
      forall A B : Prop, A -> B -> A /\ B.
   ------------------------------------------------------------------ *)

Lemma conj_intro: forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. (* A, B : Prop
                       HA : A
                       HB : B
                       ============================
                       A /\ B *)
  split.
  -                 (* A, B : Prop
                       HA : A
                       HB : B
                       ============================
                       A *)
    apply HA.
  -                 (* A, B : Prop
                       HA : A
                       HB : B
                       ============================
                       B *)
    apply HB.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.3. Demostrar, con con_intro, que
      3 + 4 = 7 /\ 2 * 2 = 4.
   ------------------------------------------------------------------ *)

Example ej_conjuncion': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj_intro. 
  -                 (* 3 + 4 = 7 *)
    reflexivity.
  -                 (* 2 * 2 = 4 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.1.1. Demostrar que
      forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
   ------------------------------------------------------------------ *)

Example ejercicio_conj:
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.                      (* n, m : nat
                                        H : n + m = 0
                                        ============================
                                        n = 0 /\ m = 0 *)
  apply conj_intro.
  -                                  (* n, m : nat
                                        H : n + m = 0
                                        ============================
                                        n = 0 *)
    destruct n.
    +                                (* m : nat
                                        H : 0 + m = 0
                                        ============================
                                        0 = 0 *)
      reflexivity.
    +                                (* n, m : nat
                                        H : S n + m = 0
                                        ============================
                                        S n = 0 *)
      simpl in H.                    (* n, m : nat
                                        H : S (n + m) = 0
                                        ============================
                                        S n = 0 *)
      inversion H.
  -                                  (* n, m : nat
                                        H : n + m = 0
                                        ============================
                                        m = 0 *)
    destruct m.
    +                                (* n : nat
                                        H : n + 0 = 0
                                        ============================
                                        0 = 0 *)
      reflexivity.
    +                                (* n, m : nat
                                        H : n + S m = 0
                                        ============================
                                        S m = 0 *)
      rewrite suma_conmutativa in H. (* n, m : nat
                                        H : S m + n = 0
                                        ============================
                                        S m = 0 *)
      simpl in H.                    (* n, m : nat
                                        H : S (m + n) = 0
                                        ============================
                                        S m = 0 *)
      inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.4. Demostrar que
      forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
   ------------------------------------------------------------------ *)

Lemma ej_conjuncion2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.          (* n, m : nat
                            H : n = 0 /\ m = 0
                            ============================
                            n + m = 0 *)
  destruct H as [Hn Hm]. (* n, m : nat
                            Hn : n = 0
                            Hm : m = 0
                            ============================
                            n + m = 0 *)
  rewrite Hn.            (* 0 + m = 0 *)
  rewrite Hm.            (* 0 + 0 = 0 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'destruct H as [HA HB]' que  sustituye la
   hipótesis H de la forma (A /\ B) por las hipótesis HA (que afirma
   que A es verdad) y HB (que afirma que B es verdad).
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.5. Demostrar que
      forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
   ------------------------------------------------------------------ *)

Lemma ej_conjuncion2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].    (* n, m : nat
                            Hn : n = 0
                            Hm : m = 0
                            ============================
                            n + m = 0 *)
  rewrite Hn.            (* 0 + m = 0 *)
  rewrite Hm.            (* 0 + 0 = 0 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. La táctica 'intros x [HA HB]', cuando el objetivo es de la
   forma (forall x, A /\ B -> C), introduce la variable x y las
   hipótesis HA y HB afirmando la certeza de A y de B, respectivamente.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.6. Demostrar que
      forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
   ------------------------------------------------------------------ *)

Lemma ej_conjuncion2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm. (* n, m : nat
                       Hn : n = 0
                       Hm : m = 0
                       ============================
                       n + m = 0 *)
  rewrite Hn.       (* 0 + m = 0 *)
  rewrite Hm.       (* 0 + 0 = 0 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.7. Demostrar que
      forall n m : nat, n + m = 0 -> n * m = 0.
   ------------------------------------------------------------------ *)

Lemma ej_conjuncion3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.                (* n, m : nat
                                  H : n + m = 0
                                  ============================
                                  n * m = 0 *)
  assert (H' : n = 0 /\ m = 0). 
  -                            (* n, m : nat
                                  H : n + m = 0
                                  ============================
                                  n = 0 /\ m = 0 *)
    apply ejercicio_conj.      (* n + m = 0 *)
    apply H.
  -                            (* n, m : nat
                                  H : n + m = 0
                                  H' : n = 0 /\ m = 0
                                  ============================
                                  n * m = 0 *)
    destruct H' as [Hn Hm].    (* n, m : nat
                                  H : n + m = 0
                                  Hn : n = 0
                                  Hm : m = 0
                                  ============================
                                  n * m = 0 *)
    rewrite Hn.                (* 0 * m = 0 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.8. Demostrar que
      forall P Q : Prop,
        P /\ Q -> P.
   ------------------------------------------------------------------ *)

Lemma conj_e1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ]. (* P, Q : Prop
                         HP : P
                         HQ : Q
                         ============================
                         P *)
  apply HP.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.1.2. Demostrar que
      forall P Q : Prop,
        P /\ Q -> Q.
   ------------------------------------------------------------------ *)

Lemma conj_e2: forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ]. (* P, Q : Prop
                         HP : P
                         HQ : Q
                         ============================
                         Q *)
  apply HQ.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.9. Demostrar que
      forall P Q : Prop,
        P /\ Q -> Q /\ P.
   ------------------------------------------------------------------ *)

Theorem conj_conmutativa: forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. (* P, Q : Prop
                         HP : P
                         HQ : Q
                         ============================
                         Q /\ P *)
  split.
  -                   (* P, Q : Prop
                         HP : P
                         HQ : Q
                         ============================
                         Q *)
    apply HQ.
  -                   (* P, Q : Prop
                         HP : P
                         HQ : Q
                         ============================
                         P *)
    apply HP.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.1.3. Demostrar que
      forall P Q R : Prop,
        P /\ (Q /\ R) -> (P /\ Q) /\ R.
   ------------------------------------------------------------------ *)

Theorem conj_asociativa : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. (* P, Q, R : Prop
                                HP : P
                                HQ : Q
                                HR : R
                                ============================
                                (P /\ Q) /\ R *)
  split.
  -                          (* P /\ Q *)
    split.
    +                        (* P *)
      apply HP.
    +                        (* Q *)
      apply HQ.
  -                          (* R *)
    apply HR.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'intros P Q R [HP [HQ HR]]'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.10. Calcular el tipo de la expresión
      and
   ------------------------------------------------------------------ *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ---------------------------------------------------------------------
   Nota. (x /\ y) es una abreviatura de (and x y).
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.2. Disyunción  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.1. Demostrar que
      forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Lemma disy_ej1:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm]. 
  -                        (* n, m : nat
                              Hn : n = 0
                              ============================
                              n * m = 0 *)
    rewrite Hn.            (* 0 * m = 0 *)
    reflexivity.           
  -                        (* n, m : nat
                              Hm : m = 0
                              ============================
                              n * m = 0 *)
    rewrite Hm.            (* n * 0 = 0 *)
    rewrite <- mult_n_O.    (* 0 = 0 *)
    reflexivity.
Qed.

(* 2ª demostración *)
Lemma disy_ej:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm]. 
  -                     (* n, m : nat
                           Hn : n = 0
                           ============================
                           n * m = 0 *)
    rewrite Hn.         (* 0 * m = 0 *)
    reflexivity.
  -                     (* n, m : nat
                           Hm : m = 0
                           ============================
                           n * m = 0 *)
    rewrite Hm.         (* n * 0 = 0 *)
    rewrite <- mult_n_O. (* 0 = 0 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Notas.
   1. La táctica 'destruct H as [Hn | Hm]', cuando la hipótesis H es de
      la forma (A \/ B), la divide en dos casos: uno con hipótesis HA
      (afirmando la certeza de A) y otro con la hipótesis HB (afirmando
      la certeza de B).   
   2. La táctica 'intros x [HA | HB]', cuando el objetivo es de la
      forma (forall x, A \/ B -> C), intoduce la variable x y dos casos:
      uno con hipótesis HA (afirmando la certeza de A) y otro con la
      hipótesis HB (afirmando la certeza de B).
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.2. Demostrar que
      forall A B : Prop, A -> A \/ B.
   ------------------------------------------------------------------ *)

Lemma disy_intro: forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA. (* A, B : Prop
                    HA : A
                    ============================
                    A \/ B *)
  left.          (* A *)
  apply HA.
Qed.

(* ---------------------------------------------------------------------
   Nota. La táctica 'left' sustituye el objetivo de la forma (A \/ B)
   por A.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.3. Demostrar que
      forall n : nat, n = 0 \/ n = S (pred n).
   ------------------------------------------------------------------ *)

Lemma cero_o_sucesor:
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  -              (* 
                    ============================
                    0 = 0 \/ 0 = S (Nat.pred 0) *)
    left.        (* 0 = 0 *)
    reflexivity. 
  -              (* n : nat
                    ============================
                    S n = 0 \/ S n = S (Nat.pred (S n)) *)
    right.       (* S n = S (Nat.pred (S n)) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. La táctica 'right' sustituye el objetivo de la forma (A \/ B)
   por B.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 2.2.1. Demostrar que
      forall n m, n * m = 0 -> n = 0 \/ m = 0.
   ------------------------------------------------------------------ *)

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.          (* n, m : nat
                            H : n * m = 0
                            ============================
                            n = 0 \/ m = 0 *)
  destruct n as [|n'].
  -                      (* m : nat
                            H : 0 * m = 0
                            ============================
                            0 = 0 \/ m = 0 *)
    left.                (* 0 = 0 *)
    reflexivity.
  -                      (* n', m : nat
                            H : S n' * m = 0
                            ============================
                            S n' = 0 \/ m = 0 *)
    destruct m as [|m']. 
    +                    (* n' : nat
                            H : S n' * 0 = 0
                            ============================
                            S n' = 0 \/ 0 = 0 *)
      right.             (* 0 = 0 *)
      reflexivity.
    +                    (* n', m' : nat
                            H : S n' * S m' = 0
                            ============================
                            S n' = 0 \/ S m' = 0 *)
      simpl in H.        (* n', m' : nat
                            H : S (m' + n' * S m') = 0
                            ============================
                            S n' = 0 \/ S m' = 0 *)
      inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.2. Demostrar que
      forall P Q : Prop,
        P \/ Q  -> Q \/ P.
   ------------------------------------------------------------------ *)

Theorem disy_conmutativa: forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ]. 
  -                     (* P, Q : Prop
                           HP : P
                           ============================
                           Q \/ P *)
    right.              (* P *)
    apply HP.
  -                     (* P, Q : Prop
                           HQ : Q
                           ============================
                           Q \/ P *)
    left.               (* Q *)
    apply HQ.
Qed.
  
(* ---------------------------------------------------------------------
   Ejemplo 2.2.4. Calcular el tipo de la expresión
      or
   ------------------------------------------------------------------ *)

Check or.
(* ===> or : Prop -> Prop -> Prop *)

(* ---------------------------------------------------------------------
   Nota. (x \/ y) es una abreviatura de (or x y).
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.3. Falsedad y negación  
   ================================================================== *)

Module DefNot.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.1. Definir la función
      not (P : Prop) : Prop
   tal que (not P) es la negación de P
   ------------------------------------------------------------------ *)

Definition not (P:Prop) : Prop :=
    P -> False.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.2. Definir (~ x) como abreviatura de (not x).
   ------------------------------------------------------------------ *)

Notation "~ x" := (not x) : type_scope.

(* ---------------------------------------------------------------------
   Nota. Esta es la forma como está definida la negación en Coq.
   ------------------------------------------------------------------ *)

End DefNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] (or [inversion]) on it to complete
    any goal: *)

(* ---------------------------------------------------------------------
   Ejemplo 2.3.3. Demostrar que
      forall (P:Prop),
        False -> P.
   ------------------------------------------------------------------ *)

Theorem ex_falso_quodlibet: forall (P:Prop),
  False -> P.
Proof.
  intros P H. (* P : Prop
                 H : False
                 ============================
                 P *)
  destruct H.
Qed.

(* ---------------------------------------------------------------------
   Nota. En latín, "ex falso quodlibet" significa "de lo falso (se
   sigue) cualquier cosa". 
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 2.3.1. Demostrar que
      forall (P:Prop),
        ~ P -> (forall (Q:Prop), P -> Q).
   ------------------------------------------------------------------ *)

Fact negacion_elim: forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.     (* 
                     ============================
                     forall P : Prop, (P -> False) -> forall Q : Prop, P -> Q *)
  intros P H1.    (* P : Prop
                     H1 : P -> False
                     ============================
                     forall Q : Prop, P -> Q *)
  intros Q H2.    (* P : Prop
                     H1 : P -> False
                     Q : Prop
                     H2 : P
                     ============================
                     Q *)
  apply H1 in H2. (* P : Prop
                     H1 : P -> False
                     Q : Prop
                     H2 : False
                     ============================
                     Q *)
  destruct H2.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.4. Demostrar que
      ~(0 = 1).
   ------------------------------------------------------------------ *)

Theorem cero_no_es_uno: ~(0 = 1).
Proof.
  intros H.       (* H : 0 = 1
                     ============================
                     False *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Nota. La expresión (x <> y) es una abreviatura de ~(x = y).
   ------------------------------------------------------------------ *)


Theorem cero_no_es_uno': 0 <> 1.
Proof.
  intros H.       (* H : 0 = 1
                     ============================
                     False *)
  inversion H. 
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.5. Demostrar que
      ~ False
   ------------------------------------------------------------------ *)


Theorem not_False :
  ~ False.
Proof.
  unfold not. (* 
                 ============================
                 False -> False *)
  intros H.   (* H : False
                 ============================
                 False *)
  destruct H. 
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.6. Demostrar que
      forall P Q : Prop,
        (P /\ ~P) -> Q.
   ------------------------------------------------------------------ *)

Theorem contradiccion_implica_cualquiera: forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP]. (* P, Q : Prop
                          HP : P
                          HNP : ~ P
                          ============================
                          Q *)
  unfold not in HNP. (* P, Q : Prop
                          HP : P
                          HNP : P -> False
                          ============================
                          Q *)
  apply HNP in HP. (* P, Q : Prop
                          HP : False
                          HNP : P -> False
                          ============================
                          Q *)
  destruct HP.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.7. Demostrar que
      forall P : Prop,
        P -> ~~P.
   ------------------------------------------------------------------ *)

Theorem doble_neg: forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. (* P : Prop
                 H : P
                 ============================
                 ~ ~ P *)
  unfold not. (* (P -> False) -> False *)
  intros G.   (* P : Prop
                 H : P
                 G : P -> False
                 ============================
                 False *)
  apply G.    (* P *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.3.2. Demostrar que
      forall (P Q : Prop),
        (P -> Q) -> (~Q -> ~P).
   ------------------------------------------------------------------ *)

Theorem contrapositiva: forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.          (* 
                          ============================
                          forall P Q : Prop, 
                            (P -> Q) -> (Q -> False) -> P -> False *)
  intros P Q H1 H2 H3. (* P, Q : Prop
                          H1 : P -> Q
                          H2 : Q -> False
                          H3 : P
                          ============================
                          False *)
  apply H1 in H3.      (* P, Q : Prop
                          H1 : P -> Q
                          H2 : Q -> False
                          H3 : Q
                          ============================
                          False *)
  apply H2 in H3.      (* P, Q : Prop
                          H1 : P -> Q
                          H2 : Q -> False
                          H3 : False
                          ============================
                          False *)
  apply H3.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.3.3. Demostrar que
      forall P : Prop,
        ~ (P /\ ~P).
   ------------------------------------------------------------------ *)

Theorem no_contradiccion: forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.       (* 
                       ============================
                       forall P : Prop, P /\ (P -> False) -> False *)
  intros P [H1 H2]. (* P : Prop
                       H1 : P
                       H2 : P -> False
                       ============================
                       False *)
  apply H2.         (* P *)
  apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.8. Demostrar que
      forall b : bool,
        b <> true -> b = false.
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Theorem no_verdadero_es_falso: forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -                           (* H : true <> true
                                 ============================
                                 true = false *)
    unfold not in H.          (* H : true = true -> False
                                 ============================
                                 true = false *)
    apply ex_falso_quodlibet. (* H : true = true -> False
                                 ============================
                                 False *)
    apply H.                  (* true = true *)
    reflexivity.
  -                           (* H : false <> true
                                 ============================
                                 false = false *)
    reflexivity.
Qed.

(* 2ª demostración *)
Theorem no_verdadero_es_falso': forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -                  (* H : true <> true
                        ============================
                        true = false *)
    unfold not in H. (* H : true = true -> False
                        ============================
                        true = false *)
    exfalso.         (* H : true = true -> False
                        ============================
                        False *)
    apply H.         (* true = true *)
    reflexivity.
  -                  (* H : false <> true
                        ============================
                        false = false *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Notas. 
   1. Uso de 'apply ex_falso_quodlibet' en la primera demostración.
   2. Uso de 'exfalso' en la segunda demostración.
   3. La táctica 'exfalso' sustituye el objetivo por falso. 
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.4. Verdad
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.4.1. Demostrar que la proposición True es verdadera.
   ------------------------------------------------------------------ *)

Lemma True_es_verdadera : True.
Proof.
  apply I.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso del constructor I.
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.5. Equivalencia lógica  
   ================================================================== *)

Module DefIff.

  (* ---------------------------------------------------------------------
   Ejemplo 2.5.1. Definir la función
      iff (P Q : Prop) : Prop
   tal que  (iff P Q) es la equivalencia de P y Q.
   ------------------------------------------------------------------ *)


Definition iff (P Q : Prop) : Prop := (P -> Q) /\ (Q -> P).

(* ---------------------------------------------------------------------
   Ejemplo 2.5.2. Definir (P <-> Q) como una abreviatura de (iff P Q). 
   ------------------------------------------------------------------ *)

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End DefIff.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.3. Demostrar que
      forall P Q : Prop,
        (P <-> Q) -> (Q <-> P).
   ------------------------------------------------------------------ *)

Theorem iff_sim : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP]. (* P, Q : Prop
                           HPQ : P -> Q
                           HQP : Q -> P
                           ============================
                           Q <-> P *)
  split.
  -                     (* P, Q : Prop
                           HPQ : P -> Q
                           HQP : Q -> P
                           ============================
                           Q -> P *)
    apply HQP.
  -                     (* P, Q : Prop
                           HPQ : P -> Q
                           HQP : Q -> P
                           ============================
                           P -> Q *)
    apply HPQ.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.4. Demostrar que
      forall b : bool,
        b <> true <-> b = false.
   ------------------------------------------------------------------ *)

Lemma not_true_iff_false : forall b : bool,
  b <> true <-> b = false.
Proof.
  intros b.                      (* b : bool
                                    ============================
                                    b <> true <-> b = false *)
  split.
  -                              (* b : bool
                                    ============================
                                    b <> true -> b = false *)
    apply no_verdadero_es_falso. 
  -                              (* b : bool
                                    ============================
                                    b = false -> b <> true *)
    intros H.                    (* b : bool
                                    H : b = false
                                    ============================
                                    b <> true *)
    rewrite H.                   (* false <> true *)
    intros H'.                   (* b : bool
                                    H : b = false
                                    H' : false = true
                                    ============================
                                    False *)
    inversion H'.
Qed.


(* ---------------------------------------------------------------------
   Ejercicio 2.3.4. Demostrar que
      forall P : Prop,
        P <-> P.
   ------------------------------------------------------------------ *)

Lemma iff_refl_aux: forall P : Prop,
    P -> P.
Proof.
  intros P H. (* P : Prop
                 H : P
                 ============================
                 P *)
  apply H.
Qed.

Theorem iff_refl: forall P : Prop,
    P <-> P.
Proof.
  split.
  -                     (* P : Prop
                           ============================
                           P -> P *)
    apply iff_refl_aux. 
  -                     (* P : Prop
                           ============================
                           P -> P *)
    apply iff_refl_aux.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.3.5. Demostrar que
      forall P Q R : Prop,
        (P <-> Q) -> (Q <-> R) -> (P <-> R).
   ------------------------------------------------------------------ *)

Theorem iff_trans: forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [HPQ HQP] [HQR HRQ]. (* P, Q, R : Prop
                                       HPQ : P -> Q
                                       HQP : Q -> P
                                       HQR : Q -> R
                                       HRQ : R -> Q
                                       ============================
                                       P <-> R *)
  split.
  -                                 (* P, Q, R : Prop
                                       HPQ : P -> Q
                                       HQP : Q -> P
                                       HQR : Q -> R
                                       HRQ : R -> Q
                                       ============================
                                       P -> R *)
    intros HP.                      (* P, Q, R : Prop
                                       HPQ : P -> Q
                                       HQP : Q -> P
                                       HQR : Q -> R
                                       HRQ : R -> Q
                                       HP : P
                                       ============================
                                       R *)
    apply HQR.                      (* Q *)
    apply HPQ.                      (* P *)
    apply HP.
  -                                 (* P, Q, R : Prop
                                       HPQ : P -> Q
                                       HQP : Q -> P
                                       HQR : Q -> R
                                       HRQ : R -> Q
                                       ============================
                                       R -> P *)
    intros HR.                      (* P, Q, R : Prop
                                       HPQ : P -> Q
                                       HQP : Q -> P
                                       HQR : Q -> R
                                       HRQ : R -> Q
                                       HR : R
                                       ============================
                                       P *)
    apply HQP.                      (* Q *)
    apply HRQ.                      (* R *)
    apply HR.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.3.6. Demostrar que
      forall P Q R : Prop,
        P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
   ------------------------------------------------------------------ *)

Theorem distributiva_disy_conj: forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split.
  -                             (* P, Q, R : Prop
                                   ============================
                                   P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R) *)
    intros [HP | [HQ HR]].
    +                           (* P, Q, R : Prop
                                   HP : P
                                   ============================
                                   (P \/ Q) /\ (P \/ R) *)
      split.
      *                         (* P, Q, R : Prop
                                   HP : P
                                   ============================
                                   P \/ Q *)
        left.                   (* P *)
        apply HP.
      *                         (* P, Q, R : Prop
                                   HP : P
                                   ============================
                                   P \/ R *)
        left.                   (* P *)
        apply HP.
    +                           (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   (P \/ Q) /\ (P \/ R) *)
      split.
      *                         (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   P \/ Q *)
        right.                  (* Q *)
        apply HQ.
      *                         (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   P \/ R *)
        right.                  (* R *)
        apply HR.
  -                             (* P, Q, R : Prop
                                   ============================
                                   (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R) *)
    intros [[HP1|HQ] [HP2|HR]]. 
    +                           (* P, Q, R : Prop
                                   HP1, HP2 : P
                                   ============================
                                   P \/ (Q /\ R) *)
      left.                     (* P *)
      apply HP1.
    +                           (* P, Q, R : Prop
                                   HP1 : P
                                   HR : R
                                   ============================
                                   P \/ (Q /\ R) *)
      left.                     (* P *)
      apply HP1.
    +                           (* P, Q, R : Prop
                                   HQ : Q
                                   HP2 : P
                                   ============================
                                   P \/ (Q /\ R) *)
      left.                     (* P *)
      apply HP2.
    +                           (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   P \/ (Q /\ R) *)
      right.                    (* Q /\ R *)
      split.
      *                         (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   Q *)
        apply HQ.
      *                         (* P, Q, R : Prop
                                   HQ : Q
                                   HR : R
                                   ============================
                                   R *)
        apply HR.
Qed.

(* ---------------------------------------------------------------------
   Nota. Se importa la librería Coq.Setoids.Setoid para usar las
   tácticas reflexivity y rewrite con iff.
   ------------------------------------------------------------------ *)

Require Import Coq.Setoids.Setoid.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.5. Demostrar que
      forall n m : nat, n * m = 0 <-> n = 0 \/ m = 0.
   ------------------------------------------------------------------ *)

Lemma mult_0 : forall n m : nat, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  -                  (* n, m : nat
                        ============================
                        n * m = 0 -> n = 0 \/ m = 0 *)
    apply mult_eq_0. 
  -                  (* n, m : nat
                        ============================
                        n = 0 \/ m = 0 -> n * m = 0 *)
    apply disy_ej.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.6. Demostrar que
      forall P Q R : Prop, 
        P \/ (Q \/ R) <-> (P \/ Q) \/ R.
   ------------------------------------------------------------------ *)

Lemma disy_asociativa :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.           (* P, Q, R : Prop
                             ============================
                             P \/ (Q \/ R) <-> (P \/ Q) \/ R *)
  split.
  -                       (* P, Q, R : Prop
                             ============================
                             P \/ (Q \/ R) -> (P \/ Q) \/ R *)
    intros [H | [H | H]]. 
    +                     (* P, Q, R : Prop
                             H : P
                             ============================
                             (P \/ Q) \/ R *)
      left.               (* P \/ Q *)
      left.               (* P *)
      apply H.
    +                     (* P, Q, R : Prop
                             H : Q
                             ============================
                             (P \/ Q) \/ R *)
      left.               (* P \/ Q *)
      right.              (* Q *)
      apply H.
    +                     (* P, Q, R : Prop
                             H : R
                             ============================
                             (P \/ Q) \/ R *)
      right.              (* R *)
      apply H.
  -                       (* P, Q, R : Prop
                             ============================
                             (P \/ Q) \/ R -> P \/ (Q \/ R) *)
    intros [[H | H] | H].
    +                     (* P, Q, R : Prop
                             H : P
                             ============================
                             (P \/ Q) \/ R *)
      left.               (* P *)
      apply H.
    +                     (* P, Q, R : Prop
                             H : Q
                             ============================
                             P \/ (Q \/ R) *)
      right.              (* Q \/ R *)
      left.               (* Q *)
      apply H.
    +                     (* P, Q, R : Prop
                             H : R
                             ============================
                             P \/ (Q \/ R) *)
      right.              (* Q \/ R *)
      right.              (* R *)
      apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.7. Demostrar que
      forall n m p : nat,
        n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
   ------------------------------------------------------------------ *)

Lemma mult_0_3: forall n m p : nat,
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.            (* n, m, p : nat
                              ============================
                              n * (m * p) = 0 <-> n = 0 \/ (m = 0 \/ p = 0) *)
  rewrite mult_0.          (* n * m = 0 \/ p = 0 <-> 
                              n = 0 \/ (m = 0 \/ p = 0) *)
  rewrite mult_0.          (* (n = 0 \/ m = 0) \/ p = 0 <-> 
                              n = 0 \/ (m = 0 \/ p = 0) *)
  rewrite disy_asociativa. (* (n = 0 \/ m = 0) \/ p = 0 <-> 
                              (n = 0 \/ m = 0) \/ p = 0 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de reflexivity y rewrite con iff.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.5.8. Demostrar que
      forall n m : nat,
        n * m = 0 -> n = 0 \/ m = 0.
   ------------------------------------------------------------------ *)

Lemma ej_apply_iff: forall n m : nat,
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. (* n, m : nat
                   H : n * m = 0
                   ============================
                   n = 0 \/ m = 0 *)
  apply mult_0. (* n * m = 0 *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de apply sobre iff.
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.6. Cuantificación existencial  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.6.1. Demostrar que
      exists n : nat, 4 = n + n.
   ------------------------------------------------------------------ *)

Lemma cuatro_es_par: exists n : nat, 4 = n + n.
Proof.
  exists 2.          (* 
                   ============================
                   4 = 2 + 2 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. La táctica 'exists a' sustituye el objetivo de la forma 
   (exists x, P(x)) por P(a).
   ------------------------------------------------------------------ *)

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

(* ---------------------------------------------------------------------
   Ejemplo 2.6.2. Demostrar que
      forall n : nat,
        (exists m, n = 4 + m) -> (exists o, n = 2 + o).
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Theorem ej_existe_2a: forall n : nat,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  destruct H as [a Ha].
  exists (2 + a).
  apply Ha.
Qed.

(* 2ª demostración *)
Theorem ej_existe_2b: forall n : nat,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [a Ha]. 
  exists (2 + a).
  apply Ha.
Qed.

(* ---------------------------------------------------------------------
   Notas.
   1. 'destruct H [a Ha]' sustituye la hipótesis (H : exists x, P(x)) 
      por (Ha : P(a)).
   2. 'intros x [a Ha]' sustituye el objetivo 
      (forall x, (exists y P(y)) -> Q(x)) por Q(x) y le añade la
      hipótesis (Ha : P(a)).
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 2.6.1. Demostrar que
      forall (X:Type) (P : X -> Prop),
        (forall x, P x) -> ~ (exists x, ~ P x)
   ------------------------------------------------------------------ *)

Theorem paraTodo_no_existe_no: forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1 [a Ha]. (* X : Type
                           P : X -> Prop
                           H1 : forall x : X, P x
                           a : X
                           Ha : ~ P a
                           ============================
                           False *)
  apply Ha.             (* P a *)
  apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.6.2. Demostrar que
      forall (X : Type) (P Q : X -> Prop),
        (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
   ------------------------------------------------------------------ *)

Theorem dist_existe: forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.                 (* X : Type
                                   P, Q : X -> Prop
                                   ============================
                                   (exists x:X, P x \/ Q x) <-> 
                                   (exists x:X, P x) \/ (exists x:X, Q x) *)
  split.
  -                             (* X : Type
                                   P, Q : X -> Prop
                                   ============================
                                   (exists x : X, P x \/ Q x) -> 
                                   (exists x:X, P x) \/ (exists x:X, Q x) *)
    intros [a [HPa | HQa]].
    +                           (* X : Type
                                   P, Q : X -> Prop
                                   a : X
                                   HPa : P a
                                   ============================
                                   (exists x:X, P x) \/ (exists x:X, Q x) *)
      left.                     (* exists x : X, P x *)
      exists a.                      (* P a *)
      apply HPa.
    +                           (* X : Type
                                   P, Q : X -> Prop
                                   a : X
                                   HQa : Q a
                                   ============================
                                   (exists x:X, P x) \/ (exists x:X, Q x) *)
      right.                    (* exists x : X, Q x *)
      exists a.                      (* Q a *)
      apply HQa.
  -                             (* X : Type
                                   P, Q : X -> Prop
                                   ============================
                                   (exists x:X, P x) \/ (exists x:X, Q x) -> 
                                   exists x : X, P x \/ Q x *)
    intros [[a HPa] | [a HQa]]. 
    +                           (* X : Type
                                   P, Q : X -> Prop
                                   a : X
                                   HPa : P a
                                   ============================
                                   exists x : X, P x \/ Q x *)
      exists a.                      (* P a \/ Q a *)
      left.                     (* P a *)
      apply HPa.
    +                           (* X : Type
                                   P, Q : X -> Prop
                                   a : X
                                   HQa : Q a
                                   ============================
                                   exists x : X, P x \/ Q x *)
      exists a.                      (* P a \/ Q a *)
      right.                    (* Q a *)
      apply HQa.
Qed.

(* =====================================================================
   § 3. Programación con proposiciones 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 3.1.1. Definir la función
      En {A : Type} (x : A) (xs : list A) : Prop :=
   tal que (En x xs) se verifica si x pertenece a xs.
   ------------------------------------------------------------------ *)

Fixpoint En {A : Type} (x : A) (xs : list A) : Prop :=
  match xs with
  | []        => False
  | x' :: xs' => x' = x \/ En x xs'
  end.

(* ---------------------------------------------------------------------
   Ejemplo 3.1.2. Demostrar que
      En 4 [1; 2; 3; 4; 5].
   ------------------------------------------------------------------ *)

Example En_ejemplo_1 : En 4 [1; 2; 3; 4; 5].
Proof.
  simpl.       (* 1 = 4 \/ 2 = 4 \/ 3 = 4 \/ 4 = 4 \/ 5 = 4 \/ False *)
  right.       (* 2 = 4 \/ 3 = 4 \/ 4 = 4 \/ 5 = 4 \/ False *)
  right.       (* 3 = 4 \/ 4 = 4 \/ 5 = 4 \/ False *)
  right.       (* 4 = 4 \/ 5 = 4 \/ False *)
  left.        (* 4 = 4 *)
  reflexivity. 
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.1.3. Demostrar que
      forall n : nat, 
        En n [2; 4] -> exists n', n = 2 * n'.
   ------------------------------------------------------------------ *)

Example En_ejemplo_2: forall n : nat,
    En n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.                   (* 
                              ============================
                              forall n : nat,
                               2 = n \/ 4 = n \/ False -> 
                               exists n' : nat, n = n' + (n' + 0) *)
  intros n [H | [H | []]]. 
  -                        (* n : nat
                              H : 2 = n
                              ============================
                              exists n' : nat, n = n' + (n' + 0) *)
    exists 1.                   (* n = 1 + (1 + 0) *)
    rewrite <- H.           (* 2 = 1 + (1 + 0) *)
    reflexivity.
  -                        (* n : nat
                              H : 4 = n
                              ============================
                              exists n' : nat, n = n' + (n' + 0) *)
    exists 2.                   (* n = 2 + (2 + 0) *)
    rewrite <- H.           (* 4 = 2 + (2 + 0) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso del patrón vacóp para descartar el último caso.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 3.2. Demostrar que
      forall (A B : Type) (f : A -> B) (xs : list A) (x : A),
        En x xs ->
        En (f x) (map f xs).
   ------------------------------------------------------------------ *)


Lemma En_map: forall (A B : Type) (f : A -> B) (xs : list A) (x : A),
    En x xs ->
    En (f x) (map f xs).
Proof.
  intros A B f xs x.            (* A : Type
                                   B : Type
                                   f : A -> B
                                   xs : list A
                                   x : A
                                   ============================
                                   En x xs -> En (f x) (map f xs) *)
  induction xs as [|x' xs' HI]. 
  -                             (* A : Type
                                   B : Type
                                   f : A -> B
                                   x : A
                                   ============================
                                   En x [ ] -> En (f x) (map f [ ]) *)
    simpl.                      (* False -> False *)
    intros [].
  -                             (* A : Type
                                   B : Type
                                   f : A -> B
                                   x' : A
                                   xs' : list A
                                   x : A
                                   HI : En x xs' -> En (f x) (map f xs')
                                   ============================
                                   En x (x'::xs') -> 
                                   En (f x) (map f (x'::xs')) *)
    simpl.                      (* x' = x \/ En x xs' -> 
                                   f x' = f x \/ En (f x) (map f xs') *)
    intros [H | H].
    +                           (* A : Type
                                   B : Type
                                   f : A -> B
                                   x' : A
                                   xs' : list A
                                   x : A
                                   HI : En x xs' -> En (f x) (map f xs')
                                   H : x' = x
                                   ============================
                                   f x' = f x \/ En (f x) (map f xs') *)
      rewrite H.                (* f x = f x \/ En (f x) (map f xs') *)
      left.                     (* f x = f x *)
      reflexivity.
    +                           (* A : Type
                                   B : Type
                                   f : A -> B
                                   x' : A
                                   xs' : list A
                                   x : A
                                   HI : En x xs' -> En (f x) (map f xs')
                                   H : En x xs'
                                   ============================
                                   f x' = f x \/ En (f x) (map f xs') *)
      right.                    (* En (f x) (map f xs') *)
      apply HI.                 (* En x xs' *)
      apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.1. Demostrar que
      forall (A B : Type) (f : A -> B) (xs : list A) (y : B),
        En y (map f xs) <->
        exists x, f x = y /\ En x xs.
   ------------------------------------------------------------------ *)

Lemma En_map_iff: forall (A B : Type) (f : A -> B) (xs : list A) (y : B),
    En y (map f xs) <->
    exists x, f x = y /\ En x xs.
Proof.
  intros A B f xs y.                  (* A : Type
                                         B : Type
                                         f : A -> B
                                         xs : list A
                                         y : B
                                         ============================
                                         En y (map f xs) <-> 
                                         (exists x : A, f x = y /\ En x xs) *)
  induction xs as [|x xs' HI]. 
  -                                   (* A : Type
                                         B : Type
                                         f : A -> B
                                         y : B
                                         ============================
                                         En y (map f [ ]) <-> 
                                         (exists x : A, f x = y /\ En x [ ]) *)
    simpl.                            (* En y (map f [ ]) <-> 
                                         (exists x : A, f x = y /\ En x [ ]) *)
    split.
    +                                 (* A : Type
                                         B : Type
                                         f : A -> B
                                         y : B
                                         ============================
                                         False -> 
                                         exists x : A, f x = y /\ False *)
      intros [].
    +                                 (* A : Type
                                         B : Type
                                         f : A -> B
                                         y : B
                                         ============================
                                         (exists x : A, f x = y /\ False) -> 
                                         False *)
      intros [a [H []]].
  -                                   (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         ============================
                                         En y (map f (x :: xs')) <-> 
                                         (exists x0 : A, 
                                           f x0 = y /\ En x0 (x :: xs')) *)
    simpl.                            (* f x = y \/ En y (map f xs') <->
                                         (exists x0 : A, 
                                           f x0 = y /\ (x = x0 \/ En x0 xs')) *)
    split.
    +                                 (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         ============================
                                         f x = y \/ En y (map f xs') ->
                                         exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs') *)
      intros [H1 | H2].
      *                               (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         H1 : f x = y
                                         ============================
                                         exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs') *)
        exists x.                        (* f x = y /\ (x = x \/ En x xs') *)
        split.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         H1 : f x = y
                                         ============================
                                         f x = y *)
          apply H1.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         H1 : f x = y
                                         ============================
                                         x = x \/ En x xs' *)
          left.                       (* x = x *)
          reflexivity.
      *                               (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         H2 : En y (map f xs')
                                         ============================
                                         exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs') *)
        apply HI in H2.               (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         H2 : exists x : A, f x = y /\ En x xs'
                                         ============================
                                         exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs') *)
        destruct H2 as [a [Ha1 Ha2]]. (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha2 : En a xs'
                                         ============================
                                         exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs') *)
        
        exists a.                          (* En y (map f xs) <-> 
                                         (exists x : A, f x = y /\ En x xs) *)
        split.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha2 : En a xs'
                                         ============================
                                         f a = y *)
          apply Ha1.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha2 : En a xs'
                                         ============================
                                         x = a \/ En a xs' *)
          right.                      (* En a xs' *)
          apply Ha2.
    +                                 (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x : A, 
                                                f x = y /\ En x xs')
                                         ============================
                                         (exists x0 : A, 
                                          f x0 = y /\ (x = x0 \/ En x0 xs')) ->
                                         f x = y \/ En y (map f xs') *)
      intros [a [Ha1 [Ha2 | Ha3]]].
      *                               (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha2 : x = a
                                         ============================
                                         f x = y \/ En y (map f xs') *)
        left.                         (* f x = y *)
        rewrite Ha2.                  (* f a = y *)
        rewrite Ha1.                  (* y = y *)
        reflexivity.
      *                               (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha3 : En a xs'
                                         ============================
                                         f x = y \/ En y (map f xs') *)
        right.                        (* En y (map f xs') *)
        apply HI.                     (* exists x0 : A, f x0 = y /\ En x0 xs' *)
        exists a.                          (* f a = y /\ En a xs' *)
        split.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha3 : En a xs'
                                         ============================
                                         f a = y *)
          apply Ha1.
        --                            (* A : Type
                                         B : Type
                                         f : A -> B
                                         x : A
                                         xs' : list A
                                         y : B
                                         HI : En y (map f xs') <-> 
                                              (exists x:A, f x = y /\ En x xs')
                                         a : A
                                         Ha1 : f a = y
                                         Ha3 : En a xs'
                                         ============================
                                         En a xs' *)
          apply Ha3.
Qed.

(** **** Exercise: 2 stars (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  En a (l++l') <-> En a l \/ En a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, recommended (All)  *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma All_En :
  forall T (P : T -> Prop) (l : list T),
    (forall x, En x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* =====================================================================
   § 4. Aplicando teoremas a argumentos 
   ================================================================== *)

(** One feature of Coq that distinguishes it from many other proof
    assistants is that it treats _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** Coq prints the _statement_ of the [plus_comm] theorem in the same
    way that it prints the _type_ of any term that we ask it to
    [Check].  Why? *)

(** The reason is that the identifier [plus_comm] actually refers to a
    _proof object_ -- a data structure that represents a logical
    derivation establishing of the truth of the statement [forall n m
    : nat, n + m = m + n].  The type of this object _is_ the statement
    of the theorem that it is a proof of. *)

(** Intuitively, this makes sense because the statement of a theorem
    tells us what we can use that theorem for, just as the type of a
    computational object tells us what we can do with that object --
    e.g., if we have a term of type [nat -> nat -> nat], we can give
    it two [nat]s as arguments and get a [nat] back.  Similarly, if we
    have an object of type [n = m -> n + n = m + m] and we provide it
    an "argument" of type [n = m], we can derive [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

(** One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    En n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (conj_e1 _ _ (En_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples of the idioms from this section in
    later chapters. *)

(* =====================================================================
   § 5. Coq vs. teoría de conjuntos 
   ================================================================== *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, but these are, by and large, quite natural and easy to
    work with.  For example, instead of saying that a natural number
    [n] belongs to the set of even numbers, we would say in Coq that
    [ev n] holds, where [ev : nat -> Prop] is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. *)

(* =====================================================================
   §§ 5.1. Extensionalidad funcional
   ================================================================== *)

(** The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** Informally speaking, an "extensional property" is one that
    pertains to an object's observable behavior.  Thus, functional
    extensionality simply means that a function's identity is
    completely determined by what we can observe from it -- i.e., in
    Coq terms, the results we obtain after applying it. *)

(** Functional extensionality is not part of Coq's basic axioms.  This
    means that some "reasonable" propositions are not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, we can add functional extensionality to Coq's core logic
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it _inconsistent_ -- that is, they may
    make it possible to prove every proposition, including [False]!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work is generally required to establish the
    consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command.  *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 4 stars (tr_rev_correct)  *)
(** One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that the two definitions are indeed equivalent. *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
(** [] *)

(* =====================================================================
   §§ 5.2. Proposiciones y booleanos  
   ================================================================== *)

(** We've seen two different ways of encoding logical facts in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    For instance, to claim that a number [n] is even, we can say
    either
       - (1) that [evenb n] returns [true], or
       - (2) that there exists some [k] such that [n = double k].
             Indeed, these two notions of evenness are equivalent, as
             can easily be shown with a couple of auxiliary lemmas.

    Of course, it would be very strange if these two characterizations
    of evenness did not describe the same set of natural numbers!
    Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** In view of this theorem, we say that the boolean
    computation [evenb n] _reflects_ the logical proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either (1) that [beq_nat n m] returns [true] or (2) that [n =
    m].  Again, these two notions are equivalent. *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** However, even when the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, they need
    not be equivalent _operationally_.

    Equality provides an extreme example: knowing that [beq_nat n m =
    true] is generally of little direct help in the middle of a proof
    involving [n] and [m]; however, if we convert the statement to the
    equivalent form [n = m], we can rewrite with it. *)

(** The case of even numbers is also interesting.  Recall that,
    when proving the backwards direction of [even_bool_prop] (i.e.,
    [evenb_double], going from the propositional to the boolean
    claim), we used a simple induction on [k].  On the other hand, the
    converse (the [evenb_double_conv] exercise) required a clever
    generalization, since we can't directly prove [(exists k, n =
    double k) -> evenb n = true]. *)

(** For these examples, the propositional claims are more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    elements of [bool] (or some other inductive type with two
    elements).  The reason for this error message has to do with the
    _computational_ nature of Coq's core language, which is designed
    so that every function that it can express is computable and
    total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence,
    [Prop] in Coq does _not_ have a universal case analysis operation
    telling whether any given proposition is true or false, since such
    an operation would allow us to write non-computable functions.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many
    _computable_ properties are easier to express using [Prop] than
    [bool], since recursive function definitions are subject to
    significant restrictions in Coq.  For instance, the next chapter
    shows how to define the property that a regular expression matches
    a given string using [Prop].  Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand, and harder to reason
    about.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by
    reflection_.  Consider the following statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)

Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof size in this
    case, larger proofs can often be made considerably simpler by the
    use of reflection.  As an extreme example, the Coq proof of the
    famous _4-color theorem_ uses reflection to reduce the analysis of
    hundreds of different cases to a boolean computation.  We won't
    cover reflection in great detail, but it serves as a good example
    showing the complementary strengths of booleans and general
    propositions. *)

(** **** Exercise: 2 stars (logical_connectives)  *)
(** The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** Are there any important properties of the function [forallb] which
    are not captured by this specification? *)

(* FILL IN HERE *)
(** [] *)

(* =====================================================================
   §§ 5.3. Lógica clásica vs. constructiva  
   ================================================================== *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of
    [~ ~ (exists x, P x)].  Allowing ourselves to remove double
    negations from arbitrary statements is equivalent to assuming the
    excluded middle, as shown in one of the exercises below.  Thus,
    this line of reasoning cannot be encoded in Coq without assuming
    additional axioms. *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    we cannot prove the negation of such an axiom.  If we could, we
    would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)] (since [P]
    implies [~ ~ P], by the exercise below), which would be a
    contradiction.  But since we can't, it is safe to add [P \/ ~P] as
    an axiom. *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)  *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [paraTodo_no_existe_no] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, optional (classical_axioms)  *)
(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition doble_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
(** [] *)

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Logic in Coq" de Peirce et als. http://bit.ly/2nv1T9Z *)
