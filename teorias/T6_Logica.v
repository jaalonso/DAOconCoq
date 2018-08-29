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
   Nota. Uso del patrón vacío para descartar el último caso.
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

(* ---------------------------------------------------------------------
   Ejercicio 3.2. Demostrar que
      forall A (xs ys : list A) (a : A),
        En a (xs ++ ys) <-> En a xs \/ En a ys.
   ------------------------------------------------------------------ *)

Lemma En_conc_1: forall A (xs ys : list A) (a : A),
  En a (xs ++ ys) -> En a xs \/ En a ys.
Proof.
  induction xs as [|x xs' HI].    
  -                               (* A : Type
                                     ============================
                                     forall (ys : list A) (a : A), 
                                      En a ([ ] ++ ys) -> En a [ ] \/ En a ys *)
    simpl.                        (* forall (ys : list A) (a : A), 
                                      En a ys -> False \/ En a ys *)
    intros ys a H.                (* A : Type
                                     ys : list A
                                     a : A
                                     H : En a ys
                                     ============================
                                     False \/ En a ys *)
    right.                        (* En a ys *)
    apply H.
  -                               (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a (xs' ++ ys) -> 
                                           En a xs' \/ En a ys
                                     ============================
                                     forall (ys : list A) (a : A),
                                      En a ((x :: xs') ++ ys) -> 
                                      En a (x :: xs') \/ En a ys *)
    simpl.                        (* forall (ys : list A) (a : A),
                                      x = a \/ En a (xs' ++ ys) -> 
                                      (x = a \/ En a xs') \/ En a ys *)
    intros ys a [H1 | H2].
    +                             (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a (xs' ++ ys) -> 
                                           En a xs' \/ En a ys
                                     ys : list A
                                     a : A
                                     H1 : x = a
                                     ============================
                                     (x = a \/ En a xs') \/ En a ys *)
      left.                       (* x = a \/ En a xs' *)
      left.                       (* x = a *)
      apply H1.
    +                             (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a (xs' ++ ys) -> 
                                           En a xs' \/ En a ys
                                     ys : list A
                                     a : A
                                     H2 : En a (xs' ++ ys)
                                     ============================
                                     (x = a \/ En a xs') \/ En a ys *)
      rewrite <- disy_asociativa.  (* x = a \/ (En a xs' \/ En a ys) *)
      right.                      (* En a xs' \/ En a ys *)
      apply HI.                   (* En a (xs' ++ ys) *)
      apply H2.
Qed.

Lemma En_conc_2: forall A (xs ys : list A) (a : A),
  En a xs \/ En a ys -> En a (xs ++ ys). 
Proof.
  induction xs as [|x xs' HI]. 
  -                               (* A : Type
                                     ============================
                                     forall (ys : list A) (a : A), 
                                      En a [ ] \/ En a ys -> En a ([ ] ++ ys) *)
    simpl.                        (* forall (ys : list A) (a : A), 
                                      False \/ En a ys -> En a ys *)
    intros ys a [[] | H].         (* A : Type
                                     ys : list A
                                     a : A
                                     H : En a ys
                                     ============================
                                     En a ys *)
    apply H.
  -                               (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a xs' \/ En a ys -> 
                                           En a (xs' ++ ys)
                                     ============================
                                     forall (ys : list A) (a : A),
                                      En a (x :: xs') \/ En a ys -> 
                                      En a ((x :: xs') ++ ys) *)
    simpl.                        (* forall (ys : list A) (a : A),
                                      (x = a \/ En a xs') \/ En a ys -> 
                                      x = a \/ En a (xs' ++ ys) *)
    intros ys a [[H1 | H2] | H3]. 
    +                             (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a xs' \/ En a ys -> 
                                           En a (xs' ++ ys)
                                     ys : list A
                                     a : A
                                     H1 : x = a
                                     ============================
                                     x = a \/ En a (xs' ++ ys) *)
      left.                       (* x = a *)
      apply H1.
    +                             (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a xs' \/ En a ys -> 
                                           En a (xs' ++ ys)
                                     ys : list A
                                     a : A
                                     H2 : En a xs'
                                     ============================
                                     x = a \/ En a (xs' ++ ys) *)
      right.                      (* En a (xs' ++ ys) *)
      apply HI.                   (* En a xs' \/ En a ys *)
      left.                       (* En a xs' *)
      apply H2.
    +                             (* A : Type
                                     x : A
                                     xs' : list A
                                     HI : forall (ys : list A) (a : A), 
                                           En a xs' \/ En a ys -> 
                                           En a (xs' ++ ys)
                                     ys : list A
                                     a : A
                                     H3 : En a ys
                                     ============================
                                     x = a \/ En a (xs' ++ ys) *)
      right.                      (* En a (xs' ++ ys) *)
      apply HI.                   (* En a xs' \/ En a ys *)
      right.                      (* En a ys *)
      apply H3.
Qed.    

Lemma En_conc: forall A (xs ys : list A) (a : A),
  En a (xs ++ ys) <-> En a xs \/ En a ys.
Proof.
  split.
  -                  (* A : Type
                        xs, ys : list A
                                     a : A
                                     ============================
                                     En a (xs ++ ys) -> En a xs \/ En a ys *)
    apply En_conc_1. 
  -                  (* A : Type
                                     xs, ys : list A
                                     a : A
                                     ============================
                                     En a xs \/ En a ys -> En a (xs ++ ys) *)
    apply En_conc_2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.1. Definir la propiedad
      Todos {T : Type} (P : T -> Prop) (xs : list T) : Prop
   tal que (Todos P xs) se verifica si todos los elementos de xs cumplen
   la propiedad P.
   ------------------------------------------------------------------ *)

Fixpoint Todos {T : Type} (P : T -> Prop) (xs : list T) : Prop :=
  match xs with
  | nil      => True
  | x :: xs' => P x /\ Todos P xs' 
  end.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.2. Demostrar que
      forall T (P : T -> Prop) (xs : list T),
        (forall x, En x xs -> P x) <->
        Todos P xs.
   ------------------------------------------------------------------ *)

Lemma Todos_En_1: 
  forall T (P : T -> Prop) (xs : list T),
    (forall x, En x xs -> P x) ->
    Todos P xs.
Proof.
  induction xs as [|x' xs' HI].  
  -                             (* T : Type
                                   P : T -> Prop
                                   ============================
                                   (forall x : T, En x [ ] -> P x) -> 
                                   Todos P [ ] *) 
    simpl.                      (* (forall x : T, False -> P x) -> True *)
    intros.                     (* T : Type
                                   P : T -> Prop
                                   H : forall x : T, False -> P x
                                   ============================
                                   True *)
    apply I.
  -                             (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : (forall x : T, En x xs' -> P x) -> 
                                        Todos P xs'
                                   ============================
                                   (forall x : T, En x (x' :: xs') -> P x) -> 
                                   Todos P (x' :: xs') *)
    simpl.                      (* (forall x : T, x' = x \/ En x xs' -> P x) ->
                                   P x' /\ Todos P xs' *)
    intros H.                   (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : (forall x : T, En x xs' -> P x) -> 
                                        Todos P xs'
                                   H : forall x : T, x' = x \/ En x xs' -> P x
                                   ============================
                                   P x' /\ Todos P xs' *)
    split.
    +                           (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : (forall x : T, En x xs' -> P x) -> 
                                        Todos P xs'
                                   H : forall x : T, x' = x \/ En x xs' -> P x
                                   ============================
                                   P x' *)
      apply H.                  (* x' = x' \/ En x' xs' *)
      left.                     (* x' = x' *)
      reflexivity.
    +                           (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : (forall x : T, En x xs' -> P x) -> 
                                        Todos P xs'
                                   H : forall x : T, x' = x \/ En x xs' -> P x
                                   ============================
                                   Todos P xs' *)
      apply HI.                 (* forall x : T, En x xs' -> P x *)
      intros x H1.              (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : (forall x : T, En x xs' -> P x) -> 
                                        Todos P xs'
                                   H : forall x : T, x' = x \/ En x xs' -> P x
                                   x : T
                                   H1 : En x xs'
                                   ============================
                                   P x *)
      apply H.                  (* x' = x \/ En x xs' *)
      right.                    (* En x xs' *)
      apply H1.
Qed.

Lemma Todos_En_2: 
  forall T (P : T -> Prop) (xs : list T),
    Todos P xs ->
    (forall x, En x xs -> P x).
Proof.
  induction xs as [|x' xs' HI]. 
  -                             (* T : Type
                                   P : T -> Prop
                                   ============================
                                   Todos P [ ] -> 
                                   forall x : T, En x [ ] -> P x *)
    simpl.                      (* True -> forall x : T, False -> P x *)
    intros [].                  (* T : Type
                                   P : T -> Prop
                                   ============================
                                   forall x : T, False -> P x *)
    intros x [].
  -                             (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : Todos P xs' -> 
                                        forall x : T, En x xs' -> P x
                                   ============================
                                   Todos P (x' :: xs') -> 
                                   forall x : T, En x (x' :: xs') -> P x *)
    simpl.                      (* P x' /\ Todos P xs' -> 
                                   forall x : T, x' = x \/ En x xs' -> P x *)
    intros [H1 H2] x [H3 | H4]. 
    +                           (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : Todos P xs' -> 
                                        forall x : T, En x xs' -> P x
                                   H1 : P x'
                                   H2 : Todos P xs'
                                   x : T
                                   H3 : x' = x
                                   ============================
                                   P x *)
      rewrite <- H3.             (* P x' *)
      apply H1.
    +                           (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : Todos P xs' -> 
                                        forall x : T, En x xs' -> P x
                                   H1 : P x'
                                   H2 : Todos P xs'
                                   x : T
                                   H4 : En x xs'
                                   ============================
                                   P x *)
      apply HI.
      *                         (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : Todos P xs' -> 
                                        forall x : T, En x xs' -> P x
                                   H1 : P x'
                                   H2 : Todos P xs'
                                   x : T
                                   H4 : En x xs'
                                   ============================
                                   Todos P xs' *)
        apply H2.
      *                         (* T : Type
                                   P : T -> Prop
                                   x' : T
                                   xs' : list T
                                   HI : Todos P xs' -> 
                                        forall x : T, En x xs' -> P x
                                   H1 : P x'
                                   H2 : Todos P xs'
                                   x : T
                                   H4 : En x xs'
                                   ============================
                                   En x xs' *)
        apply H4.
Qed.

Lemma Todos_En: 
  forall T (P : T -> Prop) (xs : list T),
    (forall x, En x xs -> P x) <->
    Todos P xs.
Proof.
  split.
  -                   (* T : Type
                         P : T -> Prop
                         xs : list T
                         ============================
                         (forall x : T, En x xs -> P x) -> Todos P xs *)
    apply Todos_En_1. 
  -                   (* T : Type
                         P : T -> Prop
                         xs : list T
                         ============================
                         Todos P xs -> forall x : T, En x xs -> P x *)
    apply Todos_En_2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.1. Definir la propiedad
      combina_par_impar (Pimpar Ppar : nat -> Prop) : nat -> Prop
   tal que (combina_par_impar Pimpar Ppar) es una función que asigna a n
   (Pimpar n) si n es impar y (Ppar n) si n es par.
   ------------------------------------------------------------------ *)

Definition combina_par_impar (Pimpar Ppar : nat -> Prop) : nat -> Prop :=
  fun n => (esImpar n = true -> Pimpar n) /\
        (esImpar n = false -> Ppar n).

(* ---------------------------------------------------------------------
   Ejercicio 3.4.2. Demostrar que
      forall (Pimpar Ppar : nat -> Prop) (n : nat),
        (esImpar n = true -> Pimpar n) ->
        (esImpar n = false -> Ppar n) ->
        combina_par_impar Pimpar Ppar n.
   ------------------------------------------------------------------ *)

Theorem combina_par_impar_intro :
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    (esImpar n = true -> Pimpar n) ->
    (esImpar n = false -> Ppar n) ->
    combina_par_impar Pimpar Ppar n.
Proof.
  intros Pimpar Par n H1 H2. (* Pimpar, Par : nat -> Prop
                                n : nat
                                H1 : esImpar n = true -> Pimpar n
                                H2 : esImpar n = false -> Par n
                                ============================
                                combina_par_impar Pimpar Par n *)
  unfold combina_par_impar.  (* (esImpar n = true -> Pimpar n) /\ 
                                (esImpar n = false -> Par n) *)
  split.
  -                          (* Pimpar, Par : nat -> Prop
                                n : nat
                                H1 : esImpar n = true -> Pimpar n
                                H2 : esImpar n = false -> Par n
                                ============================
                                esImpar n = true -> Pimpar n *)
    apply H1.
  -                          (* Pimpar, Par : nat -> Prop
                                n : nat
                                H1 : esImpar n = true -> Pimpar n
                                H2 : esImpar n = false -> Par n
                                ============================
                                esImpar n = false -> Par n *)
    apply H2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.3. Demostrar que
      forall (Pimpar Ppar : nat -> Prop) (n : nat),
        combina_par_impar Pimpar Ppar n ->
        esImpar n = true ->
        Pimpar n.
   ------------------------------------------------------------------ *)

Theorem combina_par_impar_elim_impar:
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    combina_par_impar Pimpar Ppar n ->
    esImpar n = true ->
    Pimpar n.
Proof.
  intros Pimpar Ppar n H1 H2.     (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H1 : combina_par_impar Pimpar Ppar n
                                     H2 : esImpar n = true
                                     ============================
                                    Pimpar n *)
  unfold combina_par_impar in H1. (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H1 : (esImpar n = true -> Pimpar n) /\ 
                                          (esImpar n = false -> Ppar n)
                                     H2 : esImpar n = true
                                     ============================
                                     Pimpar n *)
  destruct H1 as [H3 H4].         (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H3 : esImpar n = true -> Pimpar n
                                     H4 : esImpar n = false -> Ppar n
                                     H2 : esImpar n = true
                                     ============================
                                     Pimpar n *)
  apply H3.                       (* esImpar n = true *)
  apply H2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.4. Demostrar que
      forall (Pimpar Ppar : nat -> Prop) (n : nat),
        combina_par_impar Pimpar Ppar n ->
        esImpar n = false ->
        Ppar n.
   ------------------------------------------------------------------ *)

Theorem combina_par_impar_elim_par:
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    combina_par_impar Pimpar Ppar n ->
    esImpar n = false ->
    Ppar n.
Proof.
  intros Pimpar Ppar n H1 H2.     (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H1 : combina_par_impar Pimpar Ppar n
                                     H2 : esImpar n = false
                                     ============================
                                     Ppar n *)
  unfold combina_par_impar in H1. (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H1 : (esImpar n = true -> Pimpar n) /\ 
                                          (esImpar n = false -> Ppar n)
                                     H2 : esImpar n = false
                                     ============================
                                     Ppar n *)
  destruct H1 as [H3 H4].         (* Pimpar, Ppar : nat -> Prop
                                     n : nat
                                     H3 : esImpar n = true -> Pimpar n
                                     H4 : esImpar n = false -> Ppar n
                                     H2 : esImpar n = false
                                     ============================
                                     Ppar n *)
  apply H4.                       (* esImpar n = false *)
  apply H2.
Qed.

(* =====================================================================
   § 4. Aplicando teoremas a argumentos 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1. Evaluar la expresión
      Check suma_conmutativa.
   ------------------------------------------------------------------ *)

Check suma_conmutativa.
(* ===> forall n m : nat, n + m = m + n *)

(* ---------------------------------------------------------------------
   Notas.
   1. En Coq, las demostraciones son objetos de primera clase.
   2. Coq devuelve el tipo de suma_conmutativa como el de cualquier
      expresión.
   3. El identificador suma_conmutativa representa un objeto prueba de
      (forall n m : nat, n + m = m + n).
   4. Un término de tipo (nat -> nat -> nat) transforma dos naturales en
      un natural.
   5. Análogamente, un término de tipo (n = m -> n + n = m + m)
      transforma un argumento de tipo (n = m) en otro de tipo 
      (n + n = m + m).
   ------------------------------------------------------------------ *)




(** Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

(* ---------------------------------------------------------------------
   Ejemplo 4.2. Demostrar que
      forall x y z : nat, 
        x + (y + z) = (z + y) + x.
   ------------------------------------------------------------------ *)

(* 1º intento *)
Lemma suma_conmutativa3a :
  forall x y z : nat,
    x + (y + z) = (z + y) + x.
Proof.
  intros x y z.             (* x, y, z : nat
                               ============================
                               x + (y + z) = (z + y) + x *)
  rewrite suma_conmutativa. (* (y + z) + x = (z + y) + x *)
  rewrite suma_conmutativa. (* x + (y + z) = (z + y) + x *)
Abort.

(* 2º intento *)
Lemma suma_conmutativa3b :
  forall x y z,
    x + (y + z) = (z + y) + x.
Proof.
  intros x y z.               (* x, y, z : nat
                                 ============================
                                 x + (y + z) = z + y + x *)
  rewrite suma_conmutativa.   (* (y + z) + x = (z + y) + x *)
  assert (H : y + z = z + y). 
  -                           (* x, y, z : nat
                                 ============================
                                 y + z = z + y *)
    rewrite suma_conmutativa. (* z + y = z + y *)
    reflexivity. 
  -                           (* x, y, z : nat
                                 H : y + z = z + y
                                 ============================
                                 (y + z) + x = (z + y) + x *)
    rewrite H.                (* (z + y) + x = (z + y) + x *)
    reflexivity.
Qed.

(* 3º intento *)
Lemma suma_conmutativa3c:
  forall x y z,
    x + (y + z) = (z + y) + x.
Proof.
  intros x y z.                   (* x, y, z : nat
                                     ============================
                                     x + (y + z) = (z + y) + x *)
  rewrite suma_conmutativa.       (* (y + z) + x = (z + y) + x *)
  rewrite (suma_conmutativa y z). (* (z + y) + x = (z + y) + x *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Indicación en (rewrite (suma_conmutativa y z)) de los
   argumentos con los que se aplica, análogamente a las funciones
   polimórficas. 
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 4.3. Demostrar que
     forall {n : nat} {ns : list nat},
       En n (map (fun m => m * 0) ns) ->
       n = 0.
   ------------------------------------------------------------------ *)

(* Lema auxiliar *)
Lemma producto_n_0:
  forall n : nat, n * 0 = 0.
Proof.
  induction n as [|n' HI]. 
  -                        (* 
                              ============================
                              0 * 0 = 0 *)
    reflexivity. 
  -                        (* n' : nat
                              HI : n' * 0 = 0
                              ============================
                              S n' * 0 = 0 *)
    simpl.                 (* n' * 0 = 0 *)
    apply HI.
Qed.

(* 1ª demostración *)
Example ej_aplicacion_de_lema_1:
  forall {n : nat} {ns : list nat},
    En n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.              (* n : nat
                                 ns : list nat
                                 H : En n (map (fun m : nat => m * 0) ns)
                                 ============================
                                 n = 0 *)
  rewrite En_map_iff in H.    (* n : nat
                                 ns : list nat
                                 H : exists x : nat, x * 0 = n /\ En x ns
                                 ============================
                                 n = 0 *)
  destruct H as [m [Hm _]].   (* n : nat
                                 ns : list nat
                                 m : nat
                                 Hm : m * 0 = n
                                 ============================
                                 n = 0 *)
  rewrite producto_n_0 in Hm. (* n : nat
                                 ns : list nat
                                 m : nat
                                 Hm : 0 = n
                                 ============================
                                 n = 0 *)
  symmetry.                   (* 0 = n *)
  apply Hm.
Qed.

(* 2ª demostración *)
Example ej_aplicacion_de_lema:
  forall {n : nat} {ns : list nat},
    En n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.                    (* n : nat
                                       ns : list nat
                                       H : En n (map (fun m : nat => m * 0) ns)
                                       ============================
                                       n = 0 *)
  destruct (conj_e1 _ _
             (En_map_iff _ _ _ _ _) 
             H)
           as [m [Hm _]].           (* n : nat
                                       ns : list nat
                                       H : En n (map (fun m : nat => m * 0) ns)
                                       m : nat
                                       Hm : m * 0 = n
                                       ============================
                                       n = 0 *)
  rewrite producto_n_0 in Hm.       (* n : nat
                                       ns : list nat
                                       H : En n (map (fun m : nat => m * 0) ns)
                                       m : nat
                                       Hm : 0 = n
                                       ============================
                                       n = 0 *)
  symmetry.                         (* 0 = n *)
  apply Hm.
Qed.

(* ---------------------------------------------------------------------
   Nota. Aplicación de teoremas a argumentos con
      (conj_e1 _ _  (En_map_iff _ _ _ _ _) H)
   ------------------------------------------------------------------ *)

(* =====================================================================
   § 5. Coq vs. teoría de conjuntos 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Notas.
   1. En lugar de decir que un elemento pertenece a un conjunto se puede
      decir que verifica la propiedad que define al conjunto.
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 5.1. Extensionalidad funcional
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.1.1. Demostrar que
      plus 3 = plus (pred 4).
   ------------------------------------------------------------------ *)

Example igualdad_de_funciones_ej1:
  suma 3 = suma (pred 4).
Proof.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.1.2. Definir el axioma de extensionalidad funcional que
   afirma que dos funciones son giuales cuando tienen los mismos
   valores. 
   ------------------------------------------------------------------ *)

Axiom extensionalidad_funcional : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(* ---------------------------------------------------------------------
   Ejemplo 5.1.3. Demostrar que
      (fun x => suma x 1) = (fun x => suma 1 x).
   ------------------------------------------------------------------ *)

Example igualdad_de_funciones_ej2 :
  (fun x => suma x 1) = (fun x => suma 1 x).
Proof.
  apply extensionalidad_funcional. (* 
                                      ============================
                                      forall x : nat, suma x 1 = suma 1 x *)
  intros x.                        (* x : nat
                                      ============================
                                      suma x 1 = suma 1 x *)
  apply suma_conmutativa.
Qed.

(* ---------------------------------------------------------------------
   Notas.
   1. No se puede demostrar sin el axioma.
   2. Hay que ser cuidadoso en la definición de axiomas, porque se
      pueden introducir inconsistencias. 
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 5.1.4. Calcular los axiomas usados en la prueba de 
      igualdad_de_funciones_ej2
   ------------------------------------------------------------------ *)

Print Assumptions igualdad_de_funciones_ej2.
(* ===>
     Axioms:
     extensionalidad_funcional :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(* ---------------------------------------------------------------------
   Ejercicio 5.1.1. Se considera la siguiente definición iterativa de la
   función inversa
      Fixpoint inversaIaux {X} (xs ys : list X) : list X :=
        match xs with
        | []       => ys
        | x :: xs' => inversaIaux xs' (x :: ys)
        end.
      
      Definition inversaI {X} (xs : list X) : list X :=
        inversaIaux xs [].

   Demostrar que 
      forall X : Type, 
        @inversaI X = @inversa X.
   ------------------------------------------------------------------ *)

Fixpoint inversaIaux {X} (xs ys : list X) : list X :=
  match xs with
  | []       => ys
  | x :: xs' => inversaIaux xs' (x :: ys)
  end.

Definition inversaI {X} (xs : list X) : list X :=
  inversaIaux xs [].

Lemma inversaI_correcta_aux:
  forall (X : Type) (xs ys : list X),
    inversaIaux xs ys = inversa xs ++ ys.
Proof.
  intros X xs.                  (* X : Type
                                   xs : list X
                                   ============================
                                   forall ys : list X, 
                                    inversaIaux xs ys = inversa xs ++ ys *)
  induction xs as [|x xs' HI].  
  -                             (* X : Type
                                   ============================
                                   forall ys : list X, 
                                    inversaIaux [ ] ys = inversa [ ] ++ ys *)
    simpl.                      (* forall ys : list X, ys = ys *)
    intros.                     (* X : Type
                                   ys : list X
                                   ============================
                                   ys = ys *)
    reflexivity.
  -                             (* X : Type
                                   x : X
                                   xs' : list X
                                   HI : forall ys : list X, 
                                         inversaIaux xs' ys = inversa xs' ++ ys
                                   ============================
                                   forall ys : list X, 
                                    inversaIaux (x :: xs') ys = 
                                    inversa (x :: xs') ++ ys *)
    intros ys.                  (* X : Type
                                   x : X
                                   xs' : list X
                                   HI : forall ys : list X, 
                                         inversaIaux xs' ys = inversa xs' ++ ys
                                   ys : list X
                                   ============================
                                   inversaIaux (x :: xs') ys = 
                                   inversa (x :: xs') ++ ys *)
    simpl.                      (* inversaIaux xs' (x :: ys) = 
                                   (inversa xs' ++ [x]) ++ ys *)
    rewrite <- conc_asociativa.  (* inversaIaux xs' (x :: ys) = 
                                   inversa xs' ++ ([x] ++ ys) *)
    apply HI.
Qed.
                                            
Lemma inversaI_correcta:
  forall X : Type,
    @inversaI X = @inversa X.
Proof.
  intros X.                        (* X : Type
                                      ============================
                                      inversaI = inversa *)
  apply extensionalidad_funcional. (* forall x : list X, 
                                       inversaI x = inversa x *)
  intros.                          (* X : Type
                                      x : list X
                                      ============================
                                      inversaI x = inversa x *)
  unfold inversaI.                 (* inversaIaux x [ ] = inversa x *)
  rewrite inversaI_correcta_aux.   (* inversa x ++ [ ] = inversa x *)
  apply conc_nil.
Qed.

  
(* =====================================================================
   §§ 5.2. Proposiciones y booleanos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.2.1. Demostrar que
     forall k : nat,
       esPar (doble k) = true.
   ------------------------------------------------------------------ *)

Theorem esPar_doble:
  forall k : nat,
    esPar (doble k) = true.
Proof.
  intros k.                (* k : nat
                              ============================
                              esPar (doble k) = true *)
  induction k as [|k' HI]. 
  -                        (* 
                              ============================
                              esPar (doble 0) = true *)
    reflexivity.
  -                        (* k' : nat
                              HI : esPar (doble k') = true
                              ============================
                              esPar (doble (S k')) = true *)
    simpl.                 (* esPar (doble k') = true *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2.1. Demostrar que
      forall n : nat,
        exists k : nat, n = if esPar n
                     then doble k
                     else S (doble k).
   ------------------------------------------------------------------ *)

Theorem esPar_doble_aux :
  forall n : nat,
    exists k : nat, n = if esPar n
                 then doble k
                 else S (doble k).
Proof.
  induction n as [|n' HI].    
  -                            (* 
                                  ============================
                                  exists k : nat, 
                                   0 = (if esPar 0 
                                        then doble k 
                                        else S (doble k)) *)
    exists 0.                       (* 0 = (if esPar 0 
                                       then doble 0 
                                       else S (doble 0)) *)
    reflexivity.
  -                            (* n' : nat
                                  HI : exists k : nat, 
                                        n' = (if esPar n' 
                                              then doble k 
                                              else S (doble k))
                                  ============================
                                  exists k : nat, 
                                   S n' = (if esPar (S n') 
                                           then doble k 
                                           else S (doble k)) *)
    destruct (esPar n') eqn:H. 
    +                          (* n' : nat
                                  H : esPar n' = true
                                  HI : exists k : nat, n' = doble k
                                  ============================
                                  exists k : nat, 
                                   S n' = (if esPar (S n') 
                                           then doble k 
                                           else S (doble k)) *)
      rewrite esPar_S.         (* exists k : nat,
                                   S n' = (if negacion (esPar n') 
                                           then doble k 
                                           else S (doble k)) *)
      rewrite H.               (* exists k : nat, 
                                   S n' = (if negacion true 
                                           then doble k 
                                           else S (doble k)) *)
      simpl.                   (* exists k : nat, S n' = S (doble k) *)
      destruct HI as [k' Hk']. (* n' : nat
                                  H : esPar n' = true
                                  k' : nat
                                  Hk' : n' = doble k'
                                  ============================
                                  exists k : nat, S n' = S (doble k) *)
      exists k'.                    (* S n' = S (doble k') *)
      rewrite Hk'.             (* S (doble k') = S (doble k') *)
      reflexivity.
    +                          (* n' : nat
                                  H : esPar n' = false
                                  HI : exists k : nat, n' = S (doble k)
                                  ============================
                                  exists k : nat, 
                                   S n' = (if esPar (S n') 
                                           then doble k 
                                           else S (doble k)) *)
      rewrite esPar_S.         (* exists k : nat,
                                   S n' = (if negacion (esPar n') 
                                           then doble k 
                                           else S (doble k)) *)
      rewrite H.               (* exists k : nat, 
                                   S n' = (if negacion false 
                                           then doble k 
                                           else S (doble k)) *)
      simpl.                   (* exists k : nat, S n' = doble k *)
      destruct HI as [k' Hk']. (* n' : nat
                                  H : esPar n' = false
                                  k' : nat
                                  Hk' : n' = S (doble k')
                                  ============================
                                  exists k : nat, S n' = doble k *)
      exists (1 + k').              (* S n' = doble (1 + k') *)
      rewrite Hk'.             (* S (S (doble k')) = doble (1 + k') *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.2. Demostrar que
      forall n : nat,
        esPar n = true <-> exists k, n = doble k.

   Es decir, que la computación booleana (esPar n) refleja la
   proposición (exists k, n = doble k).
   ------------------------------------------------------------------ *)

Theorem esPar_bool_prop:
  forall n : nat,
    esPar n = true <-> exists k, n = doble k.
Proof.
  intros n.               (* n : nat
                             ============================
                             esPar n = true <-> (exists k : nat, n = doble k) *)
  split.
  -                       (* n : nat
                             ============================
                             esPar n = true -> exists k : nat, n = doble k *)
    intros H.             (* n : nat                           
                             H : esPar n = true
                             ============================
                             exists k : nat, n = doble k *)
    destruct
      (esPar_doble_aux n) 
      as [k Hk].          (* n : nat
                             H : esPar n = true
                             k : nat
                             Hk : n = (if esPar n then doble k else S (doble k))
                             ============================
                             exists k0 : nat, n = doble k0 *)
    rewrite Hk.           (* exists k0 : nat, 
                              (if esPar n 
                               then doble k 
                               else S (doble k)) 
                              = doble k0 *)
    rewrite H.            (* exists k0 : nat, doble k = doble k0 *)
    exists k.                  (* doble k = doble k *)
    reflexivity.
  -                       (* n : nat
                             ============================
                             (exists k : nat, n = doble k) -> esPar n = true *)
    intros [k Hk].        (* n, k : nat
                             Hk : n = doble k
                             ============================
                             esPar n = true *)
    rewrite Hk.           (* esPar (doble k) = true *)
    apply esPar_doble.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.3. Demostrar que
      forall n m : nat,
        iguales_nat n m = true <-> n = m.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_bool_prop:
  forall n m : nat,
    iguales_nat n m = true <-> n = m.
Proof.
  intros n m.                 (* n, m : nat
                                 ============================
                                 iguales_nat n m = true <-> n = m *)
  split.
  -                           (* n, m : nat
                                 ============================
                                 iguales_nat n m = true -> n = m *)
    apply iguales_nat_true.
  -                           (* n, m : nat
                                 ============================
                                 n = m -> iguales_nat n m = true *)
    intros H.                 (* n, m : nat
                                 H : n = m
                                 ============================
                                 iguales_nat n m = true *)
    rewrite H.                (* iguales_nat m m = true *)
    rewrite iguales_nat_refl. (* true = true *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.4. Definir la función es_primo_par tal que 
   (es_primo_par n) es verifica si n es un primo par.
   ------------------------------------------------------------------ *)

(* 1º intento *)
Fail Definition es_primo_par n :=
  if n = 2
  then true
  else false.

(* 2º intento *)
Definition es_primo_par n :=
  if iguales_nat n 2
  then true
  else false.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.5.1. Demostrar que
      exists k : nat, 1000 = doble k.
   ------------------------------------------------------------------ *)

Example esPar_1000: exists k : nat, 1000 = doble k.
Proof.
  exists 500.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.5.2. Demostrar que
      esPar 1000 = true.
   ------------------------------------------------------------------ *)

Example esPar_1000' : esPar 1000 = true.
Proof.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.2.5.3. Demostrar que
      exists k : nat, 1000 = doble k.
   ------------------------------------------------------------------ *)

Example esPar_1000'': exists k : nat, 1000 = doble k.
Proof.
  apply esPar_bool_prop. (* esPar 1000 = true *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Notas. 
   1. En la proposicional se necesita proporcionar un testipo.
   2. En la booleano se calcula sin testigo.
   3. Se puede demostrar la proposicional usando la equivalencia con la
      booleana sin necesidad de testigo.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 5.2.2.1. Demostrar que
      forall x y : bool,
        x && y = true <-> x = true /\ y = true.
   ------------------------------------------------------------------ *)

Lemma conj_verdad_syss:
  forall x y : bool,
    x && y = true <-> x = true /\ y = true.
Proof.
  intros x y.             (* x, y : bool
                             ============================
                             x && y = true <-> x = true /\ y = true *)
  destruct x.             
  -                       (* y : bool
                             ============================
                             true && y = true <-> true = true /\ y = true *)
    destruct y.           
    +                     (* 
                             ============================
                             true && true = true <-> true = true /\ true=true *)
      simpl.              (* true = true <-> true = true /\ true = true *)
      split.              
      *                   (* 
                             ============================
                             true = true -> true = true /\ true = true *)
        apply conj_intro. (* true = true *)
        reflexivity.
      *                   (* 
                             ============================
                             true = true /\ true = true -> true = true *)
        apply conj_e1.
    +                     (* 
                             ============================
                             true && false = true <-> true=true /\ false=true *)
      simpl.              (* false = true <-> true = true /\ false = true *)
      split.
      *                   (* 
                             ============================
                             false = true -> true = true /\ false = true *)
        intros H.         (* H : false = true
                             ============================
                             true = true /\ false = true *)
        inversion H.
      *                   (* 
                             ============================
                             true = true /\ false = true -> false = true *)
        intros [H1 H2].   (* H1 : true = true
                             H2 : false = true
                             ============================
                             false = true *)
        apply H2.
  -                       (* y : bool
                             ============================
                             false && y = true <-> false = true /\ y = true *)
    split.
    +                     (* y : bool
                             ============================
                             false && y = true -> false = true /\ y = true *)
      simpl.              (* false = true -> false = true /\ y = true *)
      intros H.           (* y : bool
                             H : false = true
                             ============================
                             false = true /\ y = true *)
      inversion H.
    +                     (* y : bool
                             ============================
                             false = true /\ y = true -> false && y = true *)
      simpl.              (* false = true /\ y = true -> false = true *)
      intros [H1 H2].     (* y : bool
                             H1 : false = true
                             H2 : y = true
                             ============================
                             false = true *)
      apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2.2.2. Demostrar que
      forall x y : bool,
        x || y = true <-> x = true \/ y = true.
   ------------------------------------------------------------------ *)

Lemma disy_verdad_syss:
  forall x y : bool,
    x || y = true <-> x = true \/ y = true.
Proof.
  intros x y.           (* x, y : bool
                           ============================
                           x || y = true <-> x = true \/ y = true *)
  destruct x.
  -                     (* y : bool
                           ============================
                           true || y = true <-> true = true \/ y = true *)
    simpl.              (* true = true <-> true = true \/ y = true *)
    split.
    +                   (* y : bool
                           ============================
                           true = true -> true = true \/ y = true *)
      apply disy_intro. 
    +                   (* y : bool
                           ============================
                           true = true \/ y = true -> true = true *)
      intros.           (* y : bool
                           H : true = true \/ y = true
                           ============================
                           true = true *)
      reflexivity.
  -                     (* y : bool
                           ============================
                           false || y = true <-> false = true \/ y = true *)
    simpl.              (* y = true <-> false = true \/ y = true *)
    split.
    +                   (* y : bool
                           ============================
                           y = true -> false = true \/ y = true *)
      destruct y.
      *                 (* 
                           ============================
                           true = true -> false = true \/ true = true *)
        intros.         (* H : true = true
                           ============================
                           false = true \/ true = true *)
        right.          (* true = true *)
        reflexivity.
      *                 (* 
                           ============================
                           false = true -> false = true \/ false = true *)
        apply disy_intro.
    +                   (* y : bool
                           ============================
                           false = true \/ y = true -> y = true *)
      intros [H1 | H2].
      *                 (* y : bool
                           H1 : false = true
                           ============================
                           y = true *)
        inversion H1.
      *                 (* y : bool
                           H2 : y = true
                           ============================
                           y = true *)
        apply H2.
Qed.
        
(* ---------------------------------------------------------------------
   Ejercicio 5.2.3. Demostrar que
      forall x y : nat,
        iguales_nat x y = false <-> x <> y.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_falso_syss:
  forall x y : nat,
    iguales_nat x y = false <-> x <> y.
Proof.
  intros x y.                           (* x, y : nat
                                           ============================
                                           iguales_nat x y = false <-> x <> y *)
  destruct (iguales_nat x y) eqn:H.
  -                                     (* x, y : nat
                                           H : iguales_nat x y = true
                                           ============================
                                           true = false <-> x <> y *)
    rewrite iguales_nat_bool_prop in H. (* x, y : nat
                                           H : x = y
                                           ============================
                                           true = false <-> x <> y *)
    rewrite H.                          (* true = false <-> y <> y *)
    split.
    +                                   (* x, y : nat
                                           H : x = y
                                           ============================
                                           true = false -> y <> y *)
      intros H1.                        (* x, y : nat
                                           H : x = y
                                           H1 : true = false
                                           ============================
                                           y <> y *)
      inversion H1.
    +                                   (* x, y : nat
                                           H : x = y
                                           ============================
                                           y <> y -> true = false *)
      intros H1.                        (* x, y : nat
                                           H : x = y
                                           H1 : y <> y
                                           ============================
                                           true = false *)
      exfalso.                          (* False *)
      unfold not in H1.                 (* x, y : nat
                                           H : x = y
                                           H1 : y = y -> False
                                           ============================
                                           False *)
      apply H1.                         (* y = y *)
      apply eq_refl.
  -                                     (* x, y : nat
                                           H : iguales_nat x y = false
                                           ============================
                                           false = false <-> x <> y *)
    split.
    +                                   (* x, y : nat
                                           H : iguales_nat x y = false
                                           ============================
                                           false = false -> x <> y *)
      unfold not.                       (* false = false -> x = y -> False *)
      intros H1 H2.                     (* x, y : nat
                                           H : iguales_nat x y = false
                                           H1 : false = false
                                           H2 : x = y
                                           ============================
                                           False *)
      rewrite H2 in H.                  (* x, y : nat
                                           H : iguales_nat y y = false
                                           H1 : false = false
                                           H2 : x = y
                                           ============================
                                           False *)
      rewrite iguales_nat_refl in H.    (* x, y : nat
                                           H : true = false
                                           H1 : false = false
                                           H2 : x = y
                                           ============================
                                           False *)
      inversion H.
    +                                   (* x, y : nat
                                           H : iguales_nat x y = false
                                           ============================
                                           x <> y -> false = false *)
      intros.                           (* x, y : nat
                                           H : iguales_nat x y = false
                                           H0 : x <> y
                                           ============================
                                           false = false *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2.4.1. Definir la función 
      iguales_lista {A : Type} (i : A -> A -> bool) (xs ys : list A)
   tal que (iguales_lists xs ys) se verifica si los correspondientes
   elementos de las listas xs e ys son iguales respecto de la relación
   de igualdad i.
   ------------------------------------------------------------------ *)

Fixpoint iguales_lista {A : Type} (i : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | nil, nil            => true
  | x' ::xs', y' :: ys' => i x' y' && iguales_lista i xs' ys'
  | _, _                => false                          
  end.

(* ---------------------------------------------------------------------
   Ejercicio 5.2.4.2. Demostrar que
      forall A (i : A -> A -> bool),
        (forall x y, i x y = true <-> x = y) ->
        forall xs ys, iguales_lista i xs ys = true <-> xs = ys.
   ------------------------------------------------------------------ *)

Lemma iguales_lista_verdad_CN:
  forall A (i : A -> A -> bool),
    (forall x y, i x y = true <-> x = y) ->
    forall xs ys, iguales_lista i xs ys = true -> xs = ys.
Proof.
  intros A i H xs.                  (* A : Type
                                       i : A -> A -> bool
                                       H : forall x y : A, 
                                            i x y = true <-> x = y
                                       xs : list A
                                       ============================
                                       forall ys : list A, 
                                        iguales_lista i xs ys = true -> xs=ys *)
  induction xs as [|x xs' HIxs'].
  -                                 (* A : Type
                                       i : A -> A -> bool
                                       H : forall x y : A, 
                                            i x y = true <-> x = y
                                       ============================
                                       forall ys : list A, 
                                        iguales_lista i [ ] ys = true -> 
                                        [ ] = ys *)
    destruct ys as [|y ys'].
    +                               (* iguales_lista i [ ] [ ] = true -> 
                                       [ ] = [ ] *)
      intros.                       (*   H0 : iguales_lista i [ ] [ ] = true
                                       ============================
                                       [ ] = [ ] *)
      reflexivity.
    +                               (* y : A
                                       ys' : list A
                                       ============================
                                       iguales_lista i [ ] (y :: ys') = true 
                                       -> [ ] = y :: ys' *)
      simpl.                        (* false = true -> [ ] = y :: ys' *)
      intros H1.                    (* H1 : false = true
                                       ============================
                                       [ ] = y :: ys' *)
      inversion H1.
  -                                 (* x : A
                                       xs' : list A
                                       HIxs' : forall ys : list A, 
                                                iguales_lista i xs' ys = true 
                                                -> xs' = ys
                                       ============================
                                       forall ys : list A, 
                                        iguales_lista i (x :: xs') ys = true 
                                        -> x :: xs' = ys *)
    destruct ys as [|y ys'].
    +                               (* iguales_lista i (x :: xs') [ ] = true 
                                       -> x :: xs' = [ ] *)
      simpl.                        (* false = true -> x :: xs' = [ ] *)
      intros H1.                    (* H1 : false = true
                                       ============================
                                       x :: xs' = [ ] *)
      inversion H1.
    +                               (* y : A
                                       ys' : list A
                                       ============================
                                       iguales_lista i (x::xs') (y::ys') = true
                                       -> x :: xs' = y :: ys' *)
      simpl.                        (* i x y && iguales_lista i xs' ys' = true
                                       -> x :: xs' = y :: ys' *)
      intros H1.                    (* H1 : i x y && iguales_lista i xs' ys' = 
                                            true
                                       ============================
                                       x :: xs' = y :: ys' *)
      apply conj_verdad_syss in H1. (* H1 : i x y = true /\ 
                                            iguales_lista i xs' ys' = true
                                       ============================
                                       x :: xs' = y :: ys' *)
      destruct H1 as [H2 H3].       (* H2 : i x y = true
                                       H3 : iguales_lista i xs' ys' = true
                                       ============================
                                       x :: xs' = y :: ys' *)
      f_equal.
      *                             (* x = y *)
        apply H.                    (* i x y = true *)
        apply H2.
      *                             (* xs' = ys' *)
        apply HIxs'.                (* iguales_lista i xs' ys' = true *)
        apply H3.
Qed.

Lemma iguales_lista_verdad_CS:
  forall A (i : A -> A -> bool),
    (forall x y, i x y = true <-> x = y) ->
    forall xs ys, xs = ys -> iguales_lista i xs ys = true.
Proof.
  intros A i H xs.                (* A : Type
                                     i : A -> A -> bool
                                     H : forall x y : A, i x y = true <-> x = y
                                     xs : list A
                                     ============================
                                     forall ys : 
                                      list A, xs = ys -> 
                                      iguales_lista i xs ys = true *)
  induction xs as [|x xs' HIxs']. 
  -                               (* forall ys : 
                                      list A, [ ] = ys -> 
                                      iguales_lista i [ ] ys = true *)
    intros ys H1.                 (* ys : list A
                                     H1 : [ ] = ys
                                     ============================
                                     iguales_lista i [ ] ys = true *)
    rewrite <- H1.                 (* iguales_lista i [ ] [ ] = true *)
    simpl.                        (* true = true *)
    reflexivity.
  -                               (* x : A
                                     xs' : list A
                                     HIxs' : forall ys : 
                                              list A, xs' = ys -> 
                                              iguales_lista i xs' ys = true
                                     ============================
                                     forall ys : 
                                      list A, x :: xs' = ys -> 
                                      iguales_lista i (x :: xs') ys = true *)
    intros ys H1.                 (* ys : list A
                                     H1 : x :: xs' = ys
                                     ============================
                                     iguales_lista i (x :: xs') ys = true *)
    rewrite <-H1.                  (* iguales_lista i (x::xs') (x::xs') = true *)
    simpl.                        (* i x x && iguales_lista i xs' xs' = true *)
    apply conj_verdad_syss.       (* i x x = true /\ 
                                     iguales_lista i xs' xs' = true *)
    split.
    +                             (* i x x = true *)
      apply H.                    (* x = x *)
      reflexivity.
    +                             (* iguales_lista i xs' xs' = true *)
      apply HIxs'.                (* xs' = xs' *)
      reflexivity.
Qed.

Lemma iguales_lista_verdad_syss:
  forall A (i : A -> A -> bool),
    (forall x y, i x y = true <-> x = y) ->
    forall xs ys, iguales_lista i xs ys = true <-> xs = ys.
Proof.
  intros A i H xs ys.              (* A : Type
                                      i : A -> A -> bool
                                      H : forall x y : A, i x y = true <-> x = y
                                      xs, ys : list A
                                      ============================
                                      iguales_lista i xs ys = true <-> xs=ys *)
  split.
  -                                (* iguales_lista i xs ys = true -> xs = ys *)
    apply iguales_lista_verdad_CN. (* forall x y : A, i x y = true <-> x = y *)
    apply H.
  -                                (* xs = ys -> iguales_lista i xs ys = true *)
    apply iguales_lista_verdad_CS. (* forall x y : A, i x y = true <-> x = y *)
    apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2.5. Demostrar que
      forall (X : Type) (p : X -> bool) (xs : list X),
        todos p xs = true <-> Todos (fun x => p x = true) xs.
   ------------------------------------------------------------------ *)

Theorem todos_verdad_CN:
  forall (X : Type) (p : X -> bool) (xs : list X),
    todos p xs = true -> Todos (fun x => p x = true) xs.
Proof.
  intros X p xs.                 (* X : Type
                                    p : X -> bool
                                    xs : list X
                                    ============================
                                    todos p xs = true -> 
                                    Todos (fun x : X => p x = true) xs *)
  induction xs as [|x' xs' HI].
  -                              (* todos p [ ] = true -> 
                                    Todos (fun x : X => p x = true) [ ] *)
    simpl.                       (* true = true -> True *)
    intros.                      (* H : true = true
                                    ============================
                                    True *)
    reflexivity.
  -                              (* x' : X
                                    xs' : list X
                                    HI : todos p xs' = true -> 
                                         Todos (fun x : X => p x = true) xs'
                                    ============================
                                    todos p (x' :: xs') = true -> 
                                    Todos (fun x : X => p x = true) (x'::xs') *)
    simpl.                       (* p x' && todos p xs' = true ->
                                    p x' = true /\ 
                                    Todos (fun x : X => p x = true) xs' *)
    intros H.                    (* H : p x' && todos p xs' = true
                                    ============================
                                    p x' = true /\ 
                                    Todos (fun x : X => p x = true) xs' *)
    apply conj_verdad_syss in H. (* H :p x' = true /\ todos p xs' = true
                                    ============================
                                    p x' = true /\ 
                                    Todos (fun x : X => p x = true) xs' *)
    destruct H as [H1 H2].       (* H1 : p x' = true
                                    H2 : todos p xs' = true
                                    ============================
                                    p x' = true /\ 
                                    Todos (fun x : X => p x = true) xs' *)
    split.
    +                            (* p x' = true *)
      apply H1.
    +                            (* Todos (fun x : X => p x = true) xs' *)
      apply HI.                  (* todos p xs' = true *)
      apply H2.
Qed.

Theorem todos_verdad_CS:
  forall (X : Type) (p : X -> bool) (xs : list X),
    Todos (fun x => p x = true) xs -> todos p xs = true.
Proof.
  intros X p xs.                (* X : Type
                                   p : X -> bool
                                   xs : list X
                                   ============================
                                   Todos (fun x : X => p x = true) xs -> 
                                   todos p xs = true *)
  induction xs as [|x' xs' HI]. 
  -                             (* Todos (fun x : X => p x = true) [ ] -> 
                                   todos p [ ] = true *)
    simpl.                      (* True -> true = true *)
    intros.                     (* H : True
                                   ============================
                                   true = true *)
    reflexivity.
  -                             (* x' : X
                                   xs' : list X
                                   HI : Todos (fun x : X => p x = true) xs' -> 
                                        todos p xs' = true
                                   ============================
                                   Todos (fun x : X => p x = true) (x' :: xs') 
                                   -> todos p (x' :: xs') = true *)
    simpl.                      (* p x' = true /\ 
                                   Todos (fun x : X => p x = true) xs' ->
                                   p x' && todos p xs' = true *)
    intros [H1 H2].             (* H1 : p x' = true
                                   H2 : Todos (fun x : X => p x = true) xs'
                                   ============================
                                   p x' && todos p xs' = true *)
    apply conj_verdad_syss.     (* p x' = true /\ todos p xs' = true *)
    split.
    +                           (* p x' = true *)
      apply H1.
    +                           (* todos p xs' = true *)
      apply HI.                 (* Todos (fun x : X => p x = true) xs' *)
      apply H2.
Qed.

Theorem todos_verdad_syss:
  forall (X : Type) (p : X -> bool) (xs : list X),
    todos p xs = true <-> Todos (fun x => p x = true) xs.
Proof.
  intros X p xs.           (* X : Type
                              p : X -> bool
                              xs : list X
                              ============================
                              todos p xs = true <-> 
                              Todos (fun x : X => p x = true) xs *)
  split.
  -                        (* todos p xs = true -> 
                              Todos (fun x : X => p x = true) xs *)
    apply todos_verdad_CN. 
  -                        (* Todos (fun x : X => p x = true) xs -> 
                              todos p xs = true *)
    apply todos_verdad_CS.
Qed.
  
(* =====================================================================
   §§ 5.3. Lógica clásica vs. constructiva  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.3.1. Definir la proposicion
      tercio_excluso
   que afirma que  (forall P : Prop, P \/ ~ P).
   ------------------------------------------------------------------ *)


Definition tercio_excluso : Prop := forall P : Prop,
  P \/ ~ P.

(* ---------------------------------------------------------------------
   Nota. La proposión tercio_excluso no es demostrable en Coq.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 5.3.2. Demostrar que
      forall (P : Prop) (b : bool),
        (P <-> b = true) -> P \/ ~ P.
   ------------------------------------------------------------------ *)

Theorem tercio_exluso_restringido :
  forall (P : Prop) (b : bool),
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.  
  -               (* P : Prop
                     H : P <-> true = true
                     ============================
                     P \/ ~ P *)
    left.         (* P *)
    rewrite H.    (* true = true *)
    reflexivity.
  -               (* P : Prop
                     H : P <-> false = true
                     ============================
                     P \/ ~ P *)
    right.        (* ~ P *)
    rewrite H.    (* false <> true *)
    intros H1.    (* H1 : false = true
                     ============================
                     False *)
    inversion H1. 
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.3.3. Demostrar que
      forall (n m : nat),
        n = m \/ n <> m.
   ------------------------------------------------------------------ *)

Theorem tercio_exluso_restringido_eq:
  forall (n m : nat),
    n = m \/ n <> m.
Proof.
  intros n m.                      (* n, m : nat
                                      ============================
                                      n = m \/ n <> m *)
  apply (tercio_exluso_restringido 
           (n = m)
           (iguales_nat n m)).     (* n = m <-> iguales_nat n m = true *)
  symmetry.                        (* iguales_nat n m = true <-> n = m *)
  apply iguales_nat_bool_prop.
Qed.

(* ---------------------------------------------------------------------
   Notas.
   1. En Coq no se puede demostrar el principio del tercio exluso.
   2. Las demostraciones de las fórmulas existenciales tienen que
      proporcionar un testigo.
   2. La lógica de Coq es constructiva.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 5.3.1. Demostrar que
      forall (P : Prop),
        ~ ~ (P \/ ~ P).
   ------------------------------------------------------------------ *)

Theorem tercio_excluso_irrefutable:
  forall (P : Prop),
    ~ ~ (P \/ ~ P).
Proof.
  intros P.   (* P : Prop
                 ============================
                 ~ ~ (P \/ ~ P) *)
  unfold not. (* (P \/ (P -> False) -> False) -> False *)
  intros H.   (* H : P \/ (P -> False) -> False
                 ============================
                 False *)
  apply H.    (* P \/ (P -> False) *)
  right.      (* P -> False *)
  intro H1.   (* H1 : P
                 ============================
                 False *)
  apply H.    (* P \/ (P -> False) *)
  left.       (* P *)
  apply H1.
Qed.

(* ---------------------------------------------------------------------
   Nota. El teorema anterior garantiza que añadir el tercio excluso como
   axioma no provoca contradicción.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 5.3.2. Demostrar que
      tercio_excluso ->
      forall (X : Type) (P : X -> Prop),
        ~ (exists x, ~ P x) -> (forall x, P x).

   Nota. La condición del tercio_excluso es necesaria.
   ------------------------------------------------------------------ *)

Theorem no_existe_no:
  tercio_excluso ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros H1 X P H2 x.          (* H1 : tercio_excluso
                                  X : Type
                                  P : X -> Prop
                                  H2 : ~ (exists x : X, ~ P x)
                                  x : X
                                  ============================
                                  P x *)
  unfold tercio_excluso in H1. (* H1 : forall P : Prop, P \/ ~ P *)
  assert (P x \/ ~ P x).
  -                            (* P x \/ ~ P x *)
    apply H1.
  -                            (* H : P x \/ ~ P x
                                  ============================
                                  P x *)
    destruct H as [H3 | H4].
    +                          (* x : X
                                  H3 : P x
                                  ============================
                                  P x *)
      apply H3.
    +                          (* x : X
                                  H4 : ~ P x
                                  ============================
                                  P x *)
      exfalso.                 (* False *)
      apply H2.                (* exists x0 : X, ~ P x0 *)
      exists x.                     (* ~ P x *)
      apply H4.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.3.1. En este ejercico se van a demostrar 4 formas
   equivalentes del principio del tercio excluso. 

   Sea peirce la proposición definida por
      Definition peirce: Prop := forall P Q : Prop,
        ((P -> Q) -> P) -> P.

   Demostrar que 
      tercio_excluso <-> peirce 
   ------------------------------------------------------------------ *)

Definition peirce: Prop := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Theorem tercio_excluso_peirce_L1:
  tercio_excluso -> peirce.
Proof.
  unfold tercio_excluso.     (* 
                                ============================
                                (forall P : Prop, P \/ ~ P) -> peirce *)
  unfold peirce.             (* (forall P : Prop, P \/ ~ P) -> 
                                forall P Q : Prop, ((P -> Q) -> P) -> P *)
  intros H1 P Q H2.          (* H1 : forall P : Prop, P \/ ~ P
                                P, Q : Prop
                                H2 : (P -> Q) -> P
                                ============================
                                P *)
  assert (P \/ ~P).
  -                          (* P \/ ~ P *)
    apply H1.
  -                          (* H : P \/ ~ P
                                ============================
                                P *)
    destruct H as [H3 | H4]. 
    +                        (* H3 : P
                                ============================
                                P *)
      apply H3.
    +                        (* H4 : ~ P
                                ============================
                                P *)
      apply H2.              (* P -> Q *)
      intros H5.             (* H5 : P
                                ============================
                                Q *)
      exfalso.               (* False *)
      apply H4.              (* P *)
      apply H5.
Qed.

Theorem tercio_excluso_peirce_L2:
  peirce -> tercio_excluso.
Proof.
  unfold peirce.         (* 
                            ============================
                            (forall P Q : Prop, ((P -> Q) -> P) -> P) -> 
                            tercio_excluso *)
  unfold tercio_excluso. (* (forall P Q : Prop, ((P -> Q) -> P) -> P) -> 
                            forall P : Prop, P \/ ~ P *)
  intros H P.            (* H : forall P Q : Prop, ((P -> Q) -> P) -> P
                            P : Prop
                            ============================
                            P \/ ~ P *)
  apply H with (Q := False). (* (P \/ ~ P -> False) -> P \/ ~ P *)
  intros H1.             (* H1 : P \/ ~ P -> False
                            ============================
                            P \/ ~ P *)
  right.                 (* ~ P *)
  unfold not.            (* P -> False *)
  intros H2.             (* H2 : P
                            ============================
                            False *)
  apply H1.              (* P \/ ~ P *)
  left.                  (* P *)
  apply H2.
Qed.

Theorem tercio_excluso_equiv_peirce:
  tercio_excluso <-> peirce.
Proof.
  split.
  -                                 (* 
                                       ============================
                                       tercio_excluso -> peirce *)
    apply tercio_excluso_peirce_L1. 
  -                                 (* 
                                       ============================
                                       peirce -> tercio_excluso *)
    apply tercio_excluso_peirce_L2.
Qed.


(* ---------------------------------------------------------------------
   Ejercicio 5.3.2. Sea eliminacion_doble_negacion la proposición
   definida por 
      Definition eliminacion_doble_negacion: Prop := forall P : Prop,
        ~~P -> P.

   Demostrar que 
      tercio_excluso <-> eliminacion_doble_negacion
   ------------------------------------------------------------------ *)

Definition eliminacion_doble_negacion: Prop := forall P : Prop,
  ~~P -> P.

Theorem tercio_excluso_equiv_eliminacion_doble_negacion_L1:
  tercio_excluso -> eliminacion_doble_negacion.
Proof.
  unfold tercio_excluso.             (* 
                                        ============================
                                        (forall P : Prop, P \/ ~ P) -> 
                                        eliminacion_doble_negacion *)
  unfold eliminacion_doble_negacion. (* (forall P : Prop, P \/ ~ P) -> 
                                        forall P : Prop, ~ ~ P -> P *)
  intros H1 P H2.                    (* H1 : forall P : Prop, P \/ ~ P
                                        P : Prop
                                        H2 : ~ ~ P
                                        ============================
                                        P *)
  assert (P \/ ~P).
  -                                  (* P \/ ~ P *)
    apply H1.
  -                                  (* H : P \/ ~ P
                                        ============================
                                        P *)
    destruct H as [H3 | H4].
    +                                (* H2 : ~ ~ P
                                        H3 : P
                                        ============================
                                        P *)
      apply H3.
    +                                (* H4 : ~ P
                                        ============================
                                        P *)
      exfalso.                       (* False *)
      apply H2.                      (* ~ P *)
      apply H4.
Qed.

Theorem tercio_excluso_equiv_eliminacion_doble_negacion_L2:
  eliminacion_doble_negacion -> tercio_excluso.
Proof.
  unfold eliminacion_doble_negacion. (* 
                                        ============================
                                        (forall P : Prop, ~ ~ P -> P) -> 
                                        tercio_excluso *)
  unfold tercio_excluso.             (* (forall P : Prop, ~ ~ P -> P) -> 
                                        forall P : Prop, P \/ ~ P *)
  intros H P.                        (* H : forall P : Prop, ~ ~ P -> P
                                        P : Prop
                                        ============================
                                        P \/ ~ P *)
  apply H.                           (* ~ ~ (P \/ ~ P) *)
  apply tercio_excluso_irrefutable.
Qed.

Theorem tercio_excluso_equiv_eliminacion_doble_negacion:
  tercio_excluso <-> eliminacion_doble_negacion.
Proof.
  split.
  -
    apply tercio_excluso_equiv_eliminacion_doble_negacion_L1.
  -
    apply tercio_excluso_equiv_eliminacion_doble_negacion_L2.
Qed.


(* ---------------------------------------------------------------------
   Ejercicio 5.3.3. Sea morgan_no_no la proposición
   definida por 
      Definition de_morgan_no_no: Prop :=
        forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.

   Demostrar que 
      tercio_excluso <-> morgan_no_no
   ------------------------------------------------------------------ *)

Definition de_morgan_no_no: Prop :=
  forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.

Theorem tercio_excluso_equiv_de_morgan_no_no_L1:
  tercio_excluso -> de_morgan_no_no.
Proof.
  unfold tercio_excluso.     (* 
                                ============================
                                (forall P : Prop, P \/ ~ P) -> 
                                de_morgan_no_no *)
  unfold de_morgan_no_no.    (* (forall P : Prop, P \/ ~ P) -> 
                                forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q *)
  intros H1 P Q H2.          (* H1 : forall P : Prop, P \/ ~ P
                                P, Q : Prop
                                H2 : ~ (~ P /\ ~ Q)
                                ============================
                                P \/ Q *)
  assert (P \/ ~P).
  -                          (* P \/ ~ P *)
    apply H1.
  -                          (* H : P \/ ~ P
                                ============================
                                P \/ Q *)
    destruct H as [H3 | H4]. 
    +                        (* H2 : ~ (~ P /\ ~ Q)
                                H3 : P
                                ============================
                                P \/ Q *)
      left.                  (* P *)
      apply H3.
    +                        (* H4 : ~ P
                                ============================
                                P \/ Q *)
      right.                 (* Q *)
      assert (Q \/ ~ Q).
      *                      (* Q \/ ~ Q *)
        apply H1.
      *                      (* H : Q \/ ~ Q
                                ============================
                                Q *)
        destruct H as [H5 | H6].
        --                   (* H5 : Q
                                ============================
                                Q *)
          apply H5.
        --                   (* H6 : ~ Q
                                ============================
                                Q *)
          exfalso.           (* False *)
          apply H2.          (* ~ P /\ ~ Q *)
          split.
          ++                 (* ~ P *)
            apply H4.
          ++                 (* ~ Q *)
            apply H6.
Qed.

Theorem tercio_excluso_equiv_de_morgan_no_no_L2:
  de_morgan_no_no -> tercio_excluso.
Proof.
  unfold de_morgan_no_no. (* 
                             ============================
                             (forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q) -> 
                             tercio_excluso *)
  unfold tercio_excluso.  (* (forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q) -> 
                             forall P : Prop, P \/ ~ P *)
  intros H1 P.            (* H1 : forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q
                             P : Prop
                             ============================
                             P \/ ~ P *)
  apply H1.               (* ~ (~ P /\ ~ ~ P) *)
  intros H2.              (* H2 : ~ P /\ ~ ~ P
                             ============================
                             False *)
  destruct H2 as (H3,H4). (* H3 : ~ P
                             H4 : ~ ~ P
                             ============================
                             False *)
  apply H4.               (* ~ P *)
  apply H3.
Qed.


Theorem tercio_excluso_equiv_de_morgan_no_no:
  tercio_excluso <-> de_morgan_no_no.
Proof.
  split.
  -
    apply tercio_excluso_equiv_de_morgan_no_no_L1.
  -
    apply tercio_excluso_equiv_de_morgan_no_no_L2.
Qed.
  
(* ---------------------------------------------------------------------
   Ejercicio 5.3.4. Sea condicional_a_disyuncion la proposición
   definida por 
      Definition condicional_a_disyuncion: Prop :=
        forall P Q : Prop, (P -> Q) -> (~P \/ Q).

   Demostrar que 
      tercio_excluso <-> morgan_no_no
   ------------------------------------------------------------------ *)

Definition condicional_a_disyuncion: Prop :=
  forall P Q : Prop, (P -> Q) -> (~P \/ Q).

Lemma tercio_excluso_equiv_condicional_a_disyuncion_L1:
  tercio_excluso -> condicional_a_disyuncion.
Proof.
  unfold tercio_excluso.           (* 
                                      ============================
                                      (forall P : Prop, P \/ ~ P) -> 
                                      condicional_a_disyuncion *)
  unfold condicional_a_disyuncion. (* (forall P : Prop, P \/ ~ P) -> 
                                      forall P Q : Prop, (P -> Q) -> ~ P \/ Q *)
  intros H1 P Q H2.                (* H1 : forall P : Prop, P \/ ~ P
                                      P, Q : Prop
                                      H2 : P -> Q
                                      ============================
                                      ~ P \/ Q *)
  assert (P \/ ~P).
  -                                (* P \/ ~ P *)
    apply H1.
  -                                (* H : P \/ ~ P
                                      ============================
                                      ~ P \/ Q *)
    destruct H as [H3 | H4]. 
    +                              (* H3 : P
                                      ============================
                                      ~ P \/ Q *)
      right.                       (* Q *)
      apply H2.                    (* P *)
      apply H3.
    +                              (* H4 : ~ P
                                      ============================
                                      ~ P \/ Q *)
      left.                        (* ~ P *)
      apply H4.
Qed.

Lemma tercio_excluso_equiv_condicional_a_disyuncion_L2:
  condicional_a_disyuncion -> tercio_excluso.
Proof.
  unfold condicional_a_disyuncion. (* 
                                      ============================
                                      (forall P Q:Prop, (P -> Q) -> ~ P \/ Q) 
                                      -> tercio_excluso *)
  unfold tercio_excluso.           (* (forall P Q:Prop, (P -> Q) -> ~ P \/ Q) 
                                      -> forall P : Prop, P \/ ~ P *)
  intros H1 P.                     (* H1 : forall P Q : Prop, 
                                            (P -> Q) -> ~ P \/ Q
                                      P : Prop
                                      ============================
                                      P \/ ~ P *)
  apply disy_conmutativa.          (* ~ P \/ P *)
  apply H1.                        (* P -> P *)
  intros.                          (* H : P
                                      ============================
                                      P *)
  apply H.
Qed.


Theorem tercio_excluso_equiv_condicional_a_disyuncion:
  tercio_excluso <-> condicional_a_disyuncion.
Proof.
  split.
  - apply tercio_excluso_equiv_condicional_a_disyuncion_L1.
  - apply tercio_excluso_equiv_condicional_a_disyuncion_L2.
Qed.    
  
(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Logic in Coq" de Peirce et als. http://bit.ly/2nv1T9Z *)
