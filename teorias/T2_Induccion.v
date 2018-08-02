(* T2: Demostraciones por inducción sobre los números naturales en Coq *)

Require Export T1_PF_en_Coq.

(* El contenido de la teoría es
   1. Demostraciones por inducción. 
   2. Demostraciones anidadas.
   3. Demostraciones formales vs demostraciones informales.
   4. Ejercicios complementarios *)

(* =====================================================================
   § 1. Demostraciones por inducción 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1. Demostrar que
      forall n:nat, n = n + 0.
   ------------------------------------------------------------------ *)

(* 1º intento: con métodos elementales *)
Theorem suma_n_0_a: forall n:nat, n = n + 0.
Proof.
  intros n. (* n : nat
               ============================
                n = n + 0 *)
  simpl.    (* n : nat
               ============================
                n = n + 0 *)
Abort.

(* 2º intento: con casos *)
Theorem suma_n_0_b : forall n:nat,
  n = n + 0.
Proof.
  intros n.             (* n : nat
                           ============================
                            n = n + 0 *)
  destruct n as [| n']. 
  -                     (* 
                           ============================
                            0 = 0 + 0 *)
    reflexivity. 
  -                     (* n' : nat
                           ============================
                            S n' = S n' + 0  *)
    simpl.              (* n' : nat
                           ============================
                            S n' = S (n' + 0) *)
Abort.

(* 3ª intento: con inducción *)
Theorem suma_n_0 : forall n:nat,
    n = n + 0.
Proof.
  intros n.                   (* n : nat
                                 ============================
                                 n = n + 0 *) 
  induction n as [| n' IHn']. 
  +                           (*   
                                 ============================
                                 0 = 0 + 0 *)
    reflexivity.
  +                           (* n' : nat
                                 IHn' : n' = n' + 0
                                 ============================
                                 S n' = S n' + 0 *)
    simpl.                    (* S n' = S (n' + 0) *)
    rewrite <- IHn'.          (* S n' = S n' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.2. Demostrar que
      forall n, n - n = 0.
   ------------------------------------------------------------------ *)

Theorem resta_n_n: forall n, n - n = 0.
Proof.
  intros n.                   (* n : nat
                                 ============================
                                 n - n = 0 *)
  induction n as [| n' IHn']. 
  +                           (*  
                                 ============================
                                 0 - 0 = 0 *)
    reflexivity.
  +                           (* n' : nat
                                 IHn' : n' - n' = 0
                                 ============================
                                 S n' - S n' = 0 *)
    simpl.                    (* n' - n' = 0 *)
    rewrite -> IHn'.          (* 0 = 0 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1. Demostrar que
      forall n:nat, n * 0 = 0.
   ------------------------------------------------------------------ *)

Theorem multiplica_n_0: forall n:nat, n * 0 = 0.
Proof.
  intros n.                   (* n : nat
                                 ============================
                                 n * 0 = 0 *)
  induction n as [| n' IHn']. 
  +                           (* 
                                 ============================
                                 0 * 0 = 0 *)
    reflexivity.      
  +                           (* n' : nat
                                 IHn' : n' * 0 = 0
                                 ============================
                                 S n' * 0 = 0 *)   
    simpl.                    (* n' * 0 = 0 *)
    rewrite IHn'.             (* 0 = 0 *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.2. Demostrar que, 
      forall n m : nat, S (n + m) = n + (S m).
   ------------------------------------------------------------------ *)

Theorem suma_n_Sm: forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.                (*  n, m : nat
                                 ============================
                                 S (n + m) = n + S m *)
  induction n as [|n' IHn']. 
  +                          (* m : nat
                                ============================
                                S (0 + m) = 0 + S m *)
    simpl.                   (* m : nat
                                ============================
                                S m = S m *)
    reflexivity.
  +                          (* S (S n' + m) = S n' + S m *)
    simpl.                   (* S (S (n' + m)) = S (n' + S m) *)
    rewrite IHn'.            (* S (n' + S m) = S (n' + S m) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.3. Demostrar que 
      forall n m : nat, n + m = m + n.
   ------------------------------------------------------------------ *)

Theorem suma_conmutativa: forall n m : nat,
  n + m = m + n.
Proof.
  intros  n m.               (* n, m : nat
                                ============================
                                n + m = m + n *)
  induction n as [|n' IHn'].
  +                          (* m : nat
                                ============================
                                0 + m = m + 0 *)
    simpl.                   (* m = m + 0 *)
    rewrite <- suma_n_0.     (* m = m *)
    reflexivity.
  +                          (* n', m : nat
                                IHn' : n' + m = m + n'
                                ============================
                                S n' + m = m + S n' *)
    simpl.                   (* S (n' + m) = m + S n' *)
    rewrite IHn'.            (* S (m + n') = m + S n' *)
    rewrite <- suma_n_Sm.    (* S (m + n') = S (m + n') *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.4. Demostrar que 
      forall n m p : nat, n + (m + p) = (n + m) + p.
   ------------------------------------------------------------------ *)

Theorem suma_asociativa: forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.              (* n, m, p : nat
                                ============================
                                n + (m + p) = (n + m) + p *)
  induction n as [|n' IHn'].
  +                          (* m, p : nat
                                ============================
                                0 + (m + p) = (0 + m) + p *)
    reflexivity.
  +                          (* n', m, p : nat
                                IHn' : n' + (m + p) = n' + m + p
                                ============================
                                S n' + (m + p) = (S n' + m) + p *)
    simpl.                   (* S (n' + (m + p)) = S ((n' + m) + p) *)
    rewrite IHn'.            (* S ((n' + m) + p) = S ((n' + m) + p) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.5. Se considera la siguiente función que dobla su argumento. 
      Fixpoint doble (n:nat) :=
        match n with
        | O    => O
        | S n' => S (S (doble n'))
        end.

   Demostrar que 
      forall n, doble n = n + n. 
   ------------------------------------------------------------------ *)

Fixpoint doble (n:nat) :=
  match n with
  | O    => O
  | S n' => S (S (doble n'))
  end.

Lemma doble_suma : forall n, doble n = n + n .
Proof.
  intros n.                  (* n : nat
                                ============================
                                doble n = n + n *)
  induction n as [|n' IHn']. 
  +                          (* 
                                ============================
                                doble 0 = 0 + 0 *)
    reflexivity.
  +                          (* n' : nat
                                IHn' : doble n' = n' + n'
                                ============================
                                doble (S n') = S n' + S n' *)
    simpl.                   (* S (S (doble n')) = S (n' + S n') *)
    rewrite IHn'.            (* S (S (n' + n')) = S (n' + S n') *)
    rewrite suma_n_Sm.       (* S (n' + S n') = S (n' + S n') *)
    reflexivity.
Qed. 

(* ---------------------------------------------------------------------
   Ejercicio 1.6. Demostrar que
      forall n : nat, esPar (S n) = negacion (esPar n).
   ------------------------------------------------------------------ *)

Theorem esPar_S : forall n : nat,
  esPar (S n) = negacion (esPar n).
Proof.
  intros n.                      (* n : nat
                                    ============================
                                    esPar (S n) = negacion (esPar n) *)
  induction n as [|n' IHn'].
  +                              (* 
                                    ============================
                                    esPar 1 = negacion (esPar 0) *)
    simpl.                       (* 
                                    ============================
                                    false = false *)
    reflexivity.
  +                              (* n' : nat
                                    IHn' : esPar (S n') = negacion (esPar n')
                                    ============================
                                    esPar (S (S n')) = 
                                     negacion (esPar (S n')) *)
    rewrite IHn'.                (* esPar (S (S n')) = 
                                     negacion (negacion (esPar n')) *)
    rewrite negacion_involutiva. (* esPar (S (S n')) = esPar n' *)
    simpl.                       (* esPar n' = esPar n' *)
    reflexivity.
Qed.

(* =====================================================================
   § 2. Demostraciones anidadas
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1. Demostrar que
      forall n m : nat, (0 + n) * m = n * m.
   ------------------------------------------------------------------ *)

Theorem producto_0_suma': forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.            (* n, m : nat
                            ============================
                            (0 + n) * m = n * m *)
  assert (H: 0 + n = n). 
  -                      (* n, m : nat
                            ============================
                            0 + n = n *)
    reflexivity.
  -                      (* n, m : nat
                            H : 0 + n = n
                            ============================
                            (0 + n) * m = n * m *)
    rewrite -> H.        (* n * m = n * m *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.2. Demostrar que
      forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q)
   ------------------------------------------------------------------ *)

(* 1º intento sin assert*)
Theorem suma_reordenada_1: forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.              (* n, m, p, q : nat
                                  ============================
                                  (n + m) + (p + q) = (m + n) + (p + q) *)
  rewrite -> suma_conmutativa. (* n, m, p, q : nat
                                  ============================
                                  p + q + (n + m) = m + n + (p + q) *)
Abort.

(* 2º intento con assert *)
Theorem suma_reordenada: forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.                (* n, m, p, q : nat
                                    ============================
                                    (n + m) + (p + q) = (m + n) + (p + q) *)
  assert (H: n + m = m + n).
  -                              (* n, m, p, q : nat
                                    ============================
                                    n + m = m + n *)
    rewrite -> suma_conmutativa. (* m + n = m + n *)
    reflexivity.
  -                              (* n, m, p, q : nat
                                    H : n + m = m + n
                                    ============================
                                    (n + m) + (p + q) = (m + n) + (p + q) *)
    rewrite -> H.                (* m + n + (p + q) = m + n + (p + q) *)
    reflexivity.
Qed.

(* =====================================================================
   § 3. Demostraciones formales vs demostraciones informales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 3.1. Escribir la demostración informal (en lenguaje natural)
   correspondiente a la demostración formal de la asociatividad de la
   suma del ejercicio 1.4.
   ------------------------------------------------------------------ *)

(* Demostración por inducción en n.

   - Caso base: Se supone que n es 0 y hay que demostrar que
        0 + (m + p) = (0 + m) + p.
     Esto es consecuencia inmediata de la definición de suma.

   - Paso de indución: Suponemos la hipótesis de inducción
        n' + (m + p) = (n' + m) + p.                 
     Hay que demostrar que
        (S n') + (m + p) = ((S n') + m) + p.
     que, por la definición de suma, se reduce a
        S (n' + (m + p)) = S ((n' + m) + p)
     que por la hipótesis de inducción se reduce a
        S ((n' + m) + p) = S ((n' + m) + p)
     que es una identidad. *)

(* ---------------------------------------------------------------------
   Ejercicio 3.2. Escribir la demostración informal (en lenguaje natural)
   correspondiente a la demostración formal de la asociatividad de la
   suma del ejercicio 1.3.
   ------------------------------------------------------------------ *)

(* Demostración por inducción en n.

   - Caso base: Se supone que n es 0 y hay que demostrar que
        0 + m = m + 0
     que, por la definición de la suma, se reduce a
        m = m + 0
     que se verifica por el lema suma_n_0.

   - Paso de indución: Suponemos la hipótesis de inducción
        n' + m = m + n'
     Hay que demostrar que
        S n' + m = m + S n'
     que, por la definición de suma, se reduce a
        S (n' + m) = m + S n'
     que, por la hipótesis de inducción, se reduce a
        S (m + n') = m + S n'
     que, por el lema suma_n_Sm, se reduce a
        S (m + n') = S (m + n')
     que es una identidad. *)

(* ---------------------------------------------------------------------
   Ejercicio 3.3. Demostrar que
      forall n:nat, iguales_nat n n = true.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_refl: forall n : nat,
    iguales_nat n n = true.
Proof.
  intros n.                  (* n : nat
                                ============================
                                iguales_nat n n = true *)
  induction n as [|n' IHn']. 
  -                          (* 
                                ============================
                                iguales_nat 0 0 = true *)
    reflexivity.
  -                          (* n' : nat
                                IHn' : iguales_nat n' n' = true
                                ============================
                                iguales_nat (S n') (S n') = true *)
    simpl.                   (* iguales_nat n' n' = true *)
    rewrite <- IHn'.          (* true = true *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4. Escribir la demostración informal (en lenguaje natural)
   correspondiente la demostración del ejercicio anterior.
   ------------------------------------------------------------------ *)

(* Demostración por inducción en n.

   - Caso base: Se supone que n es 0 y hay que demostrar que
        true = iguales_nat 0 0
     que se verifica por la definición de iguales_nat.

   - Paso de indución: Suponemos la hipótesis de inducción
        true = iguales_nat n' n'
     Hay que demostrar que
        true = iguales_nat (S n') (S n') 
     que, por la definición de iguales_nat, se reduce a
        true = iguales_nat n' n
     que, por la hipótesis de inducción, se reduce a
        true = true
     que es una identidad. *)

(* =====================================================================
   § 4. Ejercicios complementarios 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 4.1. Demostrar, usando assert pero no induct,
      forall n m p : nat, n + (m + p) = m + (n + p).
   ------------------------------------------------------------------ *)

Theorem suma_permutada: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof. 
  intros n m p.               (* n, m, p : nat
                                 ============================
                                 n + (m + p) = m + (n + p) *)
  rewrite suma_asociativa.    (* n, m, p : nat
                                 ============================
                                 (n + m) + p = m + (n + p) *)
  rewrite suma_asociativa.    (* n, m, p : nat
                                 ============================
                                 n + m + p = m + n + p *)
  assert (H : n + m = m + n). 
  -                           (* n, m, p : nat
                                 ============================
                                 n + m = m + n *)
    rewrite suma_conmutativa. (* m + n = m + n *)
    reflexivity. 
  -                           (* n, m, p : nat
                                 H : n + m = m + n
                                 ============================
                                 (n + m) + p = (m + n) + p *)
    rewrite H.                (* (m + n) + p = (m + n) + p *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.2. Demostrar que la multiplicación es conmutativa.
   ------------------------------------------------------------------ *)

Lemma producto_n_1 : forall n: nat,
    n * 1 = n.
Proof.
  intro n.                   (* n : nat
                                ============================
                                n * 1 = n *)
  induction n as [|n' IHn']. 
  -                          (* 
                                ============================
                                0 * 1 = 0 *)
    reflexivity.
  -                          (* n' : nat
                                IHn' : n' * 1 = n'
                                ============================
                                S n' * 1 = S n' *)
    simpl.                   (* S (n' * 1) = S n' *)
    rewrite IHn'.            (* S n' = S n' *)
    reflexivity.
Qed.

Theorem suma_n_1 : forall n : nat,
    n + 1 = S n.
Proof.
  intro n.                   (* n : nat
                                ============================
                                n + 1 = S n *)
  induction n as [|n' HIn']. 
  -                          (* 
                                ============================
                                0 + 1 = 1 *)
    reflexivity.
  -                          (* n' : nat
                                HIn' : n' + 1 = S n'
                                ============================
                                S n' + 1 = S (S n') *)
    simpl.                   (* S (n' + 1) = S (S n') *)
    rewrite HIn'.            (* S (S n') = S (S n') *)
    reflexivity.
Qed.

Theorem producto_n_Sm: forall n m : nat, 
    n * (m + 1) = n * m + n.
Proof.
  intros n m.                   (* n, m : nat
                                   ============================
                                   n * (m + 1) = n * m + n *)
  induction n as [|n' IHn'].
  -                             (* m : nat
                                   ============================
                                   0 * (m + 1) = 0 * m + 0 *)
    reflexivity.
  -                             (* n', m : nat
                                   IHn' : n' * (m + 1) = n' * m + n'
                                   ============================
                                   S n' * (m + 1) = S n' * m + S n' *)
    simpl.                      (* (m + 1) + n' * (m + 1) = 
                                    (m + n' * m) + S n' *)
    rewrite IHn'.               (* (m + 1) + (n' * m + n') = 
                                    (m + n' * m) + S n' *)
    rewrite suma_permutada.     (* n' * m + ((m + 1) + n') = 
                                    (m + n' * m) + S n' *)
    rewrite <- suma_asociativa. (* n' * m + (m + (1 + n')) = 
                                    (m + n' * m) + S n' *)
    rewrite <- suma_n_1.        (* n' * m + (m + (n' + 1)) = 
                                   (m + n' * m) + S n' *)
    rewrite suma_n_1.           (* n' * m + (m + S n') = (m + n' * m) + S n' *)
    rewrite suma_permutada.     (* m + (n' * m + S n') = (m + n' * m) + S n' *)
    rewrite suma_asociativa.    (* m + (n' * m + S n') = (m + n' * m) + S n' *)
    reflexivity.
Qed.

Theorem producto_conmutativa: forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.                 (* n, m : nat
                                 ============================
                                 n * m = m * n *)
  induction n as [|n' HIn'].
  -                           (* m : nat
                                 ============================
                                 0 * m = m * 0 *)
    rewrite multiplica_n_0.   (* 0 * m = 0 *)
    reflexivity.
  -                           (* n', m : nat
                                 HIn' : n' * m = m * n'
                                 ============================
                                 S n' * m = m * S n' *)
    simpl.                    (* m + n' * m = m * S n' *)
    rewrite HIn'.             (* m + m * n' = m * S n' *)
    rewrite <- suma_n_1.      (* m + m * n' = m * (n' + 1) *)
    rewrite producto_n_Sm.    (* m + m * n' = m * n' + m *)
    rewrite suma_conmutativa. (* m * n' + m = m * n' + m *)
   reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.3. Demostrar que 
      forall n : nat, true = menor_o_igual n n.  
   ------------------------------------------------------------------ *)


Theorem menor_o_igual_refl: forall n : nat,
    true = menor_o_igual n n.
Proof.
  intro n.                    (* n : nat
                                 ============================
                                 true = menor_o_igual n n *)
  induction n as [| n' HIn']. 
  -                           (* 
                                 ============================
                                 true = menor_o_igual 0 0 *)
    reflexivity.
  -                           (* n' : nat
                                 HIn' : true = menor_o_igual n' n'
                                 ============================
                                 true = menor_o_igual (S n') (S n') *)
    simpl.                    (* true = menor_o_igual n' n' *)
    rewrite HIn'.             (* menor_o_igual n' n' = menor_o_igual n' n' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.4. Demostrar que 
      forall n : nat, iguales_nat 0 (S n) = false. 
   ------------------------------------------------------------------ *)

Theorem cero_distinto_S: forall n : nat,
  iguales_nat 0 (S n) = false.
Proof.
  intros n.    (* n : nat
                  ============================
                  iguales_nat 0 (S n) = false *)
  simpl.       (* false = false *)
  reflexivity. 
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.5. Demostrar que 
      forall b : bool, conjuncion b false = false.
   ------------------------------------------------------------------ *)

Theorem conjuncion_false_r : forall b : bool,
  conjuncion b false = false.
Proof.
  intros b.      (* b : bool
                    ============================
                    b && false = false *)
  destruct b.
  -              (* 
                    ============================
                    true && false = false *)
    simpl.       (* false = false *)
    reflexivity.
  -              (* 
                    ============================
                    false && false = false *)
    simpl.       (* false = false *)
    reflexivity. 
Qed. 

(* ---------------------------------------------------------------------
   Ejercicio 4.6. Demostrar que 
      forall n m p : nat, menor_o_igual n m = true -> 
                          menor_o_igual (p + n) (p + m) = true.
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_suma: forall n m p : nat,
  menor_o_igual n m = true -> menor_o_igual (p + n) (p + m) = true.
Proof.
  intros n m p H.            (* n, m, p : nat
                                H : menor_o_igual n m = true
                                ============================
                                menor_o_igual (p + n) (p + m) = true *)
  induction p as [|p' HIp'].
  -                          (* n, m : nat
                                H : menor_o_igual n m = true
                                ============================
                                menor_o_igual (0 + n) (0 + m) = true *)
    simpl.                   (* menor_o_igual n m = true *)
    rewrite H.               (* true = true *)
    reflexivity.
  -                          (* n, m, p' : nat
                                H : menor_o_igual n m = true
                                HIp' : menor_o_igual (p' + n) (p' + m) = true
                                ============================
                                menor_o_igual (S p' + n) (S p' + m) = true *)
    simpl.                   (* menor_o_igual (p' + n) (p' + m) = true *)
    rewrite HIp'.            (* true = true *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.7. Demostrar que 
      forall n : nat, iguales_nat (S n) 0 = false.
   ------------------------------------------------------------------ *)

Theorem S_distinto_0 : forall n:nat,
  iguales_nat (S n) 0 = false.
Proof.
  intro n.     (* n : nat
                  ============================
                  iguales_nat (S n) 0 = false *)
  simpl.       (* false = false *)
  reflexivity. 
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.8. Demostrar que 
      forall n:nat, 1 * n = n.
   ------------------------------------------------------------------ *)

Theorem producto_1_n: forall n:nat, 1 * n = n.
Proof.
  intro n.          (* n : nat
                       ============================
                       1 * n = n *)
  simpl.            (* n + 0 = n *)
  rewrite suma_n_0. (* n + 0 = n + 0 *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.9. Demostrar que 
       forall b c : bool, disyuncion (conjuncion b c)
                              (disyuncion (negacion b)
                                          (negacion c))
                          = true.
   ------------------------------------------------------------------ *)

Theorem alternativas: forall b c : bool,
    disyuncion
      (conjuncion b c)
      (disyuncion (negacion b)
                  (negacion c))
    = true.
Proof.
  intros [] [].
  - reflexivity. (* (true && true) || (negacion true || negacion true) = true *)
  - reflexivity. (* (true && false) || (negacion true || negacion false) = true *)
  - reflexivity. (* (false && true) || (negacion false || negacion true) = true *)
  - reflexivity. (* (false && false) || (negacion false || negacion false)=true *)
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.10. Demostrar que 
      forall n m p : nat, (n + m) * p = (n * p) + (m * p).
   ------------------------------------------------------------------ *)

Theorem producto_suma_distributiva_d: forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.              (* n, m, p : nat
                                ============================
                                (n + m) * p = n * p + m * p *)
  induction n as [|n' HIn']. 
  -                          (* m, p : nat
                                ============================
                                (0 + m) * p = 0 * p + m * p *)
    reflexivity.
  -                          (* n', m, p : nat
                                HIn' : (n' + m) * p = n' * p + m * p
                                ============================
                                (S n' + m) * p = S n' * p + m * p *)
    simpl.                   (* p + (n' + m) * p = (p + n' * p) + m * p *)
    rewrite HIn'.            (* p + (n' * p + m * p) = (p + n') * p + m * p *)
    rewrite suma_asociativa. (* (p + n' * p) + m * p = (p + n' * p) + m * p *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.11. Demostrar que 
      forall n m p : nat, n * (m * p) = (n * m) * p.
   ------------------------------------------------------------------ *)

Theorem producto_asociativa: forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.     (* n, m, p : nat
                       ============================
                       n * (m * p) = (n * m) * p *)
  induction n as [|n' HIn'].
  -                 (* m, p : nat
                       ============================
                       0 * (m * p) = (0 * m) * p *)
    simpl.          (* 0 = 0 *)
    reflexivity.
  -                 (* n', m, p : nat
                       HIn' : n' * (m * p) = (n' * m) * p
                       ============================
                       S n' * (m * p) = (S n' * m) * p *)
    simpl.          (* m * p + n' * (m * p) = (m + n' * m) * p *)
    rewrite HIn'.   (* m * p + (n' * m) * p = (m + n' * m) * p *)
    rewrite producto_suma_distributiva_d.
                    (* m * p + (n' * m) * p = m * p + (n' * m) * p *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 11. La táctica replace permite especificar el subtérmino
   que se desea reescribir y su sustituto: 
      replace t with u
   sustituye todas las copias de la expresión t en el objetivo por la
   expresión u y añade la ecuación (t = u) como un nuevo subojetivo. 
 
   El uso de la táctica replace es especialmente útil cuando la táctica 
   rewrite actúa sobre una parte del objetivo que no es la que se desea. 

   Demostrar, usando la táctica replace y sin usar 
   [assert (n + m = m + n)], que
      forall n m p : nat, n + (m + p) = m + (n + p).
   ------------------------------------------------------------------ *)

Theorem suma_permutada' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.                 (* n, m, p : nat
                                   ============================
                                   n + (m + p) = m + (n + p) *)
  rewrite suma_asociativa.      (* (n + m) + p = m + (n + p) *)
  rewrite suma_asociativa.      (* (n + m) + p = (m + n) + p *)
  replace (n + m) with (m + n). 
  -                             (* n, m, p : nat
                                   ============================
                                   (m + n) + p = (m + n) + p *)
    reflexivity.
  -                             (* n, m, p : nat
                                   ============================
                                   m + n = n + m *)
    rewrite suma_conmutativa.   (* n + m = n + m *)
    reflexivity.
Qed. 

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Demostraciones por inducción" de Peirce et als. http://bit.ly/2NRSWTF
 *)
