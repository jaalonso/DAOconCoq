(* T5: Tácticas básicas de Coq *)

Set Warnings "-notation-overridden,-parsing".
Require Export T4_PolimorfismoyOS.

(* El contenido del tema es
   1. La táctica 'apply'
   2. La táctica 'apply ... with ...'
   3. La táctica 'inversion'
   4. Uso de tácticas sobre las hipótesis
   5. Control de la hipótesis de inducción  
   6. Expansión de definiciones 
   7. Uso de 'destruct' sobre expresiones compuestas
   8. Ejercicios 
   9. Resumen de tácticas básicas 
*)

(* =====================================================================
   § 1. La táctica 'apply'
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1. Demostrar que 
          n = m  ->
          [n;o] = [n;p] ->
          [n;o] = [m;p].
   ------------------------------------------------------------------ *)

(* Demostración sin apply *)
Theorem artificial_1a : forall (n m o p : nat),
    n = m  ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p H1 H2. (* n, m, o, p : nat
                           H1 : n = m
                           H2 : [n; o] = [n; p]
                           ============================
                           [n; o] = [m; p] *)
  rewrite <- H1.         (* [n; o] = [n; p] *)
  rewrite H2.           (* [n; p] = [n; p] *)
  reflexivity.
Qed.

(* Demostración con apply *)
Theorem artificial_1b : forall (n m o p : nat),
    n = m  ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p H1 H2. (* n, m, o, p : nat
                           H1 : n = m
                           H2 : [n; o] = [n; p]
                           ============================
                           [n; o] = [m; p] *)
  rewrite <- H1.         (* [n; o] = [n; p] *)
  apply H2.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'apply'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 1.2. Demostrar que 
      n = m  ->
      (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
      [n;o] = [m;p].
   ------------------------------------------------------------------ *)

Theorem artificial2 : forall (n m o p : nat),
    n = m  ->
    (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p H1 H2. (* n, m, o, p : nat
                           H1 : n = m
                           H2 : forall q r : nat, q = r -> [q; o] = [r; p]
                           ============================
                           [n; o] = [m; p] *)
  apply H2.             (* n = m *)
  apply H1.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'apply' en hipótesis condicionales y
   razonamiento hacia atrás
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 1.3. Demostrar que 
      (n,n) = (m,m)  ->
      (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
      [n] = [m].
   ------------------------------------------------------------------ *)

Theorem artificial2a : forall (n m : nat),
    (n,n) = (m,m)  ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m H1 H2. (* n, m : nat
                       H1 : (n, n) = (m, m)
                       H2 : forall q r : nat, (q, q) = (r, r) -> [q] = [r]
                       ============================
                       [n] = [m] *)
  apply H2.         (* (n, n) = (m, m) *)
  apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1. Demostrar, sin usar simpl, que
      (forall n, evenb n = true -> oddb (S n) = true) ->
      evenb 3 = true ->
      oddb 4 = true.
   ------------------------------------------------------------------ *)

Theorem artificial_ex :
  (forall n, esPar n = true -> esImpar (S n) = true) ->
  esPar 3 = true ->
  esImpar 4 = true.
Proof.
  intros H1 H2. (* H1 : forall n : nat, esPar n = true -> esImpar (S n) = true
                   H2 : esPar 3 = true
                   ============================
                   esImpar 4 = true *)
  apply H1.     (* esPar 3 = true *)
  apply H2.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.4. Demostrar que 
      true = iguales_nat n 5  ->
      iguales_nat (S (S n)) 7 = true.
   ------------------------------------------------------------------ *)

Theorem artificial3a: forall (n : nat),
    true = iguales_nat n 5  ->
    iguales_nat (S (S n)) 7 = true.
Proof.
  intros n H. (* n : nat
                 H : true = iguales_nat n 5
                 ============================
                 iguales_nat (S (S n)) 7 = true *)
  symmetry.   (* true = iguales_nat (S (S n)) 7 *)
  simpl.      (* true = iguales_nat n 5 *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Nota. Necesidad de usar symmetry antes de apply.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 1.2. Demostrar
      forall (xs ys : list nat), 
       xs = inversa ys -> ys = inversa xs.
   ------------------------------------------------------------------ *)

Theorem inversa2: forall (xs ys : list nat),
    xs = inversa ys -> ys = inversa xs.
Proof.
  intros xs ys H.           (* xs, ys : list nat
                               H : xs = inversa ys
                               ============================
                               ys = inversa xs *)
  rewrite H.                (* ys = inversa (inversa ys) *)
  symmetry.                 (* inversa (inversa ys) = ys *)
  apply inversa_involutiva. 
Qed.

(* =====================================================================
   § 2. La táctica 'apply ... with ...'
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1. Demostrar que
      forall (a b c d e f : nat),
       [a;b] = [c;d] ->
       [c;d] = [e;f] ->
       [a;b] = [e;f].
   ------------------------------------------------------------------ *)

Example ejemplo_con_transitiva: forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2. (* a, b, c, d, e, f : nat
                               H1 : [a; b] = [c; d]
                               H2 : [c; d] = [e; f]
                               ============================
                               [a; b] = [e; f] *)
  rewrite -> H1.             (* [c; d] = [e; f] *)
  rewrite -> H2.             (* [e; f] = [e; f] *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.2. Demostrar que
      forall (X : Type) (n m o : X),
       n = m -> m = o -> n = o.
   ------------------------------------------------------------------ *)

Theorem igualdad_transitiva: forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2. (* X : Type
                           n, m, o : X
                           H1 : n = m
                           H2 : m = o
                           ============================
                           n = o *)
  rewrite -> H1.         (* m = o *)
  rewrite -> H2.         (* o = o *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. El ejercicio 2.2 es una generalización del 2.1, sus
   demostraciones son isomorfas y se puede usar el 2.2 en la
   demostración del 2.1.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.3. Demostrar que
      forall (X : Type) (n m o : X),
       n = m -> m = o -> n = o.
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Example ejemplo_con_transitiva' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.                  (* a, b, c, d, e, f : nat
                                                H1 : [a; b] = [c; d]
                                                H2 : [c; d] = [e; f]
                                                ============================
                                                [a; b] = [e; f] *)
  apply igualdad_transitiva with (m:=[c;d]).
  -                                          (* [a; b] = [c; d] *)
    apply H1.
  -                                          (* [c; d] = [e; f] *)
    apply H2.
Qed.

(* 2ª demostración *)
Example ejemplo_con_transitiva'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.             (* a, b, c, d, e, f : nat
                                           H1 : [a; b] = [c; d]
                                           H2 : [c; d] = [e; f]
                                           ============================
                                           [a; b] = [e; f] *)
  apply igualdad_transitiva with [c;d].
  -                                     (* [a; b] = [c; d] *)
    apply H1.
  -                                     (* [c; d] = [e; f] *)
    apply H2.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'apply ... whith ...'
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 2.1. Demostrar que
      forall (n m o p : nat),
        m = (menosDos o) ->
        (n + p) = m ->
        (n + p) = (menosDos o).
   ------------------------------------------------------------------ *)

Example ejercicio_igualdad_transitiva: forall (n m o p : nat),
    m = (menosDos o) ->
    (n + p) = m ->
    (n + p) = (menosDos o).
Proof.
  intros n m o p H1 H2.             (* n, m, o, p : nat
                                       H1 : m = menosDos o
                                       H2 : n + p = m
                                       ============================
                                       n + p = menosDos o *)
  apply igualdad_transitiva with m. 
  -                                 (* n + p = m *)
    apply H2.
  -                                 (* m = menosDos o *)
    apply H1.
Qed.

(* =====================================================================
   § 3. La táctica 'inversion'
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 3.1. Demostrar que
      forall (n m : nat),
       S n = S m -> n = m.
   ------------------------------------------------------------------ *)

Theorem S_inyectiva: forall (n m : nat),
  S n = S m ->
  n = m.
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
   Nota. Uso de la táctica 'inversion'
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 3.2. Demostrar que
      forall (n m o : nat),
       [n; m] = [o; o] -> [n] = [m].
   ------------------------------------------------------------------ *)

Theorem inversion_ej1: forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H. (* n, m, o : nat
                     H : [n; m] = [o; o]
                     ============================
                     [n] = [m] *)
  inversion H.    (* n, m, o : nat
                     H : [n; m] = [o; o]
                     H1 : n = o
                     H2 : m = o
                     ============================
                     [o] = [o] *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.3. Demostrar que
      forall (n m : nat),
       [n] = [m] ->
       n = m.
   ------------------------------------------------------------------ *)

Theorem inversion_ej2: forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
  intros n m H.         (* n, m : nat
                           H : [n] = [m]
                           ============================
                           n = m *)
  inversion H as [Hnm]. (* n, m : nat
                           H : [n] = [m]
                           Hnm : n = m
                           ============================
                           m = m *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Nombramiento de las hipótesis generadas por inversión.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 3.1. Demostrar que
      forall (X : Type) (x y z : X) (xs ys : list X),
        x :: y :: xs = z :: ys ->
        y :: xs = x :: ys ->
        x = y.
   ------------------------------------------------------------------ *)

Example inversion_ej3 : forall (X : Type) (x y z : X) (xs ys : list X),
  x :: y :: xs = z :: ys ->
  y :: xs = x :: ys ->
  x = y.
Proof.
  intros X x y z xs ys H1 H2. (* X : Type
                                 x, y, z : X
                                 xs, ys : list X
                                 H1 : x :: y :: xs = z :: ys
                                 H2 : y :: xs = x :: ys
                                 ============================
                                 x = y *)
  inversion H1.               (* X : Type
                                 x, y, z : X
                                 xs, ys : list X
                                 H1 : x :: y :: xs = z :: ys
                                 H2 : y :: xs = x :: ys
                                 H0 : x = z
                                 H3 : y :: xs = ys
                                 ============================
                                 z = y *)
  inversion H2.               (* xs, ys : list X
                                 H1 : x :: y :: xs = z :: ys
                                 H2 : y :: xs = x :: ys
                                 H0 : x = z
                                 H3 : y :: xs = ys
                                 H4 : y = x
                                 H5 : xs = ys
                                 ============================
                                 z = x *)
  symmetry.                   (* x = z *)
  apply H0.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.4. Demostrar que
      forall n:nat,
       iguales_nat 0 n = true -> n = 0.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_0_n: forall n:nat,
    iguales_nat 0 n = true -> n = 0.
Proof.
  intros n.             (* n : nat
                           ============================
                           iguales_nat 0 n = true -> n = 0 *)
  destruct n as [| n']. 
  -                     (* 
                           ============================
                           iguales_nat 0 0 = true -> 0 = 0 *)
    intros H.           (* H : iguales_nat 0 0 = true
                           ============================
                           0 = 0 *)
    reflexivity.
  -                     (* n' : nat
                           ============================
                           iguales_nat 0 (S n') = true -> S n' = 0 *)
    simpl.              (* n' : nat
                           ============================
                           false = true -> S n' = 0 *)
    intros H.           (* n' : nat
                           H : false = true
                           ============================
                           S n' = 0 *)
    inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.5. Demostrar que
      forall (n : nat),
       S n = O -> 2 + 2 = 5.
   ------------------------------------------------------------------ *)

Theorem inversion_ej4: forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n H.  (* n : nat
                  H : S n = 0
                  ============================
                  2 + 2 = 5 *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.6. Demostrar que
      forall (n m : nat),
       false = true -> [n] = [m].
   ------------------------------------------------------------------ *)

Theorem inversion_ej5: forall (n m : nat),
    false = true -> [n] = [m].
Proof.
  intros n m H. (* n, m : nat
                   H : false = true
                   ============================
                   [n] = [m] *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.2. Demostrar que
      forall (X : Type) (x y z : X) (xs ys : list X),
        x :: y :: xs = [] ->
        y :: xs = z :: ys ->
        x = z.
   ------------------------------------------------------------------ *)

Example inversion_ej6 :
  forall (X : Type) (x y z : X) (xs ys : list X),
    x :: y :: xs = [] ->
    y :: xs = z :: ys ->
    x = z.
Proof.
  intros X x y z xs ys H. (* X : Type
                             x, y, z : X
                             xs, ys : list X
                             H : x :: y :: xs = [ ]
                             ============================
                             y :: xs = z :: ys -> x = z *)
  inversion H.
Qed.  

(* ---------------------------------------------------------------------
   Ejemplo 3.7. Demostrar que
      forall (A B : Type) (f: A -> B) (x y: A),
       x = y -> f x = f y.
   ------------------------------------------------------------------ *)

Theorem funcional: forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros A B f x y H. (* A : Type
                         B : Type
                         f : A -> B
                         x, y : A
                         H : x = y
                         ============================
                         f x = f y *)
  rewrite H.          (* f y = f y *)
  reflexivity.
Qed.

(* =====================================================================
   § 4. Uso de tácticas sobre las hipótesis
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1. Demostrar que
      forall (n m : nat) (b : bool),
       iguales_nat (S n) (S m) = b  ->
       iguales_nat n m = b.
   ------------------------------------------------------------------ *)

Theorem S_inj: forall (n m : nat) (b : bool),
    iguales_nat (S n) (S m) = b  ->
    iguales_nat n m = b.
Proof.
  intros n m b H. (* n, m : nat
                     b : bool
                     H : iguales_nat (S n) (S m) = b
                     ============================
                     iguales_nat n m = b *)
  simpl in H.     (* n, m : nat
                     b : bool
                     H : iguales_nat n m = b
                     ============================
                     iguales_nat n m = b *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de táctica 'simpl in ...'
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1. Demostrar que
      forall (n : nat),
       (iguales_nat n 5 = true -> iguales_nat (S (S n)) 7 = true) ->
       true = iguales_nat n 5  ->
       true = iguales_nat (S (S n)) 7.
   ------------------------------------------------------------------ *)

Theorem artificial3': forall (n : nat),
  (iguales_nat n 5 = true -> iguales_nat (S (S n)) 7 = true) ->
  true = iguales_nat n 5  ->
  true = iguales_nat (S (S n)) 7.
Proof.
  intros n H1 H2. (* n : nat
                     H1 : iguales_nat n 5 = true -> 
                          iguales_nat (S (S n)) 7 = true
                     H2 : true = iguales_nat n 5
                     ============================
                     true = iguales_nat (S (S n)) 7 *)
  symmetry in H2. (* n : nat
                     H1 : iguales_nat n 5 = true -> 
                          iguales_nat (S (S n)) 7 = true
                     H2 : iguales_nat n 5 = true
                     ============================
                     true = iguales_nat (S (S n)) 7 *)
  apply H1 in H2. (* n : nat
                     H1 : iguales_nat n 5 = true -> 
                          iguales_nat (S (S n)) 7 = true
                     H2 : iguales_nat (S (S n)) 7 = true
                     ============================
                     true = iguales_nat (S (S n)) 7 *)
  symmetry in H2. (* n : nat
                     H1 : iguales_nat n 5 = true -> 
                          iguales_nat (S (S n)) 7 = true
                     H2 : true = iguales_nat (S (S n)) 7
                     ============================
                     true = iguales_nat (S (S n)) 7 *)
  apply H2.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de las tácticas 'apply H1 in H2' y 'symemetry in H'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 4.1. Demostrar
      forall n m : nat,
        n + n = m + m ->
        n = m.

   Nota: Usar suma_s_Sm.
   ------------------------------------------------------------------ *)

Theorem suma_n_n_inyectiva:
  forall n m : nat,
    n + n = m + m ->
    n = m.
Proof.
  intros n.                      (* n : nat
                                    ============================
                                    forall m : nat, n + n = m + m -> n = m *)
  induction n as [| n' HI]. 
  -                              (* 
                                    ============================
                                    forall m : nat, 0 + 0 = m + m -> 0 = m *)
    intros m H1.                 (* m : nat
                                    H1 : 0 + 0 = m + m
                                    ============================
                                    0 = m *)
    destruct m.
    +                            (* H1 : 0 + 0 = 0 + 0
                                    ============================
                                    0 = 0 *)
      reflexivity.
    +                            (* m : nat
                                    H1 : 0 + 0 = S m + S m
                                    ============================
                                    0 = S m *)
      inversion H1.
  -                              (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m
                                                         -> n' = m
                                    ============================
                                    forall m : nat, S n' + S n' = m + m 
                                                    -> S n' = m *)
    intros m H2.                 (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = m + m
                                    ============================
                                    S n' = m *)
    destruct m.
    +                            (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    H2 : S n' + S n' = 0 + 0
                                    ============================
                                    S n' = 0 *)
      inversion H2.
    +                            (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    ============================
                                    S n' = S m *)
      inversion H2.              (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : n' + S n' = m + S m
                                    ============================
                                    S n' = S m *)
      rewrite <- suma_n_Sm in H0. (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (n' + n') = m + S m
                                    ============================
                                    S n' = S m *)
      symmetry in H0.            (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : m + S m = S (n' + n')
                                    ============================
                                    S n' = S m *)
      rewrite <- suma_n_Sm in H0. (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (m + m) = S (n' + n')
                                    ============================
                                    S n' = S m *)
      inversion H0.              (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (m + m) = S (n' + n')
                                    H1 : m + m = n' + n'
                                    ============================
                                    S n' = S m *)
      symmetry in H1.            (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (m + m) = S (n' + n')
                                    H1 : n' + n' = m + m
                                    ============================
                                    S n' = S m *)
      apply HI in H1.            (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (m + m) = S (n' + n')
                                    H1 : n' = m
                                    ============================
                                    S n' = S m *)
      rewrite <- H1.             (* n' : nat
                                    HI : forall m : nat, n' + n' = m + m 
                                                         -> n' = m
                                    m : nat
                                    H2 : S n' + S n' = S m + S m
                                    H0 : S (m + m) = S (n' + n')
                                    H1 : n' = m
                                    ============================
                                    S n' = S n' *)
      reflexivity.
Qed.    

(* =====================================================================
   § 5. Control de la hipótesis de inducción  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.1. Demostrar que
      forall n m : nat,
       doble n = doble m -> n = m.
   ------------------------------------------------------------------ *)

(* 1ª intento *)
Theorem doble_inyectiva_FAILED : forall n m : nat,
    doble n = doble m ->
    n = m.
Proof.
  intros n m.             (* n, m : nat
                             ============================
                             doble n = doble m -> n = m *)
  induction n as [| n' HI].
  -                       (* m : nat
                             ============================
                             doble 0 = doble m -> 0 = m *)
    simpl.                (* m : nat
                             ============================
                             0 = doble m -> 0 = m *)
    intros H.             (* m : nat
                             H : 0 = doble m
                             ============================
                             0 = m *)
    destruct m as [| m']. 
    +                     (* H : 0 = doble 0
                             ============================
                             0 = 0 *)
      reflexivity.
    +                     (* m' : nat
                             H : 0 = doble (S m')
                             ============================
                             0 = S m' *)
      inversion H.
  -                       (* n', m : nat
                             HI : doble n' = doble m -> n' = m
                             ============================
                             doble (S n') = doble m -> S n' = m *)
    intros H.             (* n', m : nat
                             HI : doble n' = doble m -> n' = m
                             H : doble (S n') = doble m
                             ============================
                             S n' = m *)
    destruct m as [| m'].
    +                     (* n' : nat
                             HI : doble n' = doble 0 -> n' = 0
                             H : doble (S n') = doble 0
                             ============================
                             S n' = 0 *)
      simpl in H.         (* n' : nat
                             HI : doble n' = doble 0 -> n' = 0
                             H : S (S (doble n')) = 0
                             ============================
                             S n' = 0 *)
      inversion H.
    +                     (* n', m' : nat
                             HI : doble n' = doble (S m') -> n' = S m'
                             H : doble (S n') = doble (S m')
                             ============================
                             S n' = S m' *)
      apply funcional.    (* n', m' : nat
                             HI : doble n' = doble (S m') -> n' = S m'
                             H : doble (S n') = doble (S m')
                             ============================
                             n' = m' *)
      Abort.

(* 2º intento *)
Theorem doble_inyectiva: forall n m,
    doble n = doble m ->
    n = m.
Proof.
  intros n.               (* n : nat
                             ============================
                             forall m : nat, doble n = doble m -> n = m *)
  induction n as [| n' HI].
  -                       (* 
                             ============================
                             forall m : nat, doble 0 = doble m -> 0 = m *)
    simpl.                (* forall m : nat, 0 = doble m -> 0 = m *)
    intros m H.           (* m : nat
                             H : 0 = doble m
                             ============================
                             0 = m *)
    destruct m as [| m'].
    +                     (* H : 0 = doble 0
                             ============================
                             0 = 0 *)
      reflexivity.
    +                     (* m' : nat
                             H : 0 = doble (S m')
                             ============================
                             0 = S m' *)
      inversion H.
  -                       (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             ============================
                             forall m : nat, doble (S n') = doble m 
                                             -> S n' = m *)
    simpl.                (* forall m : nat, S (S (doble n')) = doble m 
                                             -> S n' = m *)
    intros m H.           (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             m : nat
                             H : S (S (doble n')) = doble m
                             ============================
                             S n' = m *)
    destruct m as [| m']. 
    +                     (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             H : S (S (doble n')) = doble 0
                             ============================
                             S n' = 0 *)
      simpl in H.         (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             H : S (S (doble n')) = 0
                             ============================
                             S n' = 0 *)
      inversion H.
    +                     (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             m' : nat
                             H : S (S (doble n')) = doble (S m')
                             ============================
                             S n' = S m' *)
      apply funcional.    (* n' = m' *)
      apply HI.           (* doble n' = doble m' *)
      inversion H.        (* n' : nat
                             HI : forall m : nat, doble n' = doble m -> n' = m
                             m' : nat
                             H : S (S (doble n')) = doble (S m')
                             H1 : doble n' = doble m'
                             ============================
                             doble n' = doble n' *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la estrategia de generalización.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 5.1. Demostrar que
      forall n m : nat,
        iguales_nat n m = true -> n = m.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_true : forall n m : nat,
    iguales_nat n m = true -> n = m.
Proof.
  induction n as [|n' HIn'].
  -                             (* 
                                   ============================
                                   forall m : nat, iguales_nat 0 m = true 
                                              -> 0 = m *)
    induction m as [|m' HIm'].
    +                           (* 
                                   ============================
                                   iguales_nat 0 0 = true -> 0 = 0 *)
      reflexivity.
    +                           (* m' : nat
                                   HIm' : iguales_nat 0 m' = true -> 0 = m'
                                   ============================
                                   iguales_nat 0 (S m') = true -> 0 = S m' *)
      simpl.                    (* false = true -> 0 = S m' *)
      intros H.                 (* m' : nat
                                   HIm' : iguales_nat 0 m' = true -> 0 = m'
                                   H : false = true
                                   ============================
                                   0 = S m' *)
      inversion H.
  -                             (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                         -> n' = m
                                   ============================
                                   forall m : nat, iguales_nat (S n') m = true
                                                   -> S n' = m *)
    induction m as [|m' HIm'].
    +                           (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                         -> n' = m
                                   ============================
                                   iguales_nat (S n') 0 = true -> S n' = 0 *)
      simpl.                    (* false = true -> S n' = 0 *)
      intros H.                 (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                        -> n' = m
                                   H : false = true
                                   ============================
                                   S n' = 0 *)
      inversion H.
    +                           (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                         -> n' = m
                                   m' : nat
                                   HIm' : iguales_nat (S n') m' = true 
                                          -> S n' = m'
                                   ============================
                                   iguales_nat (S n') (S m') = true 
                                   -> S n' = S m' *)
      simpl.                    (* iguales_nat n' m' = true -> S n' = S m' *)
      intros H.                 (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                         -> n' = m
                                   m' : nat
                                   HIm' : iguales_nat (S n') m' = true 
                                          -> S n' = m'
                                   H : iguales_nat n' m' = true
                                   ============================
                                   S n' = S m' *)
      apply HIn' in H.          (* n' : nat
                                   HIn' : forall m:nat, iguales_nat n' m = true
                                                         -> n' = m
                                   m' : nat
                                   HIm' : iguales_nat (S n') m' = true 
                                          -> S n' = m'
                                   H : n' = m'
                                   ============================
                                   S n' = S m' *)
      rewrite H.                (* S m' = S m' *)
      reflexivity.
Qed.
    
(* ---------------------------------------------------------------------
   Ejemplo 5.2. Demostrar que
      forall n m : nat,
       doble n = doble m ->
       n = m.
   ------------------------------------------------------------------ *)

(* 1º intento *)
Theorem doble_inyectiva_2a: forall n m : nat,
    doble n = doble m ->
    n = m.
Proof.
  intros n m.                   (* n, m : nat
                                   ============================
                                   doble n = doble m -> n = m *)
  induction m as [| m' HI].
  -                             (* n : nat
                                   ============================
                                   doble n = doble 0 -> n = 0 *)
    simpl.                      (* doble n = 0 -> n = 0 *)
    intros H.                   (* n : nat
                                   H : doble n = 0
                                   ============================
                                   n = 0 *)
    destruct n as [| n'].
    +                           (* H : doble 0 = 0
                                   ============================
                                   0 = 0 *)
      reflexivity.
    +                           (* n' : nat
                                   H : doble (S n') = 0
                                   ============================
                                   S n' = 0 *)
      simpl in H.               (* n' : nat
                                   H : S (S (doble n')) = 0
                                   ============================
                                   S n' = 0 *)
      inversion H.
  -                             (* n, m' : nat
                                   HI : doble n = doble m' -> n = m'
                                   ============================
                                   doble n = doble (S m') -> n = S m' *)

    intros H.                   (* n, m' : nat
                                   HI : doble n = doble m' -> n = m'
                                   H : doble n = doble (S m')
                                   ============================
                                   n = S m' *)
    destruct n as [| n']. 
    +                           (* m' : nat
                                   HI : doble 0 = doble m' -> 0 = m'
                                   H : doble 0 = doble (S m')
                                   ============================
                                   0 = S m' *)
      simpl in H.               (* m' : nat
                                   HI : doble 0 = doble m' -> 0 = m'
                                   H : 0 = S (S (doble m'))
                                   ============================
                                   0 = S m' *)
      inversion H.
    +                           (* n', m' : nat
                                   HI : doble (S n') = doble m' -> S n' = m'
                                   H : doble (S n') = doble (S m')
                                   ============================
                                   S n' = S m' *)
      apply funcional.          (* n' = m' *)
Abort.

(* 2º intento *)
Theorem doble_inyectiva_2 : forall n m,
    doble n = doble m ->
    n = m.
Proof.
  intros n m.               (* n, m : nat
                               ============================
                               doble n = doble m -> n = m *)
  generalize dependent n.   (* m : nat
                               ============================
                               forall n : nat, doble n = doble m -> n = m *)
  induction m as [| m' HI]. 
  -                         (*  
                               ============================
                               forall n : nat, doble n = doble 0 -> n = 0 *)
    simpl.                  (* forall n : nat, doble n = 0 -> n = 0 *)
    intros n H.             (* n : nat
                               H : doble n = 0
                               ============================
                               n = 0 *)
    destruct n as [| n'].
    +                       (* H : doble 0 = 0
                               ============================
                               0 = 0 *)
      reflexivity.
    +                       (* n' : nat
                               H : doble (S n') = 0
                               ============================
                               S n' = 0 *)
      simpl in H.           (* n' : nat
                               H : S (S (doble n')) = 0
                               ============================
                               S n' = 0 *)
      inversion H.
  -                         (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               ============================
                               forall n : nat, doble n = doble (S m') 
                                               -> n = S m' *)
    intros n H.             (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               n : nat
                               H : doble n = doble (S m')
                               ============================
                               n = S m' *)
    destruct n as [| n']. 
    +                       (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               H : doble 0 = doble (S m')
                               ============================
                               0 = S m' *)
      simpl in H.           (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               H : 0 = S (S (doble m'))
                               ============================
                               0 = S m' *)
      inversion H.
    +                       (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               n' : nat
                               H : doble (S n') = doble (S m')
                               ============================
                               S n' = S m' *)
      apply funcional.      (* n' = m' *)
      apply HI.             (* doble n' = doble m' *)
      simpl in H.           (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               n' : nat
                               H : S (S (doble n')) = S (S (doble m'))
                               ============================
                               doble n' = doble m' *)
      inversion H.          (* m' : nat
                               HI : forall n : nat, doble n = doble m' -> n = m'
                               n' : nat
                               H : S (S (doble n')) = S (S (doble m'))
                               H1 : doble n' = doble m'
                               ============================
                               doble n' = doble n' *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'generalize dependent n'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 5.3. Demostrar que
      forall x y : id,
       iguales_id x y = true -> x = y.
   ------------------------------------------------------------------ *)

Theorem iguales_id_true: forall x y : id,
  iguales_id x y = true -> x = y.
Proof.
  intros [m] [n].           (* m, n : nat
                               ============================
                               iguales_id (Id m) (Id n) = true -> Id m = Id n *)
  simpl.                    (* iguales_nat m n = true -> Id m = Id n *)
  intros H.                 (* m, n : nat
                               H : iguales_nat m n = true
                               ============================
                               Id m = Id n *)
  assert (H' : m = n).
  -                         (* m, n : nat
                               H : iguales_nat m n = true
                               ============================
                               m = n *)
    apply iguales_nat_true. (* iguales_nat m n = true *)
    apply H. 
  -                         (* m, n : nat
                               H : iguales_nat m n = true
                               H' : m = n
                               ============================
                               Id m = Id n *)
    rewrite H'.             (* Id n = Id n *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2. Demostrar, por inducción sobre l,
      forall (n : nat) (X : Type) (xs : list X),
        longitud xs = n ->
        nthOpcional xs n = None.
   ------------------------------------------------------------------ *)

Theorem nthOpcional_None: forall (n : nat) (X : Type) (xs : list X),
    longitud xs = n ->
    nthOpcional xs n = None.
Proof.
  intros n X xs.               (* n : nat
                                  X : Type
                                  xs : list X
                                  ============================
                                  longitud xs = n -> nthOpcional xs n = None *)
  generalize dependent n.       (* X : Type
                                  xs : list X
                                  ============================
                                  forall n : nat, 
                                   longitud xs = n -> nthOpcional xs n = None *)
  induction xs as [|x xs' HI]. 
  -                             (* X : Type
                                  ============================
                                  forall n : nat, 
                                   longitud [] = n -> nthOpcional [] n = None *)
    reflexivity.
  -                             (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  ============================
                                  forall n : nat, 
                                   longitud (x :: xs') = n -> 
                                   nthOpcional (x :: xs') n = None *)
    destruct n as [|n'].
    +                           (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  ============================
                                  longitud (x :: xs') = 0 -> 
                                  nthOpcional (x :: xs') 0 = None *)
      intros H.                 (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  H : longitud (x :: xs') = 0
                                  ============================
                                  nthOpcional (x :: xs') 0 = None *)
      simpl in H.               (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  H : S (longitud xs') = 0
                                  ============================
                                  nthOpcional (x :: xs') 0 = None *)
      inversion H.
    +                           (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  n' : nat
                                  ============================
                                  longitud (x :: xs') = S n' -> 
                                  nthOpcional (x :: xs') (S n') = None *)
      simpl.                    (* S (longitud xs') = S n' -> 
                                   nthOpcional xs' n' = None *)
      intros H.                 (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  n' : nat
                                  H : S (longitud xs') = S n'
                                  ============================
                                  nthOpcional xs' n' = None *)
      apply HI.                 (* longitud xs' = n' *)
      inversion H.              (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : forall n : nat, 
                                        longitud xs' = n -> 
                                        nthOpcional xs' n = None
                                  n' : nat
                                  H : S (longitud xs') = S n'
                                  H1 : longitud xs' = n'
                                  ============================
                                  longitud xs' = longitud xs' *)
      reflexivity.
Qed.

(* =====================================================================
   § 6. Expansión de definiciones 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 6.1. Definir la función
      cuadrado : nata -> nat
   tal que (cuadrado n) es el cuadrado de n.
   ------------------------------------------------------------------ *)

Definition cuadrado (n:nat) : nat := n * n.

(* ---------------------------------------------------------------------
   Ejemplo 6.2. Demostrar que
      forall n m : nat,
       cuadrado (n * m) = cuadrado n * cuadrado m.
   ------------------------------------------------------------------ *)

Lemma cuadrado_mult : forall n m : nat,
    cuadrado (n * m) = cuadrado n * cuadrado m.
Proof.
  intros n m.                            (* n, m : nat
                                            ============================
                                            cuadrado (n * m) = 
                                            cuadrado n * cuadrado m *)
  unfold cuadrado.                       (* (n * m) * (n * m) = 
                                            (n * n) * (m * m) *)
  rewrite producto_asociativa.           (* ((n * m) * n) * m = 
                                            (n * n) * (m * m) *)
  assert (H : (n * m) * n = (n * n) * m). 
  -                                      (* (n * m) * n = (n * n) * m) *)
    rewrite producto_conmutativa.        (* n * (n * m) = (n * n) * m *)
    apply producto_asociativa.           
  -                                      (* n, m : nat
                                            H : (n * m) * n = (n * n) * m
                                            ============================
                                            ((n * m) * n) * m = 
                                            (n * n) * (m * m) *)
    rewrite H.                           (* ((n * n) * m) * m = 
                                            (n * n) * (m * m) *)
    rewrite producto_asociativa.         (* ((n * n) * m) * m = 
                                            ((n * n) * m) * m *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'unfold'
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 6.4. Definir la función
      const5 : nat -> nat
   tal que (const5 x) es el número 5.
   ------------------------------------------------------------------ *)

Definition const5 (x: nat) : nat := 5.

(* ---------------------------------------------------------------------
   Ejemplo 6.5. Demostrar que
      forall m : nat,
       const5 m + 1 = const5 (m + 1) + 1.
   ------------------------------------------------------------------ *)

Fact prop_const5 : forall m : nat,
    const5 m + 1 = const5 (m + 1) + 1.
Proof.
  intros m.    (* m : nat
                  ============================
                  const5 m + 1 = const5 (m + 1) + 1 *)
  simpl.       (* 6 = 6 *)
  reflexivity. 
Qed.

(* ---------------------------------------------------------------------
   Nota. Expansión automática de la definición de const5.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 6.6. Se coonsidera la siguiente definición
      Definition const5b (x:nat) : nat :=
        match x with
        | O   => 5
        | S _ => 5
        end.

   Demostrar que
      forall m : nat,
       const5b m + 1 = const5b (m + 1) + 1.
   ------------------------------------------------------------------ *)

Definition const5b (x:nat) : nat :=
  match x with
  | O   => 5
  | S _ => 5
  end.

(* 1º intento *)
Fact prop_const5b_1: forall m : nat,
    const5b m + 1 = const5b (m + 1) + 1.
Proof.
  intros m. (* m : nat
               ============================
               const5b m + 1 = const5b (m + 1) + 1 *)
  simpl.    (* const5b m + 1 = const5b (m + 1) + 1 *)
Abort.

(* 1ª demostración *)
Fact prop_const5b_2: forall m : nat,
    const5b m + 1 = const5b (m + 1) + 1.
Proof.
  intros m.      (* m : nat
                    ============================
                    const5b m + 1 = const5b (m + 1) + 1 *)
  destruct m.
  -              (* 
                    ============================
                    const5b 0 + 1 = const5b (0 + 1) + 1 *)
    simpl.       (* 6 = 6 *)
    reflexivity. 
  -              (* m : nat
                    ============================
                    const5b (S m) + 1 = const5b (S m + 1) + 1 *)
    simpl.       (* 6 = 6 *)
    reflexivity.
Qed.

(* 2ª demostración *)
Fact prop_const5b_3: forall m : nat,
    const5b m + 1 = const5b (m + 1) + 1.
Proof.
  intros m.       (* m : nat
                     ============================
                     const5b m + 1 = const5b (m + 1) + 1 *)
  unfold const5b. (* m : nat
                     ============================
                     match m with
                     | 0 | _ => 5
                     end + 1 = match m + 1 with
                               | 0 | _ => 5
                               end + 1 *)
  destruct m.
  -               (* 
                     ============================
                     5 + 1 = match 0 + 1 with
                             | 0 | _ => 5
                             end + 1 *)
    reflexivity.
  -               (* m : nat
                     ============================
                     5 + 1 = match S m + 1 with
                             | 0 | _ => 5
                             end + 1 *)
    reflexivity.
Qed.

(* =====================================================================
   § 7. Uso de 'destruct' sobre expresiones compuestas
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 7.1. Se considera la siguiente definición 
      Definition const_false (n : nat) : bool :=
        if      iguales_nat n 3 then false
        else if iguales_nat n 5 then false
        else                         false.

   Demostrar que
      forall n : nat,
       const_false n = false.
   ------------------------------------------------------------------ *)

Definition const_false (n : nat) : bool :=
  if      iguales_nat n 3 then false
  else if iguales_nat n 5 then false
  else                         false.

Theorem const_false_false : forall n : nat,
    const_false n = false.
Proof.
  intros n.                     (* n : nat
                                   ============================
                                   const_false n = false *)
  unfold const_false.           (* (if iguales_nat n 3 then false 
                                   else if iguales_nat n 5 then false 
                                   else false) =
                                   false *)
  destruct (iguales_nat n 3).
  -                             (* n : nat
                                   ============================
                                   false = false *)
    reflexivity.
  -                             (* n : nat
                                   ============================
                                   (if iguales_nat n 5 then false 
                                   else false) = false *)
    destruct (iguales_nat n 5). 
    +                           (* n : nat
                                   ============================
                                   false = false *)
      reflexivity.
    +                           (* n : nat
                                   ============================
                                   false = false *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 7.2. Se considera la siguiente definición 
      Definition ej (n : nat) : bool :=
        if      iguales_nat n 3 then true
        else if iguales_nat n 5 then true
        else                     false.

   Demostrar que
      forall n : nat,
       ej n = true -> esImpar n = true.
   ------------------------------------------------------------------ *)

Definition ej (n : nat) : bool :=
  if      iguales_nat n 3 then true
  else if iguales_nat n 5 then true
  else                     false.

(* 1º intento *)
Theorem ej_impar_a: forall n : nat,
    ej n = true ->
    esImpar n = true.
Proof.
  intros n H.                       (* n : nat
                                       H : ej n = true
                                       ============================
                                       esImpar n = true *)
  unfold ej in H. (* n : nat
                                      H : (if iguales_nat n 3
                                           then true
                                           else if iguales_nat n 5 
                                                then true 
                                                else false) 
                                          = true
                                      ============================
                                      esImpar n = true *)
  destruct (iguales_nat n 3).
  -                                (* n : nat
                                      H : true = true
                                      ============================
                                      esImpar n = true *)
Abort.

(* 2º intento *)
Theorem ej_impar : forall n : nat,
    ej n = true ->
    esImpar n = true.
Proof.
  intros n H.                             (* n : nat
                                             H : ej n = true
                                             ============================
                                             esImpar n = true *)
  unfold ej in H.                         (* n : nat
                                             H : (if iguales_nat n 3
                                                  then true
                                                  else if iguales_nat n 5 
                                                       then true else false) 
                                                 = true
                                             ============================
                                             esImpar n = true *)
  destruct (iguales_nat n 3) eqn: H3.
  -                                       (* n : nat
                                             H3 : iguales_nat n 3 = true
                                             H : true = true
                                             ============================
                                             esImpar n = true *)
    apply iguales_nat_true in H3.         (* n : nat
                                             H3 : n = 3
                                             H : true = true
                                             ============================
                                             esImpar n = true *)
    rewrite H3.                           (* esImpar 3 = true *)
    reflexivity.
  -                                       (* n : nat
                                             H3 : iguales_nat n 3 = false
                                             H : (if iguales_nat n 5 
                                                  then true else false) 
                                                 = true
                                             ============================
                                             esImpar n = true *)
    destruct (iguales_nat n 5) eqn:H5. 
    +                                     (* n : nat
                                             H3 : iguales_nat n 3 = false
                                             H5 : iguales_nat n 5 = true
                                             H : true = true
                                             ============================
                                             esImpar n = true *)
      apply iguales_nat_true in H5.       (* n : nat
                                             H3 : iguales_nat n 3 = false
                                             H5 : n = 5
                                             H : true = true
                                             ============================
                                             esImpar n = true *)
      rewrite H5.                         (* esImpar 5 = true *)
      reflexivity.
    +                                     (* n : nat
                                             H3 : iguales_nat n 3 = false
                                             H5 : iguales_nat n 5 = false
                                             H : false = true
                                             ============================
                                             esImpar n = true *)
      inversion H.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de la táctica 'destruct e eqn: H'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 7.1. Demostrar que desempareja y empareja son inversas; es decir,
        forall X Y (ps : list (X * Y)) xs ys,
          desempareja ps = (xs, ys) ->
          empareja xs ys = ps.
   ------------------------------------------------------------------ *)

Theorem empareja_desempareja: forall X Y (ps : list (X * Y)) xs ys,
    desempareja ps = (xs, ys) ->
    empareja xs ys = ps.
Proof.
  intros X Y ps.                       (* X : Type
                                          Y : Type
                                          ps : list (X * Y)
                                          ============================
                                          forall (xs : list X) (ys : list Y),
                                           desempareja ps = (xs, ys) -> 
                                           empareja xs ys = ps *)
  induction ps as [|(x,y) ps' HI].
  -                                    (* X : Type
                                          Y : Type
                                          ============================
                                          forall (xs : list X) (ys : list Y),
                                           desempareja [ ] = (xs, ys) -> 
                                           empareja xs ys = [ ] *)
    intros xs ys H.                    (* X : Type
                                          Y : Type
                                          xs : list X
                                          ys : list Y
                                          H : desempareja [ ] = (xs, ys)
                                          ============================
                                          empareja xs ys = [ ] *)
    simpl in H.                        (* X : Type
                                          Y : Type
                                          xs : list X
                                          ys : list Y
                                          H : ([ ], [ ]) = (xs, ys)
                                          ============================
                                          empareja xs ys = [ ] *)
    inversion H.                       (* X : Type
                                          Y : Type
                                          xs : list X
                                          ys : list Y
                                          H : ([ ], [ ]) = (xs, ys)
                                          H1 : [ ] = xs
                                          H2 : [ ] = ys
                                          ============================
                                          empareja [ ] [ ] = [ ] *)
    simpl.                             (* [ ] = [ ] *)
    reflexivity.
  -                                    (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          HI : forall (xs:list X) (ys:list Y),
                                               desempareja ps' = (xs, ys) 
                                               -> empareja xs ys = ps'
                                          ============================
                                          forall (xs : list X) (ys : list Y),
                                           desempareja ((x,y)::ps') = (xs,ys) 
                                           -> empareja xs ys = (x,y)::ps' *)
    intros xs ys H.                    (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          HI : forall (xs:list X) (ys:list Y),
                                               desempareja ps' = (xs, ys) -> 
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : desempareja ((x,y)::ps') = (xs,ys)
                                          ============================
                                          empareja xs ys = (x, y) :: ps' *)
    destruct (desempareja ps') eqn: E. (* Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs:list X) (ys:list Y),
                                               (l, l0) = (xs, ys) -> 
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : desempareja ((x,y)::ps') = (xs,ys)
                                          ============================
                                          empareja xs ys = (x, y) :: ps' *)
    simpl in H.                        (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs: ist X) (ys:list Y),
                                               (l, l0) = (xs, ys) ->
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : match desempareja ps' with
                                              | (xs, ys) => (x :: xs, y :: ys)
                                              end = (xs, ys)
                                          ============================
                                          empareja xs ys = (x, y) :: ps' *)
    rewrite E in H.                    (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs:list X) (ys:list Y),
                                               (l, l0) = (xs, ys) ->
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : (x :: l, y :: l0) = (xs, ys)
                                          ============================
                                          empareja xs ys = (x, y) :: ps' *)
    inversion H.                       (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs:list X) (ys:list Y),
                                               (l, l0) = (xs, ys) ->
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : (x :: l, y :: l0) = (xs, ys)
                                          H1 : x :: l = xs
                                          H2 : y :: l0 = ys
                                          ============================
                                          empareja (x :: l) (y :: l0) = 
                                          (x, y) :: ps' *)
    simpl.                             (* (x, y) :: empareja l l0 = 
                                          (x, y) :: ps' *)
    rewrite HI.
    +                                  (* X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs:list X) (ys:list Y),
                                               (l, l0) = (xs, ys) ->
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : (x :: l, y :: l0) = (xs, ys)
                                          H1 : x :: l = xs
                                          H2 : y :: l0 = ys
                                          ============================
                                          (x, y) :: ps' = (x, y) :: ps' *)
      reflexivity.
    +                                  (*   X : Type
                                          Y : Type
                                          x : X
                                          y : Y
                                          ps' : list (X * Y)
                                          l : list X
                                          l0 : list Y
                                          E : desempareja ps' = (l, l0)
                                          HI : forall (xs:list X) (ys:list Y),
                                               (l, l0) = (xs, ys) -> 
                                               empareja xs ys = ps'
                                          xs : list X
                                          ys : list Y
                                          H : (x :: l, y :: l0) = (xs, ys)
                                          H1 : x :: l = xs
                                          H2 : y :: l0 = ys
                                          ============================
                                          (l, l0) = (l, l0)
 *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 7.2. Demostrar que
      forall (f : bool -> bool) (b : bool),
        f (f (f b)) = f b.
   ------------------------------------------------------------------ *)

Theorem bool_tres_veces:
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.                    (* f : bool -> bool
                                    b : bool
                                    ============================
                                    f (f (f b)) = f b *)
  destruct b.
  -                              (* f : bool -> bool
                                    ============================
                                    f (f (f true)) = f true *)
    destruct (f true) eqn:H1.
    +                            (* f : bool -> bool
                                    H1 : f true = true
                                    ============================
                                    f (f true) = true *)
      rewrite H1.                (* f true = true *)
      apply H1.
    +                            (* f : bool -> bool
                                    H1 : f true = false
                                    ============================
                                    f (f false) = false *)
      destruct (f false) eqn:H2. 
      *                          (* f : bool -> bool
                                    H1 : f true = false
                                    H2 : f false = true
                                    ============================
                                    f true = false *)
        apply H1.
      *                          (* f : bool -> bool
                                    H1 : f true = false
                                    H2 : f false = false
                                    ============================
                                    f false = false *)
        apply H2.
  -                              (* f : bool -> bool
                                    ============================
                                    f (f (f false)) = f false *)
    destruct (f false) eqn:H3.
    +                            (* f : bool -> bool
                                    H3 : f false = true
                                    ============================
                                    f (f true) = true *)
      destruct (f true) eqn:H4.
      *                          (* f : bool -> bool
                                    H3 : f false = true
                                    H4 : f true = true
                                    ============================
                                    f true = true *)
        apply H4.
      *                          (* f : bool -> bool
                                    H3 : f false = true
                                    H4 : f true = false
                                    ============================
                                    f false = true *)
        apply H3.
    +                            (* f : bool -> bool
                                    H3 : f false = false
                                    ============================
                                    f (f false) = false *)
      rewrite H3.                (* f false = false *)
      apply H3.
Qed.

(* =====================================================================
   § 8. Ejercicios 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 8.1. Demostrar que
      forall (n m : nat),
        iguales_nat n m = iguales_nat m n.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_simetrica: forall n m : nat,
    iguales_nat n m = iguales_nat m n.
Proof.
  intros n m.                          (* n, m : nat
                                          ============================
                                          iguales_nat n m = iguales_nat m n *)
  destruct (iguales_nat n m) eqn:H1.
  -                                    (* n, m : nat
                                          H1 : iguales_nat n m = true
                                          ============================
                                          true = iguales_nat m n *)
    apply iguales_nat_true in H1.      (* n, m : nat
                                          H1 : n = m
                                          ============================
                                          true = iguales_nat m n *)
    rewrite H1.                        (* true = iguales_nat m m *)
    symmetry.                          (* iguales_nat m m = true *)
    apply iguales_nat_refl.
  -                                    (* n, m : nat
                                          H1 : iguales_nat n m = false
                                          ============================
                                          false = iguales_nat m n *)
    destruct (iguales_nat m n) eqn:H2. 
    +                                  (* n, m : nat
                                          H1 : iguales_nat n m = false
                                          H2 : iguales_nat m n = true
                                          ============================
                                          false = true *)
      apply iguales_nat_true in H2.    (* n, m : nat
                                          H1 : iguales_nat n m = false
                                          H2 : m = n
                                          ============================
                                          false = true *)
      rewrite H2 in H1.                (* n, m : nat
                                          H1 : iguales_nat n n = false
                                          H2 : m = n
                                          ============================
                                          false = true *)
      rewrite iguales_nat_refl in H1.  (* n, m : nat
                                          H1 : true = false
                                          H2 : m = n
                                          ============================
                                          false = true *)
      inversion H1.
    +                                  (* n, m : nat
                                          H1 : iguales_nat n m = false
                                          H2 : iguales_nat m n = false
                                          ============================
                                          false = false *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 8.2. Demostrar que
        forall n m p : nat,
          iguales_nat n m = true ->
          iguales_nat m p = true ->
          iguales_nat n p = true.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_trans: forall n m p : nat,
    iguales_nat n m = true ->
    iguales_nat m p = true ->
    iguales_nat n p = true.
Proof.
  intros n m p H1 H2.           (* n, m, p : nat
                                   H1 : iguales_nat n m = true
                                   H2 : iguales_nat m p = true
                                   ============================
                                   iguales_nat n p = true *)
  apply iguales_nat_true in H1. (* n, m, p : nat
                                   H1 : n = m
                                   H2 : iguales_nat m p = true
                                   ============================
                                   iguales_nat n p = true *)
  apply iguales_nat_true in H2. (* n, m, p : nat
                                   H1 : n = m
                                   H2 : m = p
                                   ============================
                                   iguales_nat n p = true *)
  rewrite H1.                   (* iguales_nat m p = true *)
  rewrite H2.                   (* iguales_nat p p = true *)
  apply iguales_nat_refl.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 8.3. Definir las hipótesis sobre xs e ys para que se cumpla
   la propiedad 
      desempareja (empareja xs ys) = (xs,ys).
   y demostrarla.
   ------------------------------------------------------------------ *)

(* En la prueba se usará el siguiente lema *)
Lemma longitud_cero: forall (X : Type) (xs : list X),
    longitud xs = 0 -> xs = [].
Proof.
  intros X xs H.           (* X : Type
                              xs : list X
                              H : longitud xs = 0
                              ============================
                              xs = [ ] *)
  destruct xs as [|x xs']. 
  -                        (* X : Type
                              H : longitud [ ] = 0
                              ============================
                              [ ] = [ ] *)
    reflexivity.
  -                        (* X : Type
                              x : X
                              xs' : list X
                              H : longitud (x :: xs') = 0
                              ============================
                              x :: xs' = [ ] *)
    simpl in H.            (* X : Type
                              x : X
                              xs' : list X
                              H : S (longitud xs') = 0
                              ============================
                              x :: xs' = [ ] *)
    inversion H.
Qed.

Theorem desempareja_empareja: forall (X : Type) (xs ys: list X),
    longitud xs = longitud ys ->
    desempareja (empareja xs ys) = (xs,ys).
Proof.
  intros X xs.                  (* X : Type
                                   xs : list X
                                   ============================
                                   forall ys : list X,
                                   longitud xs = longitud ys -> 
                                   desempareja (empareja xs ys) = (xs, ys) *)
  induction xs as [|x xs' HI1]. 
  -                             (* X : Type
                                   ============================
                                   forall ys : list X,
                                   longitud [ ] = longitud ys -> 
                                   desempareja (empareja [ ] ys) = ([ ], ys) *)
    intros ys H.                (* X : Type
                                   ys : list X
                                   H : longitud [ ] = longitud ys
                                   ============================
                                   desempareja (empareja [ ] ys) = ([ ], ys) *)
    simpl in H.                 (* X : Type
                                   ys : list X
                                   H : 0 = longitud ys
                                   ============================
                                   desempareja (empareja [ ] ys) = ([ ], ys) *)
    symmetry in H.              (* X : Type
                                   ys : list X
                                   H : longitud ys = 0
                                   ============================
                                   desempareja (empareja [ ] ys) = ([ ], ys) *)
    apply longitud_cero in H.   (* X : Type
                                   ys : list X
                                   H : ys = [ ]
                                   ============================
                                   desempareja (empareja [] ys) = ([], ys) *)
    rewrite H.                  (* desempareja (empareja [] []) = ([], []) *)
    simpl.                      (* ([], []) = ([], []) *)
    reflexivity.
  -                             (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   ============================
                                   forall ys : list X,
                                   longitud (x :: xs') = longitud ys ->
                                   desempareja (empareja (x :: xs') ys) 
                                   = (x :: xs', ys) *)
    intros ys.                  (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   ys : list X
                                   ============================
                                   longitud (x :: xs') = longitud ys ->
                                   desempareja (empareja (x :: xs') ys) 
                                   = (x :: xs', ys) *)
    destruct ys as [|y ys'].
    +                           (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   ============================
                                   longitud (x :: xs') = longitud [ ] ->
                                   desempareja (empareja (x :: xs') [ ]) 
                                   = (x :: xs', [ ]) *)
      intros H.                 (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   H : longitud (x :: xs') = longitud [ ]
                                   ============================
                                   desempareja (empareja (x :: xs') [ ]) 
                                   = (x :: xs', [ ]) *)
      simpl in H.               (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   H : S (longitud xs') = 0
                                   ============================
                                   desempareja (empareja (x :: xs') [ ]) 
                                   = (x :: xs', [ ]) *)
      inversion H.
    +                           (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   y : X
                                   ys' : list X
                                   ============================
                                   longitud (x :: xs') = longitud (y :: ys') ->
                                   desempareja (empareja (x::xs') (y::ys')) 
                                   = (x :: xs', y :: ys') *)
      intros H.                 (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   y : X
                                   ys' : list X
                                   H : longitud (x :: xs') = longitud (y :: ys')
                                   ============================
                                   desempareja (empareja (x::xs') (y::ys')) 
                                   = (x :: xs', y :: ys') *)
      inversion H.              (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   y : X
                                   ys' : list X
                                   H : longitud (x :: xs') = longitud (y :: ys')
                                   H1 : longitud xs' = longitud ys'
                                   ============================
                                   desempareja (empareja (x::xs') (y::ys')) 
                                   = (x :: xs', y :: ys') *)
      apply HI1 in H1.          (* X : Type
                                   x : X
                                   xs' : list X
                                   HI1 : forall ys : list X,
                                         longitud xs' = longitud ys ->
                                         desempareja (empareja xs' ys) 
                                         = (xs', ys)
                                   y : X
                                   ys' : list X
                                   H : longitud (x :: xs') = longitud (y :: ys')
                                   H1 : desempareja (empareja xs' ys') 
                                        = (xs', ys')
                                   ============================
                                   desempareja (empareja (x::xs') (y::ys')) 
                                   = (x :: xs', y :: ys') *)
      simpl.                    (* match desempareja (empareja xs' ys') with
                                   | (xs, ys) => (x :: xs, y :: ys)
                                   end 
                                   = (x :: xs', y :: ys') *)
      rewrite H1.               (* (x::xs', y::ys') = (x::xs',y::ys') *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 8.4. Demostrar que
      forall (X : Type) (p : X -> bool) (x : X) (xs ys : list X),
        filtra p xs = x :: ys ->
        p x = true.
   ------------------------------------------------------------------ *)

Theorem prop_filtra:
  forall (X : Type) (p : X -> bool) (x : X) (xs ys : list X),
    filtra p xs = x :: ys ->
    p x = true.
Proof.
  intros X p x xs ys.           (* X : Type
                                   p : X -> bool
                                   x : X
                                   xs, ys : list X
                                   ============================
                                   filtra p xs = x :: ys -> p x = true *)
  induction xs as [|x' xs' HI]. 
  -                             (* X : Type
                                   p : X -> bool
                                   x : X
                                   ys : list X
                                   ============================
                                   filtra p [ ] = x :: ys -> p x = true *)
    simpl.                      (* [ ] = x :: ys -> p x = true *)
    intros H.                   (* X : Type
                                   p : X -> bool
                                   x : X
                                   ys : list X
                                   H : [ ] = x :: ys
                                   ============================
                                   p x = true *)
    inversion H.
  -                             (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   ============================
                                   filtra p (x'::xs') = x::ys -> p x = true *)
    destruct (p x') eqn:Hx'. 
    +                           (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   Hx' : p x' = true
                                   ============================
                                   filtra p (x'::xs') = x::ys -> p x = true *)
      simpl.                    (* (if p x' then x' :: filtra p xs' 
                                            else filtra p xs') 
                                   = x :: ys -> p x = true *)
      rewrite Hx'.              (* x' :: filtra p xs' = x :: ys -> p x = true *)
      intros H.                 (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   Hx' : p x' = true
                                   H : x' :: filtra p xs' = x :: ys
                                   ============================
                                   p x = true *)
      inversion H.              (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   Hx' : p x' = true
                                   H : x' :: filtra p xs' = x :: ys
                                   H1 : x' = x
                                   H2 : filtra p xs' = ys
                                   ============================
                                   p x = true *)
      rewrite H1 in Hx'.        (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   Hx' : p x = true
                                   H : x' :: filtra p xs' = x :: ys
                                   H1 : x' = x
                                   H2 : filtra p xs' = ys
                                   ============================
                                   p x = true *)
      apply Hx'.
    +                           (* X : Type
                                   p : X -> bool
                                   x, x' : X
                                   xs', ys : list X
                                   HI : filtra p xs' = x :: ys -> p x = true
                                   Hx' : p x' = false
                                   ============================
                                   filtra p (x'::xs') = x::ys -> p x = true *)
      simpl.                    (* (if p x' then x' :: filtra p xs' 
                                            else filtra p xs') 
                                   = x :: ys -> p x = true *)
      rewrite Hx'.              (* filtra p xs' = x :: ys -> p x = true *)
      apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 8.5.1. Definir, por recursión, la función 
      todos {X : Type} (p : X -> bool) (xs : list X) : bool 
   tal que (todos p xs) se verifica si todos los elementos de xs cumplen
   p. Por ejemplo, 
      todos esImpar [1;3;5;7;9]     = true
      todos negacion [false;false]  = true
      todos esPar [0;2;4;5]         = false
      todos (iguales_nat 5) []      = true
   ------------------------------------------------------------------ *)

Fixpoint todos {X : Type} (p : X -> bool) (xs : list X) : bool :=
  match xs with
  | nil    => true
  | x::xs' => conjuncion (p x) (todos p xs')
  end.

Compute (todos esImpar [1;3;5;7;9]).
(* = true : bool*)
Compute (todos negacion [false;false]).
(* = true : bool*)
Compute (todos esPar [0;2;4;5]).
(* = false : bool*)
Compute (todos (iguales_nat 5) []).
(* = true : bool *)

(* ---------------------------------------------------------------------
   Ejercicio 8.5.2. Definir, por recursión, la función 
      existe      
   tal que (existe p xs) se verifica si algún elemento de xs cumple
   p. Por ejemplo, 
      existe (iguales_nat 5) [0;2;3;6]           = false
      existe (conjuncion true) [true;true;false] = true
      existe esImpar [1;0;0;0;0;3]               = true
      existe esPar []                            = false
   ------------------------------------------------------------------ *)

Fixpoint existe {X : Type} (p : X -> bool) (xs : list X) : bool :=
  match xs with
  | nil    => false
  | x::xs' => disyuncion (p x) (existe p xs')
  end.

Compute (existe (iguales_nat 5) [0;2;3;6]).
(* = false : bool *)
Compute (existe (conjuncion true) [true;true;false]).
(* = true : bool *)
Compute (existe esImpar [1;0;0;0;0;3]).
(* = true : bool *)
Compute (existe esPar []).
(* = false : bool *)

(* ---------------------------------------------------------------------
   Ejercicio 8.5.3. Redefinir, usando todos y negb, la función existe2 y
   demostrar su equivalencia con existe.
   ------------------------------------------------------------------ *)

Definition existe2 {X : Type} (p : X -> bool) (xs : list X) : bool :=
  negacion (todos (fun y => negacion (p y)) xs).

Compute (existe2 (iguales_nat 5) [0;2;3;6]).
(* = false : bool *)
Compute (existe2 (conjuncion true) [true;true;false]).
(* = true : bool *)
Compute (existe2 esImpar [1;0;0;0;0;3]).
(* = true : bool *)
Compute (existe2 esPar []).
(* = false : bool *)

Theorem equiv_existe: forall (X : Type) (p : X -> bool) (xs : list X),
    existe p xs = existe2 p xs.
Proof.
  intros X p xs.               (* X : Type
                                  p : X -> bool
                                  xs : list X
                                  ============================
                                  existe p xs = existe2 p xs *)
  induction xs as [|x xs' HI]. 
  -                            (* X : Type
                                  p : X -> bool
                                  ============================
                                  existe p [ ] = existe2 p [ ] *)
    unfold existe2.            (* existe p [ ] = 
                                  negacion (todos (fun y : X => negacion (p y))
                                                   [ ]) *)
    simpl.                     (* false = false *)
    reflexivity.
  -                            (* X : Type
                                  p : X -> bool
                                  x : X
                                  xs' : list X
                                  HI : existe p xs' = existe2 p xs'
                                  ============================
                                  existe p (x :: xs') = existe2 p (x :: xs') *)
    destruct (p x) eqn:Hx.
    +                          (* X : Type
                                  p : X -> bool
                                  x : X
                                  xs' : list X
                                  HI : existe p xs' = existe2 p xs'
                                  Hx : p x = true
                                  ============================
                                  existe p (x :: xs') = existe2 p (x :: xs') *)
      unfold existe2.          (* existe p (x :: xs') =
                                  negacion (todos (fun y : X => negacion (p y))
                                                  (x :: xs')) *)
      simpl.                   (* p x || existe p xs' =
                                  negacion 
                                   (negacion 
                                    (p x) && 
                                    todos (fun y : X => negacion (p y)) xs') *)
      rewrite Hx.              (* true || existe p xs' =
                                  negacion 
                                   (negacion true && 
                                    todos (fun y : X => negacion (p y)) xs')*)
      simpl.                   (* true = true *)
      reflexivity.
    +                          (* X : Type
                                  p : X -> bool
                                  x : X
                                  xs' : list X
                                  HI : existe p xs' = existe2 p xs'
                                  Hx : p x = false
                                  ============================
                                  existe p (x :: xs') = existe2 p (x :: xs') *)
      unfold existe2.          (* existe p (x :: xs') =
                                  negacion 
                                   (todos (fun y : X => negacion (p y)) 
                                          (x :: xs')) *)
      simpl.                   (* p x || existe p xs' =
                                  negacion 
                                   (negacion (p x) && 
                                    todos (fun y : X => negacion (p y)) xs') *)
      rewrite Hx.              (* false || existe p xs' =
                                  negacion (
                                   negacion false && 
                                   todos (fun y : X => negacion (p y)) xs') *)
      simpl.                   (* existe p xs' =
                                  negacion 
                                   (todos (fun y : X => negacion (p y)) xs') *)
      rewrite HI.              (* existe2 p xs' = 
                                  negacion 
                                   (todos (fun y : X => negacion (p y)) xs') *)
      unfold existe2.          (* negacion 
                                   (todos (fun y : X => negacion (p y)) xs') =
                                  negacion 
                                   (todos (fun y : X => negacion (p y)) xs') *)
      reflexivity.
Qed.

(* =====================================================================
   § 9. Resumen de tácticas básicas 
   ================================================================== *)

(* Las tácticas básicas utilizadas hasta ahora son
  + apply H: 
    + si el objetivo coincide con la hipótesis H, lo demuestra;
    + si H es una implicación,
      + si el objetivo coincide con la conclusión de H, lo sustituye por
        su premisa y
      + si el objetivo coincide con la premisa de H, lo sustituye por
        su conclusión.

  + apply ... with ...: Especifica los valores de las variables que no
    se pueden deducir por emparejamiento.

  + apply H1 in H2: Aplica la igualdad de la hipótesis H1 a la
    hipótesis H2.

  + assert (H: P): Incluye la demostración de la propiedad P y continúa
    la demostración añadiendo como premisa la propiedad P con nombre H. 

  + destruct b: Distingue dos casos según que b sea True o False.

  + destruct n as [| n1]: Distingue dos casos según que n sea 0 o sea S n1. 

  + destruct p as [n m]: Sustituye el par p por (n,m).

  + destruct e eqn: H: Distingue casos según el valor de la expresión
    e y lo añade al contexto la hipótesis H.

  + generalize dependent x: Mueve la variable x (y las que dependan de
    ella) del contexto a una hipótesis explícita en el objetivo.

  + induction n as [|n1 IHn1]: Inicia una demostración por inducción
    sobre n. El caso base en ~n  0~. El paso de la inducción consiste en
    suponer la propiedad para ~n1~ y demostrarla para ~S n1~. El nombre de la
    hipótesis de inducción es ~IHn1~.

  + intros vars: Introduce las variables del cuantificador universal y,
    como premisas, los antecedentes de las implicaciones.

  + inversion: Aplica que los constructores son disjuntos e inyectivos. 

  + reflexivity: Demuestra el objetivo si es una igualdad trivial.

  + rewrite H: Sustituye el término izquierdo de H por el derecho.

  + rewrite <-H: Sustituye el término derecho de H por el izquierdo.

  + simpl: Simplifica el objetivo.

  + simpl in H: Simplifica la hipótesis H.

  + symmetry: Cambia un objetivo de la forma s = t en t = s.

  + symmetry in H: Cambia la hipótesis H de la forma ~st~ en ~ts~.

  + unfold f: Expande la definición de la función f.
 *)

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "More Basic Tactics" de Peirce et als. http://bit.ly/2LYFTlZ *)
