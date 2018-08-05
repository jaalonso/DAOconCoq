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
   8. Resumen de tácticas básicas 
   9. Ejercicios 
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

Theorem artificial3_firsttry : forall (n : nat),
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
   Ejemplo. Con dos reescrituras.
   ------------------------------------------------------------------ *)

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* [a; b] = [e; f] *)
  rewrite -> eq1.
  (* [c; d] = [e; f] *)
  rewrite -> eq2.
  (* [e; f] = [e; f] *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo de lema para simplificar la demostración anterior.
   ------------------------------------------------------------------ *)

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  (* n = o *)
  rewrite -> eq1.
  (* m = o *)
  rewrite -> eq2.
  (* o = o *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo. De simplificación de la prueba usando el lema.
   ------------------------------------------------------------------ *)

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* [a; b] = [e; f] *)
  apply trans_eq with (m:=[c;d]).
  (* [a; b] = [c; d]
     [c; d] = [e; f] *) 
  apply eq1.
  (* [c; d] = [e; f] *)
  apply eq2.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Simplificación de la prueba anterior.
   ------------------------------------------------------------------ *)

Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* [a; b] = [e; f] *)
  apply trans_eq with [c;d].
  (* [a; b] = [c; d]
     [c; d] = [e; f] *) 
  apply eq1.
  (* [c; d] = [e; f] *)
  apply eq2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3. Demostrar que
      forall (n m o p : nat),
        m = (minustwo o) ->
        (n + p) = m ->
        (n + p) = (minustwo o).
   ------------------------------------------------------------------ *)

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* FILL IN HERE *) Admitted.

(* =====================================================================
   § 3. La táctica 'inversion'
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo de demostración con inversión sobre los naturales.
   ------------------------------------------------------------------ *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* n : nat
     m : nat
     H : S n = S m *) 
  inversion H.
  (* H1 : n = m *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo de inversión generando varias hipótesis.
   ------------------------------------------------------------------ *)

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H.
  (* n : nat
     m : nat
     o : nat
     H : [n; m] = [o; o] *)
  inversion H.
  (* H1 : n = o
     H2 : m = o *)
  reflexivity.
Qed.


(* ---------------------------------------------------------------------
   Ejemplo de nombramiento de las hipótesis generadas por inversión.
   ------------------------------------------------------------------ *)

Theorem inversion_ex2 : forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
  intros n m H.
  (* n : nat
     m : nat
     H : [n] = [m] *)
  inversion H as [Hnm].
  (* Hnm : n = m *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4. Demostrar que
      forall (X : Type) (x y z : X) (l j : list X),
        x :: y :: l = z :: j ->
        y :: l = x :: j ->
        x = y.
   ------------------------------------------------------------------ *)

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejemplo de demostración por inversión basada en que los constructores
   son disjuntos.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_0_l : forall n,
    iguales_nat 0 n = true -> n = 0.
Proof.
  intros n.
  (* iguales_nat 0 n = true -> n = 0 *)
  destruct n as [| n'].
  - (* iguales_nat 0 0 = true -> 0 = 0 *)
    intros H.
    (* 0 = 0 *)
    reflexivity.
  - (* iguales_nat 0 (S n') = true -> S n' = 0 *)
    simpl.
    (* false = true -> S n' = 0 *)
    intros H.
    (* S n' = 0 *)
    inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplos de demostración por inversión sobre los booleanos.
   ------------------------------------------------------------------ *)

Theorem inversion_ex4 : forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5. Demostrar que
      forall (X : Type) (x y z : X) (l j : list X),
        x :: y :: l = [] ->
        y :: l = z :: j ->
        x = z.
   ------------------------------------------------------------------ *)

Example inversion_ex6 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejemplo de lema que usaremos más tarde.
   ------------------------------------------------------------------ *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

(* =====================================================================
   § 4. Uso de tácticas sobre las hipótesis
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo de demostración con "simpl in ..."
   ------------------------------------------------------------------ *)

Theorem S_inj : forall (n m : nat) (b : bool),
    iguales_nat (S n) (S m) = b  ->
    iguales_nat n m = b.
Proof.
  intros n m b H.
  (* H : iguales_nat (S n) (S m) = b *)
  simpl in H.
  (* H : iguales_nat n m = b *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo de "razonamiento hacia adelante" con "apply L in H".
   ------------------------------------------------------------------ *)

Theorem artificial3' : forall (n : nat),
  (iguales_nat n 5 = true -> iguales_nat (S (S n)) 7 = true) ->
  true = iguales_nat n 5  ->
  true = iguales_nat (S (S n)) 7.
Proof.
  intros n eq H.
  (* eq : iguales_nat n 5 = true -> iguales_nat (S (S n)) 7 = true
     H : true = iguales_nat n 5 *)
  symmetry in H.
  (* H : iguales_nat n 5 = true *)
  apply eq in H.
  (* H : iguales_nat (S (S n)) 7 = true *)
  symmetry in H.
  (* H : true = iguales_nat (S (S n)) 7 *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6. Demostrar
      forall n m,
        n + n = m + m ->
        n = m.

   Nota: Usar plus_n_Sm
   ------------------------------------------------------------------ *)

Theorem plus_n_n_injective :
  forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n.
  induction n as [| n'].
  (* FILL IN HERE *) Admitted.

(* =====================================================================
   § 5. Control de la hipótesis de inducción  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo de necesidad de controlar la hipótesis de inducción.
   ------------------------------------------------------------------ *)

Theorem double_injective_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  induction n as [| n'].
  - (* double 0 = double m -> 0 = m *)
    simpl.
    (* 0 = double m -> 0 = m *)
    intros eq.
    (* 0 = m *)
    destruct m as [| m'].
    + (* 0 = O *)
      reflexivity.
    + (* 0 = S m' *)
      inversion eq.
  - (* double (S n') = double m -> S n' = m *)
    intros eq.
    (* S n' = m *) 
    destruct m as [| m'].
    + (* S n' = 0 *)
      inversion eq.
    + (* S n' = S m' *)
      apply f_equal.
      (* n' = m' *)
      Abort.

Theorem double_injective : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n.
  induction n as [| n'].
  - (* forall m : nat, double 0 = double m -> 0 = m *)
    simpl.
    (* forall m : nat, 0 = double m -> 0 = m *)
    intros m eq.
    destruct m as [| m'].
    + (* 0 = O *)
      reflexivity.
    + (* 0 = S m' *)
      inversion eq.
  - (* IHn' : forall m : nat, double n' = double m -> n' = m
       forall m : nat, double (S n') = double m -> S n' = m *)
    simpl.
    (* forall m : nat, S (S (double n')) = double m -> S n' = m *)
    intros m eq.
    destruct m as [| m'].
    + (* S n' = O *)
      simpl.
      inversion eq.
    + (* S n' = S m' *)
      apply f_equal.
      (* n' = m' *)
      apply IHn'.
      (* double n' = double m' *)
      inversion eq.
      (* double n' = double n' *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Comentario sobre la estrategia de generalización.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 7. Demostrar que
      forall n m,
        iguales_nat n m = true -> n = m.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_true : forall n m,
    iguales_nat n m = true -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejemplo de problema por usar intros antes que induction.
   ------------------------------------------------------------------ *)
Theorem double_injective_take2_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
Abort.

(* ---------------------------------------------------------------------
   Ejemplo con la táctica "generalize dependent"
   ------------------------------------------------------------------ *)

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal. apply IHm'. inversion eq. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Lema para iso posterior.
   ------------------------------------------------------------------ *)

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply iguales_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 8. Demostra, por inducción sobre l,
      forall (n : nat) (X : Type) (l : list X),
        length l = n ->
        nth_error l n = None.
   ------------------------------------------------------------------ *)

Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
Proof.
  (* FILL IN HERE *) Admitted.

(* =====================================================================
   § 6. Expansión de definiciones 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo de expansión de una definición con unfold.
   ------------------------------------------------------------------ *)

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl. (* no hace nada *)
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm.
    apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo de expansión automática de definiciones.
   ------------------------------------------------------------------ *)

Definition foo (x: nat) := 5.

Fact artificial_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo de no expansión automática de definiciones.
   ------------------------------------------------------------------ *)

Definition bar x :=
  match x with
  | O   => 5
  | S _ => 5
  end.

Fact artificial_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* No hace nada *)
Abort.

(* Demostración con destruct *)
Fact artificial_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Demostración con unfold *)
Fact artificial_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(* =====================================================================
   § 7. Uso de 'destruct' sobre expresiones compuestas
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplos de uso de destruct sobre expresiones compuestas.
   ------------------------------------------------------------------ *)

Definition artificialfun (n : nat) : bool :=
  if      iguales_nat n 3 then false
  else if iguales_nat n 5 then false
  else                     false.

Theorem artificialfun_false : forall (n : nat),
    artificialfun n = false.
Proof.
  intros n. unfold artificialfun.
  destruct (iguales_nat n 3).
    - (* iguales_nat n 3 = true *) reflexivity.
    - (* iguales_nat n 3 = false *) destruct (iguales_nat n 5).
      + (* iguales_nat n 5 = true *) reflexivity.
      + (* iguales_nat n 5 = false *) reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 9. Se define la función split por
      Fixpoint split {X Y : Type} (l : list (X*Y))
                     : (list X) * (list Y) :=
        match l with
        | [] => ([], [])
        | (x, y) :: t =>
            match split t with
            | (lx, ly) => (x :: lx, y :: ly)
            end
        end.

   Demostrar que split y combine son inversas; es decir,
        forall X Y (l : list (X * Y)) l1 l2,
          split l = (l1, l2) ->
          combine l1 l2 = l.
   ------------------------------------------------------------------ *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejemplo de precauciones al usar destruct para no perder información.
   ------------------------------------------------------------------ *)

Definition artificialfun1 (n : nat) : bool :=
  if      iguales_nat n 3 then true
  else if iguales_nat n 5 then true
  else                     false.

Theorem artificialfun1_odd_FAILED : forall (n : nat),
    artificialfun1 n = true ->
    esImpar n = true.
Proof.
  intros n eq. unfold artificialfun1 in eq.
  destruct (iguales_nat n 3).
  (* Falso por falta de información *)
Abort.

(* Solución usando destruct con eqn *)
Theorem artificialfun1_odd : forall (n : nat),
    artificialfun1 n = true ->
    esImpar n = true.
Proof.
  intros n eq. unfold artificialfun1 in eq.
  destruct (iguales_nat n 3) eqn:Heqe3.
    - (* e3 = true *) apply iguales_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
      destruct (iguales_nat n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply iguales_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 10. Demostrar que
      forall (f : bool -> bool) (b : bool),
        f (f (f b)) = f b.
   ------------------------------------------------------------------ *)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.

(* =====================================================================
   § 8. Resumen de tácticas básicas 
   ================================================================== *)

(* Tácticas básicas:
   - [intros]: move hypotheses/variables from goal to context

   - [reflexivity]: finish the proof (when the goal looks like [e = e])

   - [apply]: prove goal using a hypothesis, lemma, or constructor

   - [apply... in H]: apply a hypothesis, lemma, or constructor to
     a hypothesis in the context (forward reasoning)

   - [apply... with...]: explicitly specify values for variables
     that cannot be determined by pattern matching

   - [simpl]: simplify computations in the goal

   - [simpl in H]: ... or a hypothesis

   - [rewrite]: use an equality hypothesis (or lemma) to rewrite
     the goal

   - [rewrite ... in H]: ... or a hypothesis

   - [symmetry]: changes a goal of the form [t=u] into [u=t]

   - [symmetry in H]: changes a hypothesis of the form [t=u] into [u=t]

   - [unfold]: replace a defined constant by its right-hand side in
     the goal

   - [unfold... in H]: ... or a hypothesis

   - [destruct... as...]: case analysis on values of inductively
     defined types

   - [destruct... eqn:...]: specify the name of an equation to be
     added to the context, recording the result of the case analysis

   - [induction... as...]: induction on values of inductively
     defined types

   - [inversion]: reason by injectivity and distinctness of constructors

   - [assert (H: e)] (or [assert (e) as H]): introduce a "local
     lemma" [e] and call it [H]

   - [generalize dependent x]: move the variable [x] (and anything
     else that depends on it) from the context back to an explicit
     hypothesis in the goal formula *)

(* =====================================================================
   § 9. Ejercicios 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 11. Demostrar que
      forall (n m : nat),
        iguales_nat n m = iguales_nat m n.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_sym :
  forall (n m : nat),
    iguales_nat n m = iguales_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejercicio 12. Demostrar que
        forall n m p,
          iguales_nat n m = true ->
          iguales_nat m p = true ->
          iguales_nat n p = true.
   ------------------------------------------------------------------ *)

Theorem iguales_nat_trans :
  forall n m p,
    iguales_nat n m = true ->
    iguales_nat m p = true ->
    iguales_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejercicio 13. We proved, in an exercise above, that for all lists of
   pairs, [combine] is the inverse of [split].  How would you formalize
   the statement that [split] is the inverse of [combine]?  When is this 
   property true?

   Complete the definition of [split_combine_statement] below with a
   property that states that [split] is the inverse of
   [combine]. Then, prove that the property holds. (Be sure to leave
   your induction hypothesis general by not doing [intros] on more
   things than necessary.  Hint: what property do you need of [l1]
   and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?) 
   ------------------------------------------------------------------ *)

Definition split_combine_statement : Prop
  (* ("[: Prop]" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejercicio 14. Demostrar que
      forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
        filter test l = x :: lf ->
        test x = true.
   ------------------------------------------------------------------ *)

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf ->
    test x = true.
Proof.
  (* FILL IN HERE *) Admitted.

(* ---------------------------------------------------------------------
   Ejercicio 15. Definir, por recursión, las funciones forallb y existsb
   tales que 
   + (forallb p xs) se verifica si todos los elementos de xs cumplen
     p. Por ejemplo, 
        forallb esImpar [1;3;5;7;9]   = true
        forallb negb [false;false] = true
        forallb esPar [0;2;4;5]    = false
        forallb (iguales_nat 5) []     = true
   + (existsb p xs) se verifica si algún elemento de xs cumple p. Por
     ejemplo, 
        existsb (iguales_nat 5) [0;2;3;6]         = false
        existsb (andb true) [true;true;false] = true
        existsb esImpar [1;0;0;0;0;3]            = true
        existsb esPar []                      = false

   Redefinir, usando forallb y negb, la función existsb' y demostrar su
   equivalencia con existsb.
   ------------------------------------------------------------------ *)


(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "More Basic Tactics" de Peirce et als. http://bit.ly/2LYFTlZ *)
