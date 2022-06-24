(* T7: Proposiciones definidas inductivamente *)

Set Warnings "-notation-overridden,-parsing".
Require Export T6_Logica.
Require Coq.omega.Omega.
1
(* El contenido del tema es
   1. Proposiciones definidas inductivamente.
   2. Usando evidencias en demostraciones.
      1. Inversión sobre evidencias.
      2. Inducción sobre evidencias.
   3. Relaciones inductivas.
   4. Caso de estudio: Expresiones regulares.
      1. Introducción.
      2. La táctica remember .
   5. Caso de estudio: Mejora de la reflexión.
   6. Ejercicios adicionales.
      1.Extended Exercise: A Verified Regular-Expression Matcher
*)

(* =====================================================================
   § 1. Proposiciones definidas inductivamente.
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1. Definir inductivamente la proposición
      es_par: nat -> Prop
   tal que (es_par n) expresa que n es un número par.
   ------------------------------------------------------------------ *)

Inductive es_par: nat -> Prop :=
| es_par_0  : es_par 0
| es_par_SS : forall n : nat, es_par n -> es_par (S (S n)).

(* ---------------------------------------------------------------------
   Ejemplo 1.2. Demostrar que
      es_par 4.
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Theorem es_par_4: es_par 4.
Proof.
  apply es_par_SS. (* es_par 2 *)
  apply es_par_SS. (* es_par 0 *)
  apply es_par_0.
Qed.

(* 2ª demostración *)
Theorem es_par_4': es_par 4.
Proof.
  apply (es_par_SS 2 (es_par_SS 0 es_par_0)).
Qed.

(* Nota *)
Check es_par_0.                             (* es_par 0 *)
Check es_par_SS.                            (* forall n : nat,
                                                es_par n -> es_par (S (S n)) *)
Check (es_par_SS 0).                        (* es_par 0 -> es_par 2 *)
Check (es_par_SS 0 es_par_0).               (* es_par 2 *)
Check (es_par_SS 2).                        (* es_par 2 -> es_par 4 *)
Check (es_par_SS 2 (es_par_SS 0 es_par_0)). (* es_par 4 *)

(* ---------------------------------------------------------------------
   Ejemplo 1.3. Demostrar que
      forall n : nat, es_par n -> es_par (4 + n).
   ------------------------------------------------------------------ *)

Theorem es_par_suma4:
  forall n : nat, es_par n -> es_par (4 + n).
Proof.
  intros n.        (* n : nat
                      ============================
                      es_par n -> es_par (4 + n) *)
  simpl.           (* es_par n -> es_par (S (S (S (S n)))) *)
  intros Hn.       (* Hn : es_par n
                      ============================
                      es_par (S (S (S (S n)))) *)
  apply es_par_SS. (* es_par (S (S n)) *)
  apply es_par_SS. (* es_par n *)
  apply Hn.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1. Demostrar que
      forall n : nat, es_par (doble n).
   ------------------------------------------------------------------ *)

Theorem es_par_doble:
  forall n : nat, es_par (doble n).
Proof.
  induction n as [|n' HI].
  -                        (* es_par (doble 0) *)
    simpl.                 (* es_par 0 *)
    apply es_par_0.
  -                        (* n' : nat
                              HI : es_par (doble n')
                              ============================
                              es_par (doble (S n')) *)
    simpl.                 (* es_par (S (S (doble n'))) *)
    apply es_par_SS.       (* es_par (doble n') *)
    apply HI.
Qed.

(* =====================================================================
   § 2. Usando evidencias en demostraciones
   ================================================================== *)

(* ---------------------------------------------------------------------
   Nota. Programación y demostración en Coq son dos lados de la misma
   moneda. En progrmación se procesan datos y en demostración se
   procesan evidencias.
   ------------------------------------------------------------------ *)

(* =====================================================================
   §§ 2.1. Inversión sobre evidencias
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.1. Demostrar que
      forall n : nat,
        es_par n -> es_par (pred (pred n)).
      ------------------------------------------------------------------ *)

(* 1ª demostración *)
Theorem es_par_menos_2:
  forall n : nat,
    es_par n -> es_par (pred (pred n)).
Proof.
  intros n E.               (* n : nat
                               E : es_par n
                               ============================
                               es_par (Nat.pred (Nat.pred n)) *)
  inversion E as [| n' E'].
  -                         (* H : 0 = n
                               ============================
                               es_par (Nat.pred (Nat.pred 0)) *)
    simpl.                  (* es_par 0 *)
    apply es_par_0.
  -                         (* n' : nat
                               E' : es_par n'
                               H : S (S n') = n
                               ============================
                               es_par (Nat.pred (Nat.pred (S (S n')))) *)
    simpl.                  (* es_par n' *)
    apply E'.
Qed.

(* ---------------------------------------------------------------------
   Nota. La táctica (inversion E), donde E es la etiqueta de una
   proposición P definida inductivamente, genera para cada uno de los
   constructores de P las condiciones bajo las que se puede usar el
   constructor para demostrar P.
   ------------------------------------------------------------------ *)

(* 2ª demostración *)
Theorem es_par_menos_2':
  forall n : nat,
    es_par n -> es_par (pred (pred n)).
Proof.
  intros n E.              (* n : nat
                              E : es_par n
                              ============================
                              es_par (Nat.pred (Nat.pred n)) *)
  destruct E as [| n' E'].
  -                        (* es_par (Nat.pred (Nat.pred 0)) *)
    simpl.                 (* es_par 0 *)
    apply es_par_0.
  -                        (* E' : es_par n'
                              ============================
                              es_par (Nat.pred (Nat.pred (S (S n')))) *)
    simpl.                 (* es_par n' *)
    apply E'.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de destruct sobre evidencia con (destruct E as [| n' E']).
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.2. Demostrar que
      forall n : nat,
       es_par (S (S n)) -> es_par n.
   ------------------------------------------------------------------ *)

(* 1º intento *)
Theorem es_parSS_es_par:
  forall n : nat,
    es_par (S (S n)) -> es_par n.
Proof.
  intros n E.              (* n : nat
                              E : es_par (S (S n))
                              ============================
                              es_par n *)
  destruct E as [| n' E'].
  -                        (* n : nat
                              ============================
                              es_par n *)
Abort.

(* ---------------------------------------------------------------------
   Nota. Mal funcionamiento de destruct sobre evidencias de términos
   compuestos.
   ------------------------------------------------------------------ *)

(* 2º intento *)
Theorem es_parSS_es_par:
  forall n : nat,
    es_par (S (S n)) -> es_par n.
Proof.
  intros n E.               (* n : nat
                               E : es_par (S (S n))
                               ============================
                               es_par n *)
  inversion E as [| n' E']. (* n' : nat
                               E' : es_par n
                               H : n' = n
                               ============================
                               es_par n *)
  apply E'.
Qed.
(* ---------------------------------------------------------------------
   Ejemplo 2.1.3. Demostrar que
      ~ es_par 1.
   ------------------------------------------------------------------ *)

Theorem uno_no_es_par:
  ~ es_par 1.
Proof.
  intros H.    (* H : es_par 1
                  ============================
                  False *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Nota. uso de inversión sobre evidencia para contradicción.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 2.1.1. Demostrar que
      forall n : nat,
        es_par (S (S (S (S n)))) -> es_par n.
   ------------------------------------------------------------------ *)

Theorem SSSS_es_par:
  forall n : nat,
    es_par (S (S (S (S n)))) -> es_par n.
Proof.
  intros n E.                 (* n : nat
                                 E : es_par (S (S (S (S n))))
                                 ============================
                                 es_par n *)
  inversion E as [|n' E'].    (* n' : nat
                                 E' : es_par (S (S n))
                                 H : n' = S (S n)
                                 ============================
                                 es_par n *)
  inversion E' as [|n'' E'']. (* n'' : nat
                                 E'' : es_par n
                                 H0 : n'' = n
                                 ============================
                                 es_par n *)
  apply E''.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.1.2. Demostrar que
      es_par 5 -> 2 + 2 = 9.
   ------------------------------------------------------------------ *)

Theorem consecuencia_de_5_es_par:
  es_par 5 -> 2 + 2 = 9.
Proof.
  intros E1.                (* E1 : es_par 5
                               ============================
                               2 + 2 = 9 *)
  inversion E1 as [|n2 E2]. (* n2 : nat
                               E2 : es_par 3
                               H : n2 = 3
                               ============================
                               2 + 2 = 9 *)
  inversion E2 as [|n3 E3]. (* n3 : nat
                               E3 : es_par 1
                               H0 : n3 = 1
                               ============================
                               2 + 2 = 9 *)
  inversion E3 as [|n4 E4].
Qed.

(* =====================================================================
   §§ 2.2. Inducción sobre evidencias
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.1. Demostrar que
      forall n : nat,
        es_par n -> exists k, n = doble k.
   ------------------------------------------------------------------ *)

(* 1º intento*)
Lemma es_par_par_1:
  forall n : nat,
    es_par n -> exists k, n = doble k.
Proof.
  intros n E.               (* n : nat
                               E : es_par n
                               ============================
                               exists k : nat, n = doble k *)
  inversion E as [| n' E'].
  -                         (* H : 0 = n
                               ============================
                               exists k : nat, 0 = doble k *)
    exists 0.                    (* 0 = doble 0 *)
    reflexivity.
  -                         (* n' : nat
                               E' : es_par n'
                               H : S (S n') = n
                               ============================
                               exists k : nat, S (S n') = doble k *)
    simpl.                  (* exists k : nat, S (S n') = doble k *)
    assert (I : (exists k', n' = doble k') ->
                (exists k, S (S n') = doble k)).
    +                       (* (exists k' : nat, n' = doble k') ->
                               exists k : nat, S (S n') = doble k *)
      intros [k' Hk'].      (* k' : nat
                               Hk' : n' = doble k'
                               ============================
                               exists k : nat, S (S n') = doble k *)
      rewrite Hk'.          (* exists k : nat, S (S (doble k')) = doble k *)
      exists (S k').             (* S (S (doble k')) = doble (S k') *)
      reflexivity.
    +                       (* I : (exists k' : nat, n' = doble k') ->
                                   exists k : nat, S (S n') = doble k
                               ============================
                               exists k : nat, S (S n') = doble k *)
      apply I.              (* exists k' : nat, n' = doble k' *)
Abort.

(* 2º intento *)
Lemma es_par_par:
  forall n : nat,
    es_par n -> exists k, n = doble k.
Proof.
  intros n E.                 (* n : nat
                                 E : es_par n
                                 ============================
                                 exists k : nat, n = doble k *)
  induction E as [|n' E' HI].
  -                           (* exists k : nat, 0 = doble k *)
    exists 0.                      (* 0 = doble 0 *)
    reflexivity.
  -                           (* n' : nat
                                 E' : es_par n'
                                 HI : exists k : nat, n' = doble k
                                 ============================
                                 exists k : nat, S (S n') = doble k *)
    destruct HI as [k' Hk'].  (* k' : nat
                                 Hk' : n' = doble k'
                                 ============================
                                 exists k : nat, S (S n') = doble k *)
    rewrite Hk'.              (* exists k : nat, S (S (doble k')) = doble k *)
    exists (S k').                 (* S (S (doble k')) = doble (S k') *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.2.2. Demostrar que
      forall n : nat,
        es_par n <-> exists k, n = doble k.
   ------------------------------------------------------------------ *)

Theorem es_par_par_syss:
  forall n : nat,
    es_par n <-> exists k, n = doble k.
Proof.
  intros n.             (* n : nat
                           ============================
                           es_par n <-> (exists k : nat, n = doble k) *)
  split.
  -                     (* es_par n -> exists k : nat, n = doble k *)
    apply es_par_par.
  -                     (* (exists k : nat, n = doble k) -> es_par n *)
    intros [k Hk].      (* n, k : nat
                           Hk : n = doble k
                           ============================
                           es_par n *)
    rewrite Hk.         (* es_par (doble k) *)
    apply es_par_doble.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.1. Demostrar que
      forall n m : nat,
        es_par n -> es_par m -> es_par (n + m).
   ------------------------------------------------------------------ *)

Theorem es_par_suma:
  forall n m : nat,
    es_par n -> es_par m -> es_par (n + m).
Proof.
  intros n m E1 E2.              (* n, m : nat
                                    E1 : es_par n
                                    E2 : es_par m
                                    ============================
                                    es_par (n + m) *)
  induction E1 as [|n' E3 HIn'].
  -                              (* es_par (0 + m) *)
    simpl.                       (* es_par m *)
    apply E2.
  -                              (* m, n' : nat
                                    E3 : es_par n'
                                    E2 : es_par m
                                    HIn' : es_par (n' + m)
                                    ============================
                                    es_par (S (S n') + m) *)
    destruct E2 as [|m' E4].
    +                            (* es_par (S (S n') + 0) *)
      simpl.                     (* es_par (S (S (n' + 0))) *)
      apply es_par_SS.           (* es_par (n' + 0) *)
      apply HIn'.
    +                            (* m' : nat
                                    E4 : es_par m'
                                    HIn' : es_par (n' + S (S m'))
                                    ============================
                                    es_par (S (S n') + S (S m')) *)
      simpl.                     (* es_par (S (S (n' + S (S m')))) *)
      apply es_par_SS.           (* es_par (n' + S (S m')) *)
      apply HIn'.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.2. Se considera la siguiente definición alternativa de
   ser par
      Inductive es_par': nat -> Prop :=
      | es_par'_0    : es_par' 0
      | es_par'_2    : es_par' 2
      | es_par'_suma : forall n m, es_par' n -> es_par' m -> es_par' (n + m).

   Demostrar que
      forall n : nat,
        es_par' n <-> es_par n.
   ------------------------------------------------------------------ *)

Inductive es_par': nat -> Prop :=
  | es_par'_0    : es_par' 0
  | es_par'_2    : es_par' 2
  | es_par'_suma : forall n m, es_par' n -> es_par' m -> es_par' (n + m).

Lemma es_par'_es_par_L1:
  forall n : nat,
    es_par' n -> es_par n.
Proof.
  intros n E.          (* n : nat
                          E : es_par' n
                          ============================
                          es_par n *)
  induction E.
  -                    (* es_par 0 *)
    apply es_par_0.
  -                    (* es_par 2 *)
    apply es_par_SS.   (* es_par 0 *)
    apply es_par_0.
  -                    (* n, m : nat
                          E1 : es_par' n
                          E2 : es_par' m
                          IHE1 : es_par n
                          IHE2 : es_par m
                          ============================
                          es_par (n + m) *)
    apply es_par_suma.
    +                  (* es_par n *)
      apply IHE1.
    +                  (* es_par m *)
      apply IHE2.
Qed.

Lemma es_par'_es_par_L2:
  forall n : nat,
    es_par n -> es_par' n.
Proof.
  intros n E.                 (* n : nat
                                 E : es_par n
                                 ============================
                                 es_par' n *)
  induction E.
  -                           (* es_par' 0 *)
    apply es_par'_0.
  -                           (* IHE : es_par' n
                                 ============================
                                 es_par' (S (S n)) *)
    assert (es_par' (2 + n)).
    +                         (* es_par' (2 + n) *)
      apply es_par'_suma.
      *                       (* es_par' 2 *)
        apply es_par'_2.
      *                       (* es_par' n *)
        apply IHE.
    +                         (* H : es_par' (2 + n)
                                 ============================
                                 es_par' (S (S n)) *)
      apply H.
Qed.

Theorem es_par'_es_par:
  forall n : nat,
    es_par' n <-> es_par n.
Proof.
  split.
  - apply es_par'_es_par_L1.
  - apply es_par'_es_par_L2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.3. Demostrar que
      forall n m : nat,
        es_par (n+m) -> es_par n -> es_par m.
   ------------------------------------------------------------------ *)

Theorem es_par_es_par_es_par:
  forall n m : nat,
    es_par (n+m) -> es_par n -> es_par m.
Proof.
  intros n m Enm En.              (* n, m : nat
                                     Enm : es_par (n + m)
                                     En : es_par n
                                     ============================
                                     es_par m *)
  induction En as [|n' En' HIn'].
  -                               (* Enm : es_par (0 + m)
                                     ============================
                                     es_par m *)
    apply Enm.
  -                               (* m, n' : nat
                                     Enm : es_par (S (S n') + m)
                                     En' : es_par n'
                                     HIn' : es_par (n' + m) -> es_par m
                                     ============================
                                     es_par m *)
    apply HIn'.                   (* es_par (n' + m) *)
    simpl in Enm.                 (* Enm : es_par (S (S (n' + m))) *)
    apply es_parSS_es_par.        (* es_par (S (S (n' + m))) *)
    apply Enm.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.4. Demostrar que
      forall n m p : nat,
        es_par (n+m) -> es_par (n+p) -> es_par (m+p).
   ------------------------------------------------------------------ *)

Theorem es_par_suma_suma:
  forall n m p : nat,
    es_par (n+m) -> es_par (n+p) -> es_par (m+p).
Proof.
  intros n m p H.             (* n, m, p : nat
                                 H : es_par (n + m)
                                 ============================
                                 es_par (n + p) -> es_par (m + p) *)
  apply es_par_es_par_es_par. (* es_par ((n + p) + (m + p))) *)
  rewrite suma_conmutativa.   (* es_par ((m + p) + (n + p)) *)
  rewrite suma_permutada.     (* es_par (n + ((m + p) + p)) *)
  rewrite <- suma_asociativa.  (* es_par (n + (m + (p + p))) *)
  rewrite suma_asociativa.    (* es_par ((n + m) + (p + p)) *)
  apply es_par_suma.
  -                           (* es_par (n + m) *)
    apply H.
  -                           (* es_par (p + p) *)
    rewrite <- doble_suma.     (* es_par (doble p) *)
    apply es_par_doble.
Qed.

(* =====================================================================
   § 3. Relaciones inductivas
   ================================================================== *)


(* ---------------------------------------------------------------------
   Notas.
   1. Las proposiciones con un argumento definen conjuntos; por ejemplo,
      es_par define el conjunto de los números pares.
   2. Las proposiciones con dos argumento definen relaciones.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Nota. Creamos el módulo para redefinir la relación menor o igual
   (definida por le) como menOig.
   ------------------------------------------------------------------ *)

Module RelInd.

(* ---------------------------------------------------------------------
   Ejemplo 3.1. Definir inductivamente la relación
      menOig: nat -> nat -> Prop
   tal que (menOig n m) expresa que n es menor o igual que m.
   ------------------------------------------------------------------ *)

Inductive menOig: nat -> nat -> Prop :=
  | menOig_n : forall n, menOig n n
  | menOig_S : forall n m, (menOig n m) -> (menOig n (S m)).

(* ---------------------------------------------------------------------
   Ejemplo 3.2. Definir (m <= n) como abreviatura de (menOig m n).
   ------------------------------------------------------------------ *)

Notation "m <= n" := (menOig m n).

(* ---------------------------------------------------------------------
   Nota. Sobre la relaciones (p.e. <=) se pueden usar las mismas
   tácticas que sobre las propiedades (p.e. es_par).
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 3.3. Demostrar que
      3 <= 3.
   ------------------------------------------------------------------ *)

Theorem prop_menOig1:
  3 <= 3.
Proof.
  apply menOig_n.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.4. Demostrar que
      3 <= 6.
   ------------------------------------------------------------------ *)

Theorem prop_menOig2 :
  3 <= 6.
Proof.
  apply menOig_S. (* 3 <= 5 *)
  apply menOig_S. (* 3 <= 4 *)
  apply menOig_S. (* 3 <= 3 *)
  apply menOig_n.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.5. Demostrar que
      (2 <= 1) -> 2 + 2 = 5.
   ------------------------------------------------------------------ *)

Theorem prop_menOig3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H.       (* H : 2 <= 1
                     ============================
                     2 + 2 = 5 *)
  inversion H.    (* n, m : nat
                     H2 : 2 <= 0
                     H1 : n = 2
                     H0 : m = 0
                     ============================
                     2 + 2 = 5 *)
  inversion H2.
Qed.

End RelInd.

(* ---------------------------------------------------------------------
   Nota. En lo que sigue, usaremos la predefiida le en lugar de menOig.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 3.6. Definir la relación
      mayor : nat -> nat -> Prop
   tal que (menor m n) expresa que m es menor que n.
   ------------------------------------------------------------------ *)

Definition menor (n m : nat) := le (S n) m.

(* ---------------------------------------------------------------------
   Ejemplo 3.7. Definir la abreviatura (m < n) para (menor m n).
   ------------------------------------------------------------------ *)

Notation "m < n" := (menor m n).

(* ---------------------------------------------------------------------
   Ejemplo 3.8. Definir inductivamente la relación
      cuadrado_de: nat -> nat -> Prop :=
   tal que (cuadrado x y) expresa que y es el cuadrado de x.
   ------------------------------------------------------------------ *)

Inductive cuadrado_de: nat -> nat -> Prop :=
  | cuad : forall n : nat, cuadrado_de n (n * n).

(* ---------------------------------------------------------------------
   Ejemplo 3.9. Definir inductivamente la relación
      siguiente_nat : nat -> nat -> Prop
   tal que (siguiente_nat x y) expresa que y es el siguiente de x.
   ------------------------------------------------------------------ *)

Inductive siguiente_nat : nat -> nat -> Prop :=
  | sn : forall n : nat, siguiente_nat n (S n).

(* ---------------------------------------------------------------------
   Ejemplo 3.9. Definir inductivamente la relación
      siguiente_par : nat -> nat -> Prop :=
   tal que (siguiente_par x y) expresa que y es el siguiente  número par
   de x.
   ------------------------------------------------------------------ *)

Inductive siguiente_par : nat -> nat -> Prop :=
  | sp_1 : forall n, es_par (S n) -> siguiente_par n (S n)
  | sp_2 : forall n, es_par (S (S n)) -> siguiente_par n (S (S n)).

(* ---------------------------------------------------------------------
   Ejercicio 3.1. Definir inductivamente la relación
      relacion_total : nat -> nat -> Prop
   que expresa que todos los elementos están relacionados.
   ------------------------------------------------------------------ *)

Inductive relacion_total : nat -> nat -> Prop :=
  | rt : forall n m : nat, relacion_total n m.

(* ---------------------------------------------------------------------
   Ejercicio 3.2. Definir inductivamente la relación
      relacion_vacia : nat -> nat -> Prop
   que expresa que ningún par de elementos están relacionados.
   ------------------------------------------------------------------ *)

Inductive relacion_vacia : nat -> nat -> Prop :=
  .

(* ---------------------------------------------------------------------
   Ejercicio 3.3.1. En los distintos apartados de este ejercicio se
   demostrarán propiedades de las relaciones <= y <.

   Demostrar que
      forall m n o  : nat,
        m <= n -> n <= o -> m <= o.
   ------------------------------------------------------------------ *)

Lemma le_trans :
  forall m n o  : nat,
    m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Emn Eno.     (* m, n, o : nat
                               Emn : m <= n
                               Eno : n <= o
                               ============================
                               m <= o *)
  generalize dependent Emn. (* m <= n -> m <= o *)
  generalize dependent m.   (* forall m : nat, m <= n -> m <= o *)
  induction Eno.
  -                         (* forall m : nat, m <= n -> m <= n *)
    intros.                 (* n, m : nat
                               Emn : m <= n
                               ============================
                               m <= n *)
    apply Emn.
  -                         (* n, m : nat
                               Eno : n <= m
                               IHEno : forall m0 : nat, m0 <= n -> m0 <= m
                               ============================
                               forall m0 : nat, m0 <= n -> m0 <= S m *)
    intros.                 (* m0 : nat
                               Emn : m0 <= n
                               ============================
                               m0 <= S m *)
    apply le_S.             (* m0 <= m *)
    apply IHEno.            (* m0 <= n *)
    apply Emn.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.2. Demostrar que
      forall n : nat,
        0 <= n.
   ------------------------------------------------------------------ *)

Theorem O_le_n :
  forall n : nat,
    0 <= n.
Proof.
  intros n.                (* n : nat
                              ============================
                              0 <= n *)
  induction n as [|n' HI].
  -                        (* 0 <= 0 *)
    apply le_n.
  -                        (* n' : nat
                              HI : 0 <= n'
                              ============================
                              0 <= S n' *)
    apply le_S.            (* 0 <= n' *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.3. Demostrar que
      forall n m,
        n <= m -> S n <= S m.
   ------------------------------------------------------------------ *)

Theorem n_le_m__Sn_le_Sm :
  forall n m,
    n <= m -> S n <= S m.
Proof.
  intros n m E.               (* n, m : nat
                                 E : n <= m
                                 ============================
                                 S n <= S m *)
  induction E as [|n' E' HI].
  -                           (* S n <= S n *)
    apply le_n.
  -                           (* n, n' : nat
                                 E' : n <= n'
                                 HI : S n <= S n'
                                 ============================
                                 S n <= S (S n') *)
    apply le_S.               (* S n <= S n' *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.4. Demostrar que
      forall n m : nat,
        S n <= S m -> n <= m.
   ------------------------------------------------------------------ *)

Lemma n_le_Sn :
  forall n : nat,
    n <= S n.
Proof.
  intros.     (* n : nat
                 ============================
                 n <= S n *)
  apply le_S. (* n <= n *)
  apply le_n.
Qed.

Theorem Sn_le_Sm__n_le_m :
  forall n m : nat,
    S n <= S m -> n <= m.
Proof.
  intros n m E.                     (* n, m : nat
                                       E : S n <= S m
                                       ============================
                                       n <= m *)
  inversion E.
  -                                 (* H0 : n = m
                                       ============================
                                       m <= m *)
    apply le_n.
  -                                 (* m0 : nat
                                       H0 : S n <= m
                                       H : m0 = m
                                       ============================
                                       n <= m *)
    apply le_trans with (n := S n).
    +                               (* n <= S n *)
      apply n_le_Sn.
    +                               (* S n <= m *)
      apply H0.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.5. Demostrar que
      forall a b : nat,
        a <= a + b.
   ------------------------------------------------------------------ *)

Theorem le_suma_i :
  forall a b : nat,
    a <= a + b.
Proof.
  intros.                   (* a, b : nat
                               ============================
                               a <= a + b *)
  induction a as [|a' HI].
  -                         (* 0 <= 0 + b *)
    apply O_le_n.
  -                         (* a', b : nat
                               HI : a' <= a' + b
                               ============================
                               S a' <= S a' + b *)
    simpl.                  (* S a' <= S (a' + b) *)
    apply n_le_m__Sn_le_Sm. (* a' <= a' + b *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.6. Demostrar que
      forall n1 n2 m : nat,
        n1 + n2 < m ->
        n1 < m /\ n2 < m.
   ------------------------------------------------------------------ *)

Theorem suma_menor :
  forall n1 n2 m : nat,
    n1 + n2 < m ->
    n1 < m /\ n2 < m.
Proof.
  unfold menor.                 (*
                                   ============================
                                   forall n1 n2 m : nat,
                                    S (n1 + n2) <= m ->
                                    S n1 <= m /\ S n2 <= m *)
  intros n1 n2 m H.             (* n1, n2, m : nat
                                   H : S (n1 + n2) <= m
                                   ============================
                                   S n1 <= m /\ S n2 <= m *)
  split.
  -                             (* S n1 <= m *)
    induction H.
    +                           (* S n1 <= S (n1 + n2) *)
      apply n_le_m__Sn_le_Sm.   (* n1 <= n1 + n2 *)
      apply le_suma_i.
    +                           (* IHle : S n1 <= m
                                   ============================
                                   S n1 <= S m *)
      apply le_S.               (* S n1 <= m *)
      apply IHle.
  -                             (* S n2 <= m *)
    induction H.
    +                           (* S n2 <= S (n1 + n2) *)
      apply n_le_m__Sn_le_Sm.   (* n2 <= n1 + n2 *)
      rewrite suma_conmutativa. (* n2 <= n2 + n1 *)
      apply le_suma_i.
    +                           (* IHle : S n2 <= m
                                   ============================
                                   S n2 <= S m *)
      apply le_S.               (* S n2 <= m *)
      apply IHle.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.7. Demostrar que
      forall n m : nat,
        n < m ->
        n < S m.
   ------------------------------------------------------------------ *)

Theorem menor_S :
  forall n m : nat,
    n < m ->
    n < S m.
Proof.
  unfold menor. (*
                   ============================
                   forall n m : nat, S n <= m -> S n <= S m *)
  intros n m H. (* n, m : nat
                   H : S n <= m
                   ============================
                   S n <= S m *)
  apply le_S.   (* S n <= m *)
  apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.8. Demostrar que
      forall n m : nat,
        menor_o_igual n m = true -> n <= m.
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_adecuado :
  forall n m : nat,
    menor_o_igual n m = true -> n <= m.
Proof.
  intros n.                   (* n : nat
                                 ============================
                                 forall m : nat,
                                  menor_o_igual n m = true -> n <= m *)
  induction n as [|n' HIn'].
  -                           (* forall m : nat,
                                  menor_o_igual 0 m = true -> 0 <= m *)
    intros.                   (* m : nat
                                 H : menor_o_igual 0 m = true
                                 ============================
                                 0 <= m *)
    apply O_le_n.
  -                           (* n' : nat
                                 HIn' : forall m : nat,
                                         menor_o_igual n' m = true -> n' <= m
                                 ============================
                                 forall m : nat,
                                  menor_o_igual (S n') m = true -> S n' <= m *)
    destruct m as [|m'].
    +                         (* menor_o_igual (S n') 0 = true -> S n' <= 0 *)
      simpl.                  (* false = true -> S n' <= 0 *)
      intros H.               (* H : false = true
                                 ============================
                                 S n' <= 0 *)
      inversion H.
    +                         (* m' : nat
                                 ============================
                                 menor_o_igual (S n') (S m') = true ->
                                 S n' <= S m *)
      simpl.                  (* menor_o_igual n' m' = true -> S n' <= S m' *)
      intros.                 (* H : menor_o_igual n' m' = true
                                 ============================
                                 S n' <= S m' *)
      apply n_le_m__Sn_le_Sm. (* n' <= m' *)
      apply HIn'.             (* menor_o_igual n' m' = true *)
      apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.9. Demostrar que
      forall n m : nat,
        n <= m ->
        menor_o_igual n m = true.
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_correcto :
  forall n m : nat,
    n <= m ->
    menor_o_igual n m = true.
Proof.
  intros.                 (* n, m : nat
                             H : n <= m
                             ============================
                             menor_o_igual n m = true *)
  generalize dependent n. (* m : nat
                             ============================
                             forall n : nat,
                              n <= m -> menor_o_igual n m = true *)
  induction m.
  -                       (* forall n : nat,
                              n <= 0 -> menor_o_igual n 0 = true *)
    intros n H.           (* n : nat
                             H : n <= 0
                             ============================
                             menor_o_igual n 0 = true *)
    inversion H.          (* H0 : n = 0
                             ============================
                             menor_o_igual 0 0 = true *)
    simpl.                (* true = true *)
    reflexivity.
  -                       (* m : nat
                             IHm : forall n : nat,
                                    n <= m -> menor_o_igual n m = true
                             ============================
                             forall n : nat,
                              n <= S m -> menor_o_igual n (S m) = true *)
    destruct n.
    +                     (* 0 <= S m -> menor_o_igual 0 (S m) = true *)
      simpl.              (* 0 <= S m -> true = true *)
      intros.             (* H : 0 <= S m
                             ============================
                             true = true *)
      reflexivity.
    +                     (* n : nat
                             ============================
                             S n <= S m -> menor_o_igual (S n) (S m) = true *)
      intros.             (* H : S n <= S m
                             ============================
                             menor_o_igual (S n) (S m) = true *)
      simpl.              (* menor_o_igual n m = true *)
      apply IHm.          (* n <= m *)
      apply le_S_n.       (* S n <= S m *)
      apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.10. Demostrar que
      forall n m o : nat,
        menor_o_igual n m = true ->
        menor_o_igual m o = true ->
        menor_o_igual n o = true.
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_true_trans :
  forall n m o : nat,
    menor_o_igual n m = true ->
    menor_o_igual m o = true ->
    menor_o_igual n o = true.
Proof.
  intros n m o Hnm Hmo.                  (* n, m, o : nat
                                            Hnm : menor_o_igual n m = true
                                            Hmo : menor_o_igual m o = true
                                            ============================
                                            menor_o_igual n o = true *)
  apply menor_o_igual_correcto.          (* n <= o *)
  apply le_trans with (n := m).
  -                                      (* n <= m *)
    apply menor_o_igual_adecuado in Hnm. (* Hnm : n <= m *)
    apply Hnm.
  -
    apply menor_o_igual_adecuado in Hmo. (* Hmo : m <= o *)
    apply Hmo.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.3.11. Demostrar que
      forall n m : nat,
        menor_o_igual n m = true <-> n <= m.
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_syss :
  forall n m : nat,
    menor_o_igual n m = true <-> n <= m.
Proof.
  split.
  - apply menor_o_igual_adecuado.
  - apply menor_o_igual_correcto.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.1. Se considera la relación
      R : nat -> nat -> nat -> Prop
   definida inductivamente por
      Inductive R : nat -> nat -> nat -> Prop :=
         | c1 : R 0 0 0
         | c2 : forall m n o, R m n o -> R (S m) n (S o)
         | c3 : forall m n o, R m n o -> R m (S n) (S o)
         | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
         | c5 : forall m n o, R m n o -> R n m o.

   Demostrar que
      R 1 1 2.
   ------------------------------------------------------------------ *)

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Theorem R112 : R 1 1 2.
Proof.
  apply c2. (* R 0 1 1 *)
  apply c3. (* R 0 0 0 *)
  apply c1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.2. Definir una función
      fR (m:nat) (n:nat) : nat
   tal que se verifique
      forall m n o : nat, R m n o <-> fR m n = o
   y demostrar dicha propiedad
   ------------------------------------------------------------------ *)

Definition fR (m:nat) (n:nat) : nat :=
  m + n.

Theorem R_equiv_fR_L1 :
  forall m n o : nat,
    R m n o -> fR m n = o.
Proof.
  intros.                           (* m, n, o : nat
                                       H : R m n o
                                       ============================
                                       fR m n = o *)
  unfold fR.                        (* m + n = o *)
  induction H.
  -                                 (* 0 + 0 = 0 *)
    simpl.                          (* 0 = 0 *)
    reflexivity.
  -                                 (* IHR : m + n = o
                                       ============================
                                       S m + n = S o *)
    simpl.                          (* S (m + n) = S o *)
    rewrite IHR.                    (* S o = S o *)
    reflexivity.
  -                                 (* IHR : m + n = o
                                       ============================
                                       m + S n = S o *)
    rewrite suma_conmutativa.       (* S n + m = S o *)
    simpl.                          (* S (n + m) = S o *)
    rewrite <- IHR.                  (* S (n + m) = S (m + n) *)
    rewrite suma_conmutativa.       (* S (m + n) = S (m + n) *)
    reflexivity.
  -                                 (* IHR : S m + S n = S (S o)
                                       ============================
                                       m + n = o *)
    simpl in IHR.                   (* IHR : S (m + S n) = S (S o)
                                       ============================
                                       m + n = o *)
    inversion IHR.                  (* H1 : m + S n = S o
                                       ============================
                                       m + n = o *)
    rewrite suma_conmutativa in H1. (* H1 : S n + m = S o
                                       ============================
                                       m + n = o *)
    simpl in H1.                    (* H1 : S (n + m) = S o
                                       ============================
                                       m + n = o *)
    inversion H1.                   (* H2 : n + m = o
                                       ============================
                                       m + n = n + m *)
    rewrite suma_conmutativa.       (* n + m = n + m *)
    reflexivity.
  -                                 (* IHR : m + n = o
                                       ============================
                                       n + m = o *)
    rewrite suma_conmutativa.       (* m + n = o *)
    apply IHR.
Qed.

Theorem R_equiv_fR_L2a :
  forall n : nat, R 0 n n.
Proof.
  induction n as [|n' HI].
  -                        (* R 0 0 0 *)
    apply c1.
  -                        (* n' : nat
                              HI : R 0 n' n'
                              ============================
                              R 0 (S n') (S n') *)
    apply c3.              (* R 0 n' n' *)
    apply HI.
Qed.

Theorem R_equiv_fR_L2 :
  forall m n o : nat,
    fR m n = o -> R m n o.
Proof.
  intros m.                (* m : nat
                              ============================
                              forall n o : nat, fR m n = o -> R m n o *)
  unfold fR.               (* forall n o : nat, m + n = o -> R m n o *)
  induction m as [|m' HI].
  -                        (* forall n o : nat, 0 + n = o -> R 0 n o *)
    simpl.                 (* forall n o : nat, n = o -> R 0 n o *)
    intros.                (* n, o : nat
                              H : n = o
                              ============================
                              R 0 n o *)
    rewrite H.             (* R 0 o o *)
    apply R_equiv_fR_L2a.
  -                        (* m' : nat
                              HI : forall n o : nat, m' + n = o -> R m' n o
                              ============================
                              forall n o:nat, S m' + n = o -> R (S m') n o *)
    simpl.                 (* forall n o:nat, S (m' + n) = o -> R (S m') n o *)
    intros.                (* n, o : nat
                              H : S (m' + n) = o
                              ============================
                              R (S m') n o *)
    rewrite <- H.           (* R (S m') n (S (m' + n)) *)
    apply c2.              (* R m' n (m' + n) *)
    apply HI.              (* m' + n = m' + n *)
    reflexivity.
Qed.

Theorem R_equiv_fR :
  forall m n o : nat,
    R m n o <-> fR m n = o.
Proof.
  split.
  - apply R_equiv_fR_L1.
  - apply R_equiv_fR_L2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.3. Demostrar que
      ~(R 2 2 6)
   ------------------------------------------------------------------ *)

Theorem R_226 : ~(R 2 2 6).
Proof.
  rewrite R_equiv_fR. (* fR 2 2 <> 6 *)
  unfold fR.          (* 2 + 2 <> 6 *)
  intros H.           (* H : 2 + 2 = 6
                         ============================
                         False *)
  inversion H.
Qed.

End R.

(* ---------------------------------------------------------------------
   Ejercicio 3.5.1. Una lista xs es sublista de ys si todos los
   elementos de xs ocurren en ys en el mismo orden, posiblemente con
   algunos elementos entre ellos. Por ejemplo,
      [1;2;3]
   es sublista de cada una de las siguientes
      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]
   pero no es sublista de ninguna de las siguiente
      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

   Definir inductivamente la propiedad
      sublista {X : Type} : list X -> list X -> Prop
   tal que (sublista xs ys) expresa que xs es una sublista de ys.
   ------------------------------------------------------------------ *)

Inductive sublista {X : Type} : list X -> list X -> Prop :=
  | sl1 : forall xs, sublista nil xs
  | sl2 : forall x xs ys, sublista xs ys -> sublista (x :: xs) (x :: ys)
  | sl3 : forall x xs ys, sublista xs ys -> sublista xs (x :: ys).

(* ---------------------------------------------------------------------
   Ejercicio 3.5.2. Demostrar que
      forall (X :Type) (xs : list X),
        sublista xs xs.
   ------------------------------------------------------------------ *)

Theorem sublista_refl :
  forall (X :Type) (xs : list X),
    sublista xs xs.
Proof.
  intros X xs.                 (* X : Type
                                  xs : list X
                                  ============================
                                  sublista xs xs *)
  induction xs as [|x xs' HI].
  -                            (* sublista [ ] [ ] *)
    apply sl1.
  -                            (* x : X
                                  xs' : list X
                                  HI : sublista xs' xs'
                                  ============================
                                  sublista (x :: xs') (x :: xs') *)
    apply sl2.                 (* sublista xs' xs' *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.5.3. Demostrar que
      forall (X : Type) (xs ys zs : list X),
        sublista xs ys -> sublista xs (ys ++ zs).
   ------------------------------------------------------------------ *)

Theorem sublista_conc :
  forall (X : Type) (xs ys zs : list X),
    sublista xs ys -> sublista xs (ys ++ zs).
Proof.
  intros X xs ys zs H.               (* X : Type
                                        xs, ys, zs : list X
                                        H : sublista xs ys
                                        ============================
                                        sublista xs (ys ++ zs) *)
  induction H as [ xs'
                 | x xs' ys' H' HI
                 | x xs' ys' H' HI].
  -                                  (* X : Type
                                        zs, xs' : list X
                                        ============================
                                        sublista [ ] (xs' ++ zs) *)
    apply sl1.
  -                                  (* x : X
                                        xs', ys' : list X
                                        H' : sublista xs' ys'
                                        HI : sublista xs' (ys' ++ zs)
                                        ============================
                                        sublista (x::xs') ((x::ys') ++ zs) *)
    simpl.                           (* sublista (x::xs') (x::(ys' ++ zs)) *)
    apply sl2.                       (* sublista xs' (ys' ++ zs) *)
    apply HI.
  -                                  (* x : X
                                        xs', ys' : list X
                                        H' : sublista xs' ys'
                                        HI : sublista xs' (ys' ++ zs)
                                        ============================
                                        sublista xs' ((x :: ys') ++ zs) *)
    simpl.                           (* sublista xs' (x :: (ys' ++ zs)) *)
    apply sl3.                       (* sublista xs' (ys' ++ zs) *)
    apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.5.4. Demostrar que
      forall (X :Type) (xs ys zs : list X),
        sublista xs ys ->
        sublista ys zs ->
        sublista xs zs.
   ------------------------------------------------------------------ *)

Theorem sublista_trans :
  forall (X :Type) (xs ys zs : list X),
    sublista xs ys ->
    sublista ys zs ->
    sublista xs zs.
Proof.
  intros X xs ys zs H12 H23.             (* X : Type
                                            xs, ys, zs : list X
                                            H12 : sublista xs ys
                                            H23 : sublista ys zs
                                            ============================
                                            sublista xs zs *)
  generalize dependent H12.              (* X : Type
                                            xs, ys, zs : list X
                                            H23 : sublista ys zs
                                            ============================
                                            sublista xs ys -> sublista xs zs *)
  generalize dependent xs.               (* forall xs : list X,
                                             sublista xs ys -> sublista xs zs *)
  induction H23 as [ xs'
                   | x xs' ys' H23' HI
                   | x xs' ys' H23' HI].
  -                                      (* xs' : list X
                                            ============================
                                            forall xs : list X,
                                             sublista xs [ ] ->
                                             sublista xs xs' *)
    intros.                              (* xs', xs : list X
                                            H12 : sublista xs [ ]
                                            ============================
                                            sublista xs xs' *)
    inversion H12.                       (* xs0 : list X
                                            H : [ ] = xs
                                            H0 : xs0 = [ ]
                                            ============================
                                            sublista [ ] xs' *)
    apply sl1.
  -                                      (* x : X
                                            xs', ys' : list X
                                            H23' : sublista xs' ys'
                                            HI : forall xs : list X,
                                                  sublista xs xs' ->
                                                  sublista xs ys'
                                            ============================
                                            forall xs : list X,
                                             sublista xs (x :: xs') ->
                                             sublista xs (x :: ys') *)
    intros.                              (* xs : list X
                                            H12 : sublista xs (x :: xs')
                                            ============================
                                            sublista xs (x :: ys') *)
    inversion H12.
    +                                    (* xs0 : list X
                                            H : [ ] = xs
                                            H0 : xs0 = x :: xs'
                                            ============================
                                            sublista [ ] (x :: ys') *)
      apply sl1.
    +                                    (* xs : list X
                                            H12 : sublista xs (x :: xs')
                                            x0 : X
                                            xs0, ys : list X
                                            H1 : sublista xs0 xs'
                                            H0 : x0 :: xs0 = xs
                                            H : x0 = x
                                            H2 : ys = xs'
                                            ============================
                                            sublista (x :: xs0) (x :: ys') *)
      apply sl2.                         (* sublista xs0 ys' *)
      apply HI.                          (* sublista xs0 xs' *)
      apply H1.
    +                                    (* xs : list X
                                            H12 : sublista xs (x :: xs')
                                            x0 : X
                                            xs0, ys : list X
                                            H1 : sublista xs xs'
                                            H0 : xs0 = xs
                                            H : x0 = x
                                            H2 : ys = xs'
                                            ============================
                                            sublista xs (x :: ys') *)
      apply sl3.                         (* sublista xs ys' *)
      apply HI.                          (* sublista xs xs' *)
      apply H1.
  -                                      (* x : X
                                            xs', ys' : list X
                                            H23' : sublista xs' ys'
                                            HI : forall xs : list X,
                                                  sublista xs xs' ->
                                                  sublista xs ys'
                                            ============================
                                            forall xs : list X,
                                             sublista xs xs' ->
                                             sublista xs (x :: ys') *)
    intros.                              (* xs : list X
                                            H12 : sublista xs xs'
                                            ============================
                                            sublista xs (x :: ys') *)
    apply sl3.                           (* sublista xs ys' *)
    apply HI.                            (* sublista xs xs' *)
    apply H12.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.6.1. Se condidera la relación R definida inductivamente por
      Inductive R : nat -> list nat -> Prop :=
        | c1 : R 0 []
        | c2 : forall n l, R n l -> R (S n) (n :: l)
        | c3 : forall n l, R (S n) l -> R n l.

   Demostrar que
      R 2 [1;0]
   ------------------------------------------------------------------ *)

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

Theorem R1 : R 2 [1;0].
Proof.
  apply c2. (* R 1 [0] *)
  apply c2. (* R 0 [ ] *)
  apply c1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.6.2. Demostrar que
      R 1 [1;2;1;0].
   ------------------------------------------------------------------ *)

Theorem R2 : R 1 [1;2;1;0].
Proof.
  apply c3. (* R 2 [1; 2; 1; 0] *)
  apply c2. (* R 1 [2; 1; 0] *)
  apply c3. (* R 2 [2; 1; 0] *)
  apply c3. (* R 3 [2; 1; 0] *)
  apply c2. (* R 2 [1; 0] *)
  apply c2. (* R 1 [0] *)
  apply c2. (* R 0 [ ] *)
  apply c1.
Qed.

(* =====================================================================
   § 4. Caso de estudio:Expresiones regulares
   ================================================================== *)

(* =====================================================================
   §§ 4.1. Introducción
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1.1. Definir inductivamente la proposición reg_exp para
   representar las expresiones regulares.
   ------------------------------------------------------------------ *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet : reg_exp
  | EmptyStr : reg_exp
  | Char     : T -> reg_exp
  | App      : reg_exp -> reg_exp -> reg_exp
  | Union    : reg_exp -> reg_exp -> reg_exp
  | Star     : reg_exp -> reg_exp.


(* ---------------------------------------------------------------------
   Nota. La coincidencia entre expresiones regulares y cadenas es la
   siguiente:
   - EmptySet no coincide con ninguna cadena.

   - EmptyStr coincide con la cadena vavía [].

   - (Char x) coincide con la cadena cuyo único elemento es x, [x]-

   - Si e1 coincide con s1 y e2 con s2, entonces [App e1 e2]
     coincide con (s1 ++ s2).

   - Si e1 o e2 coincide con s, entonces (Union e1 e2) también
     coincide con s.

   - Si la cadena s se puede escribir como (s1 ++ ... ++ sk) y la
     expresión e coincide con cada una de las si, entonces (Star e)
     coincide con s.

   - (Star e) coincide con la cadena vacía.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1.2. Definir inductivamente la proposición
      exp_match {T} : list T -> reg_exp -> Prop
   tal que (exp_match xs e) expresa que la expresión regualar e coincide
   con la cadena xs.
   ------------------------------------------------------------------ *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty   : exp_match [] EmptyStr
  | MChar    : forall x, exp_match [x] (Char x)
  | MApp     : forall s1 re1 s2 re2,
                 exp_match s1 re1 ->
                 exp_match s2 re2 ->
                 exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL  : forall s1 re1 re2,
                 exp_match s1 re1 ->
                 exp_match s1 (Union re1 re2)
  | MUnionR  : forall re1 s2 re2,
                 exp_match s2 re2 ->
                 exp_match s2 (Union re1 re2)
  | MStar0   : forall re, exp_match [] (Star re)
  | MStarApp : forall s1 s2 re,
                 exp_match s1 re ->
                 exp_match s2 (Star re) ->
                 exp_match (s1 ++ s2) (Star re).
(* ---------------------------------------------------------------------
   Ejemplo 4.1.3. Definir la abreviatura (s =~ e) para (exp_match s e).
   ------------------------------------------------------------------ *)

Notation "s =~ e" := (exp_match s e) (at level 80).

(* ---------------------------------------------------------------------
   Nota. Las reglas de coincidencia son

       ----------------                     (MEmpty)
        [] =~ EmptyStr

       ---------------                      (MChar)
        [x] =~ Char x

         s1 =~ re1    s2 =~ re2
        -------------------------           (MApp)
         s1 ++ s2 =~ App re1 re2

              s1 =~ re1
        ---------------------               (MUnionL)
         s1 =~ Union re1 re2

              s2 =~ re2
        ---------------------               (MUnionR)
         s2 =~ Union re1 re2

        ---------------                     (MStar0)
         [] =~ Star re

         s1 =~ re    s2 =~ Star re
        ---------------------------         (MStarApp)
           s1 ++ s2 =~ Star re
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1.4. Demostrar que
      [1] =~ Char 1.
   ------------------------------------------------------------------ *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.5. Demostrar que
      [1; 2] =~ App (Char 1) (Char 2).
   ------------------------------------------------------------------ *)

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  -                       (* [1] =~ Char 1 *)
    apply MChar.
  -                       (* [2] =~ Char 2 *)
    apply MChar.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.6. Demostrar que
      ~ ([1; 2] =~ Char 1).
   ------------------------------------------------------------------ *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H.    (* H : [1; 2] =~ Char 1
                  ============================
                  False *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.7. Definir la función
      reg_exp_of_list {T} (xs : list T) :=
   tal que (reg_exp_of_list xs) es una expresión regular e tal que xs
   coincide con e. Por ejemplo,

      Compute (reg_exp_of_list [1; 2; 3]).
      = App (Char 1) (App (Char 2) (App (Char 3) EmptyStr))
   ------------------------------------------------------------------ *)

Fixpoint reg_exp_of_list {T} (xs : list T) :=
  match xs with
  | []       => EmptyStr
  | x :: xs' => App (Char x) (reg_exp_of_list xs')
  end.

Compute (reg_exp_of_list [1; 2; 3]).
(* = App (Char 1) (App (Char 2) (App (Char 3) EmptyStr)) *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1.8. Demostrar que
      [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
   ------------------------------------------------------------------ *)

Example reg_exp_ex4 :
  [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  -                        (* [1] =~ Char 1 *)
    apply MChar.
  -                        (* [2; 3] =~ App (Char 2) (App (Char 3) EmptyStr) *)
    apply (MApp [2]).
    +                      (* [2] =~ Char 2 *)
      apply MChar.
    +                      (* [3] =~ App (Char 3) EmptyStr *)
      apply (MApp [3]).
      *                    (* [3] =~ Char 3 *)
        apply MChar.
      *                    (* [ ] =~ EmptyStr *)
        apply MEmpty.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.9. Demostrar que si la cadena s coincide con la expresión
   regular e, entonces también coincide con (Star e).
   ------------------------------------------------------------------ *)

Lemma MStar1 :
  forall T s (e : @reg_exp T) ,
    s =~ e ->
    s =~ Star e.
Proof.
  intros T s e H.           (* T : Type
                               s : list T
                               e : reg_exp
                               H : s =~ e
                               ============================
                               s =~ Star e *)
  rewrite <- (conc_nil _ s). (* s ++ [ ] =~ Star e *)
  apply (MStarApp s [] e).
  -                         (* s =~ e *)
    apply H.
  -                         (* [ ] =~ Star e *)
    apply MStar0.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de (rewrite <- (conc_nil _ s)) para transformar la
   expresión en la forma conveniente para aplicar la regla MStarApp.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 4.1.1.1. Demostrar que ninguna cadena coincide con EmptySet
   ------------------------------------------------------------------ *)

Lemma empty_is_empty :
  forall T (s : list T),
    ~ (s =~ EmptySet).
Proof.
  intros T s H. (* T : Type
                   s : list T
                   H : s =~ EmptySet
                   ============================
                   False *)
  inversion H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.1.1.2. Demostrar que si una cadena coincide con alguna de
   las expresiones regulares e1 o e2, entonces también coincide con
   (Union e1 e2).
   ------------------------------------------------------------------ *)

Lemma MUnion' :
  forall T (s : list T) (e1 e2 : @reg_exp T),
    s =~ e1 \/ s =~ e2 ->
    s =~ Union e1 e2.
Proof.
  intros T s e1 e2 [H1 | H2].
  -                           (* T : Type
                                 s : list T
                                 e1, e2 : reg_exp
                                 H1 : s =~ e1
                                 ============================
                                 s =~ Union e1 e2 *)
    apply (MUnionL s e1).     (* s =~ e1 *)
    apply H1.
  -                           (* T : Type
                                 s : list T
                                 e1, e2 : reg_exp
                                 H2 : s =~ e2
                                 ============================
                                 s =~ Union e1 e2 *)
    apply (MUnionR _ s e2).   (* s =~ e2 *)
    apply H2.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.1.1.3. Demostrar que
      forall T (ss : list (list T)) (re : reg_exp),
        (forall s, In s ss -> s =~ re) ->
        fold app ss [] =~ Star re.
   ------------------------------------------------------------------ *)

Lemma MStar' :
  forall T (xss : list (list T)) (e : reg_exp),
    (forall xs, En xs xss -> xs =~ e) ->
    fold conc xss [] =~ Star e.
Proof.
  intros T xss e H. (* T : Type
                       xss : list (list T)
                       e : reg_exp
                       H : forall xs : list T, En xs xss -> xs =~ e
                       ============================
                       fold conc xss [ ] =~ Star e *)
  induction xss as [|xs' xss' HI].
  -                 (* H : forall xs : list T, En xs [ ] -> xs =~ e
                       ============================
                       fold conc [ ] [ ] =~ Star e *)
    simpl.          (* [ ] =~ Star e *)
    apply MStar0.
  -                 (* xs' : list T
                       xss' : list (list T)
                       e : reg_exp
                       H : forall xs : list T, En xs (xs' :: xss') -> xs =~ e
                       HI : (forall xs : list T, En xs xss' -> xs =~ e) ->
                            fold conc xss' [ ] =~ Star e
                       ============================
                       fold conc (xs' :: xss') [ ] =~ Star e *)
    simpl.          (* xs' ++ fold conc xss' [ ] =~ Star e *)
    apply (MStarApp xs' (fold conc xss' [ ]) e).
    +               (* xs' =~ e *)
      apply H.      (* En xs' (xs' :: xss') *)
      simpl.        (* xs' = xs' \/ En xs' xss' *)
      left.         (* xs' = xs' *)
      reflexivity.
    +               (* fold conc xss' [ ] =~ Star e *)
      apply HI.     (* forall xs : list T, En xs xss' -> xs =~ e *)
      intros xs H1. (* xs : list T
                       H1 : En xs xss'
                       ============================
                       xs =~ e *)
      apply H.      (* En xs (xs' :: xss') *)
      simpl.        (* xs' = xs \/ En xs xss' *)
      right.        (* En xs xss' *)
      apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.1.2. Demostrar que
      forall T (s1 s2 : list T),
        s1 =~ reg_exp_of_list s2 <-> s1 = s2.
   ------------------------------------------------------------------ *)

Lemma reg_exp_of_list_spec_L1 :
  forall T (s1 s2 : list T),
    s1 =~ reg_exp_of_list s2 -> s1 = s2.
Proof.
  intros.                  (* T : Type
                              s1, s2 : list T
                              H : s1 =~ reg_exp_of_list s2
                              ============================
                              s1 = s2 *)
  generalize dependent s1. (* forall s1 : list T,
                               s1 =~ reg_exp_of_list s2 -> s1 = s2 *)
  induction s2.
  -                        (* forall s1 : list T,
                               s1 =~ reg_exp_of_list [ ] -> s1 = [ ] *)
    intros.                (* s1 : list T
                              H : s1 =~ reg_exp_of_list [ ]
                              ============================
                              s1 = [ ] *)
    inversion H.           (* H0 : [ ] = s1
                              ============================
                              [ ] = [ ] *)
    reflexivity.
  -                        (* x : T
                              s2 : list T
                              IHs2 : forall s1 : list T,
                                      s1 =~ reg_exp_of_list s2 -> s1 = s2
                              ============================
                              forall s1 : list T,
                               s1 =~ reg_exp_of_list (x::s2) -> s1 = x::s2 *)
    intros.                (* s1 : list T
                              H : s1 =~ reg_exp_of_list (x :: s2)
                              ============================
                              s1 = x :: s2 *)
    inversion H.           (* s0 : list T
                              re1 : reg_exp
                              s3 : list T
                              re2 : reg_exp
                              H3 : s0 =~ Char x
                              H4 : s3 =~ reg_exp_of_list s2
                              H2 : s0 ++ s3 = s1
                              H0 : re1 = Char x
                              H1 : re2 = reg_exp_of_list s2
                              ============================
                              s0 ++ s3 = x :: s2 *)
    inversion H3.          (* x0 : T
                              H5 : [x0] = s0
                              H7 : x0 = x
                              ============================
                              [x] ++ s3 = x :: s2 *)
    subst.                 (*   s3 : list T
                              H : [x] ++ s3 =~ reg_exp_of_list (x :: s2)
                              H3 : [x] =~ Char x
                              H4 : s3 =~ reg_exp_of_list s2
                              ============================
                              [x] ++ s3 = x :: s2 *)
    simpl.                 (* x :: s3 = x :: s2 *)
    simpl in H.            (* H : x::s3 =~ App (Char x) (reg_exp_of_list s2)
                              ============================
                              x :: s3 = x :: s2 *)
    apply f_equal.         (* s3 = s2 *)
    apply IHs2.            (* s3 =~ reg_exp_of_list s2 *)
    apply H4.
Qed.

Lemma conc_unitaria :
  forall (T : Type) (x : T) (xs : list T),
    x :: xs = [x] ++ xs.
Proof.
  reflexivity.
Qed.

Lemma reg_exp_of_list_spec_L2 :
  forall T (s1 s2 : list T),
    s1 = s2 -> s1 =~ reg_exp_of_list s2.
Proof.
  intros.                  (* T : Type
                              s1, s2 : list T
                              H : s1 = s2
                              ============================
                              s1 =~ reg_exp_of_list s2 *)
  generalize dependent s2. (* forall s2 : list T,
                               s1 = s2 -> s1 =~ reg_exp_of_list s2 *)
  induction s1.
  -                        (* forall s2 : list T,
                               [ ] = s2 -> [ ] =~ reg_exp_of_list s2 *)
    intros.                (* s2 : list T
                              H : [ ] = s2
                              ============================
                              [ ] =~ reg_exp_of_list s2 *)
    inversion H.           (* H, H0 : [ ] = s2
                              ============================
                              [ ] =~ reg_exp_of_list [ ] *)
    simpl.                 (* [ ] =~ EmptyStr *)
    apply MEmpty.
  -                        (* x : T
                              s1 : list T
                              IHs1 : forall s2 : list T,
                                      s1 = s2 -> s1 =~ reg_exp_of_list s2
                              ============================
                              forall s2 : list T,
                               x :: s1 = s2 -> x :: s1 =~ reg_exp_of_list s2 *)
    intros s2 H.           (* s2 : list T
                              H : x :: s1 = s2
                              ============================
                              x :: s1 =~ reg_exp_of_list s2 *)
    rewrite conc_unitaria. (* [x] ++ s1 =~ reg_exp_of_list s2 *)
    rewrite <- H.           (* [x] ++ s1 =~ reg_exp_of_list (x :: s1) *)
    simpl.
    apply (MApp [x] (Char x)
                s1 (reg_exp_of_list s1)).

    *                      (* [x] =~ Char x *)
      apply MChar.
    *                      (* s1 =~ reg_exp_of_list s1 *)
      apply IHs1.          (* s1 = s1 *)
      reflexivity.
Qed.

Lemma reg_exp_of_list_spec :
  forall T (s1 s2 : list T),
    s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - apply reg_exp_of_list_spec_L1.
  - apply reg_exp_of_list_spec_L2.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.3. Definir la función
      re_chars {T : Type} (re : reg_exp) : list T
   tal que (re_chars e) es la lista de los caracteres en la expresión
   regurlar e.
   ------------------------------------------------------------------ *)

Fixpoint re_chars {T : Type} (e : reg_exp) : list T :=
  match e with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App e1 e2 => re_chars e1 ++ re_chars e2
  | Union e1 e2 => re_chars e1 ++ re_chars e2
  | Star re => re_chars re
  end.

(* ---------------------------------------------------------------------
   Ejemplo 4.1.4. Demostrar que si una cadena s coincide con una expresión
   regular e, entonces todos los elementos de s son caracteres de e; es
   decir,
      forall (T : Type) (s : list T) (re : reg_exp) (x : T),
        s =~ re ->
        En x s ->
        En x (re_chars re).
   ------------------------------------------------------------------ *)

Theorem in_re_match :
  forall (T : Type) (s : list T) (re : reg_exp) (x : T),
    s =~ re ->
    En x s ->
    En x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  -
    apply Hin.
  -
    apply Hin.
  -
    simpl.
    rewrite En_conc in *.
    destruct Hin as [Hin | Hin].
    +
      left.
      apply (IH1 Hin).
    +
      right.
      apply (IH2 Hin).
  -
    simpl.
    rewrite En_conc.
    left.
    apply (IH Hin).
  -
    simpl.
    rewrite En_conc.
    right.
    apply (IH Hin).
  -
    destruct Hin.
  -
    simpl.
    rewrite En_conc in Hin.
    destruct Hin as [Hin | Hin].
    +
      apply (IH1 Hin).
    +
      apply (IH2 Hin).
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.1.3.1. Definir, por recursión, la función
      re_not_empty {T : Type} (e : @reg_exp T) : bool
   tal que (re_not_empty e) se verifica si existe una cadena s que
   coincide con e.
   ------------------------------------------------------------------ *)

Fixpoint re_not_empty {T : Type} (e : @reg_exp T) : bool :=
  match e with
  | EmptySet    => false
  | EmptyStr    => true
  | Char _      => true
  | App e1 e2   => (re_not_empty e1) && (re_not_empty e2)
  | Union e1 e2 => (re_not_empty e1) || (re_not_empty e2)
  | Star _      => true
end.

(* ---------------------------------------------------------------------
   Ejercicio 4.1.4.2. Demostrar que
      forall T (re : @reg_exp T),
        (exists s, s =~ re) <-> re_not_empty re = true.
   ------------------------------------------------------------------ *)

Lemma re_not_empty_correct :
  forall T (re : @reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H.
    induction re as [|
                     | c
                     | re1 IH1 re2 IH2
                     | re1 IH1 re2 IH2
                     | s IH].
    +
      inversion H.
      inversion H0.
    +
      reflexivity.
    +
      reflexivity.
    +
      simpl.
      apply conj_verdad_syss.
      destruct H as [s0 eq].
      inversion eq.
      split.
      *
        apply IH1.
        exists s1.
        apply H2.
      *
        apply IH2.
        exists s2.
        apply H3.
    +
      simpl.
      apply disy_verdad_syss.
      destruct H as [s0 eq].
      inversion eq.
      *
        left.
        apply IH1.
        exists s0.
        apply H1.
      *
        right.
        apply IH2.
        exists s0.
        apply H1.
    +
      reflexivity.
  -
    intros H.
    induction re as [
                    |
                    | c
                    | re1 IH1 re2 IH2
                    | re1 IH1 re2 IH2
                    | s IH].
    +
      inversion H.
    +
      exists [].
      apply MEmpty.

    +
      exists [c].
      apply MChar.
    +
      simpl in H.
      apply conj_verdad_syss in H.
      destruct H as [ne1 ne2].
      apply IH1 in ne1.
      apply IH2 in ne2.
      destruct ne1 as [s1 eq1].
      destruct ne2 as [s2 eq2].
      exists (s1 ++ s2). apply MApp.
      *
        apply eq1.
      *
        apply eq2.
    +
      simpl in H.
      apply disy_verdad_syss in H.
      destruct H as [H|H].
      *
        apply IH1 in H.
        destruct H as [s eq].
        exists s.
        apply MUnionL. apply eq.
      *
        apply IH2 in H.
        destruct H as [s eq].
        exists s.
        apply MUnionR. apply eq.
    +
      exists [].
      apply MStar0.
Qed.

(* =====================================================================
   §§ 4.2. La táctica remember
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 4.2.1. Demostrar que
      forall T (s1 s2 : list T) (re : @reg_exp T),
        s1 =~ Star re ->
        s2 =~ Star re ->
        s1 ++ s2 =~ Star re.
   ------------------------------------------------------------------ *)

(* 1ª intento *)
Lemma star_app:
  forall T (s1 s2 : list T) (re : @reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  inversion H1.
  -
    simpl.
    intros H3.
    apply H3.
  -
    subst.
    intros H4.
    rewrite <- conc_asociativa.
    apply (MStarApp s0 (s3 ++ s2) re).
    +
      apply H0.
    +
      apply (MStarApp s3 s2 re).
Abort.


(* 2ª intento *)
Lemma star_app:
  forall T (s1 s2 : list T) (re : @reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [
       | x'
       | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH
       | re1 s2' re2 Hmatch IH
       | re''
       | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  -
    simpl.
    intros H.
    apply H.
  -
    (* s2 =~ Char x' -> [x'] ++ s2 =~ Char x' *)
Abort.

(* ---------------------------------------------------------------------
   Notas.
   1- El problema está en que la indución sobre hipótesis sólo funciona
      bien si todos sus argumentos son variables.
   2. En este caso, uno esta una expresión compuesta (Star re).
   3. Se puede intentar generalizar sobre los argumentos compuestos.
   4.
   ------------------------------------------------------------------ *)

(* 3ª intento *)
Lemma star_app:
  forall T (s1 s2 : list T) (re re' : reg_exp),
    re' = Star re ->
    s1 =~ re' ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Abort.

(* ---------------------------------------------------------------------
   Nota. La táctica (remember e as x) añade al contexto la ecuación
   (x = e) y sustituye todas las ocurrencias de la expresión e por la
   variable x.
   ------------------------------------------------------------------ *)

(* 4º intento *)
Lemma star_app:
  forall T (s1 s2 : list T) (re : reg_exp),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [
       | x'
       | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH
       | re1 s2' re2 Hmatch IH
       | re''
       | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
    intros s H.
    apply H.
  -
    inversion Heqre'.
    rewrite H0 in IH2, Hmatch1.
    intros s2 H1.
    rewrite <- conc_asociativa.
    apply MStarApp.
    +
      apply Hmatch1.
    +
      apply IH2.
      *
        reflexivity.
      *
        apply H1.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.2.1. Demostrar que
      forall T (s : list T) (re : reg_exp),
        s =~ Star re ->
        exists ss : list (list T),
          s = fold conc ss []
          /\ forall s', En s' ss -> s' =~ re.
   ------------------------------------------------------------------ *)

Lemma MStar'' :
  forall T (s : list T) (re : reg_exp),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold conc ss []
      /\ forall s', En s' ss -> s' =~ re.
Proof.
  intros T s re H1.
  remember (Star re) as re'.
  induction H1
    as [
       | x'
       | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH
       | re1 s2' re2 Hmatch IH
       | re''
       | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
  -
    inversion Heqre'.
    exists [].
    simpl.
    split.
    +
      reflexivity.
    +
      intros s' H.
      exfalso.
      apply H.
  -
    inversion Heqre'.
    apply IH2 in Heqre'.
    destruct Heqre' as [ss0 [eq1 eq2]].
    exists (s1 :: ss0).
    simpl.
    split.
    +
      rewrite <- eq1.
      reflexivity.
    +
      intros s'.
      intros [H|H].
      *
        rewrite <- H.
        rewrite <- H0.
        apply Hmatch1.
      *
        apply eq2.
        apply H.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.3. En este ejercicio se formaliza el lema del bombeo para
   lenguajes regulares http://bit.ly/2o6Pb1D que, informalmente, dice
   que cualquier palabra suficientemente larga en un lenguaje regular
   puede ser bombeada - eso es, repetir una sección en la mitad de la
   palabra un número arbitrario de veces - para producir una nueva
   palabra que también pertenece al mismo lenguaje.

   Más formalmente, sea L un lenguaje regular. Entonces existe un entero
   p ≥ 1 (al que llamaremos "longitud de bombeo" y que dependerá
   exclusivamente de L) tal que cualquier cadena w perteneciente a L, de
   longitud mayor o igual que p, puede escribirse como w = xyz
   (p. ej. dividiendo w en tres subcadenas), de forma que se satisfacen
   las siguientes condiciones: 1. |y| ≥ 1 2. |xy| ≤ p 3.  ∀ i / i ≥ 0,
   xy^iz ∈ L

   y es la subcadena que puede ser bombeada (borrada o repetida un
   número i de veces como se indica en (3), y la cadena resultante
   seguirá perteneciendo a L. (1) significa que la cadena y que se
   bombea debe tener como mínimo longitud uno. (2) significa que y debe
   estar dentro de los p primeros caracteres. No hay restricciones
   acerca de x o z.
   ------------------------------------------------------------------ *)

Module Pumping.

(* ---------------------------------------------------------------------
   Ejercicio 4.3.1. Definir la función
      pumping_constant {T} (re : @reg_exp T) : nat
   tal que (pumping_constant re) es el menor longitud de las cadenas
   bombables respecto de re.
   ------------------------------------------------------------------ *)

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet      => 0
  | EmptyStr      => 1
  | Char _        => 2
  | App re1 re2   =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _        => 1
  end.

(* ---------------------------------------------------------------------
   Ejercicio 4.3.2. Definir la función
      napp {T} (n : nat) (l : list T) : list T
   tal que (napp n xs) es la cadena obtenida repitiendo n veces la
   cadena xs. Por ejemplo,
      napp 3 [1;2] = [1; 2; 1; 2; 1; 2]
   ------------------------------------------------------------------ *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0    => []
  | S n' => l ++ napp n' l
  end.

Compute (napp 3 [1;2]).
(* = [1; 2; 1; 2; 1; 2] *)

(* ---------------------------------------------------------------------
   Ejercicio 4.3.3. Demostrar que
      forall T (n m : nat) (l : list T),
        napp (n + m) l = napp n l ++ napp m l.
   ------------------------------------------------------------------ *)

Lemma napp_plus:
  forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  -
    reflexivity.
  -
    simpl.
    rewrite IHn, conc_asociativa.
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.3.4. Demostrar el lema del bombeo:
      forall T (re : @reg_exp T) s,
        s =~ re ->
        pumping_constant re <= longitud s ->
        exists s1 s2 s3,
          s = s1 ++ s2 ++ s3 /\
          s2 <> [] /\
          forall m, s1 ++ napp m s2 ++ s3 =~ re.
   ------------------------------------------------------------------ *)

Import Coq.omega.Omega.

Lemma orb_lt_or_iff :
  forall a b c d,
    a <= b \/ c <= d <->
    menor_o_igual a b || menor_o_igual c d = true.
Proof.
  split.
  -
    intros [H | H].
    +
      apply menor_o_igual_syss in H.
      rewrite H.
      simpl.
      reflexivity.
    +
      apply menor_o_igual_syss in H.
      rewrite H.
      destruct (menor_o_igual a b).
      *
        reflexivity.
      *
        reflexivity.
  -
    intros.
    destruct (menor_o_igual a b) eqn:H1.
    +
      left.
      apply menor_o_igual_syss.
      apply H1.
    +
      simpl in H.
      right.
      apply menor_o_igual_syss.
      apply H.
Qed.

Lemma plus_le_plus :
  forall a b c d,
    a + b <= c + d -> a <= c \/ b <= d.
Proof.
  intros.
  omega.
Qed.

Lemma napp_star_star :
  forall T (l : list T) re m,
    l =~ Star re -> napp m l =~ Star re.
Proof.
  intros T l re.
  induction m as [|m'].
  -
    simpl.
    intros H.
    apply MStar0.
  -
    simpl.
    intros H.
    apply star_app.
    +
      apply H.
    +
      apply IHm'.
      apply H.
Qed.

Lemma napp_star :
  forall T (l : list T) re m,
    l =~ re -> napp m l =~ Star re.
Proof.
  intros T l re m H.
  apply napp_star_star.
  replace l with (l ++ []).
  apply MStarApp.
  apply H.
  apply MStar0.
  apply conc_nil.
Qed.

Lemma pumping :
  forall T (re : @reg_exp T) s,
    s =~ re ->
    pumping_constant re <= longitud s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [
       | x
       | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH
       | re1 s2 re2 Hmatch IH
       | re
       | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  -
    simpl.
    omega.
  -
    simpl.
    omega.
  -
    simpl.
    intros.
    rewrite conc_longitud in H.
    apply plus_le_plus in H.
    induction H.
    +
      apply IH1 in H.
      destruct H, H, H.
      exists x, x0, (x1++s2).
      split.
      *
        destruct H.
        rewrite H.
        rewrite <- conc_asociativa.
        rewrite <- conc_asociativa.
        reflexivity.
      *
        destruct H.
        destruct H0.
        split.
        --
          assumption.
        --
          intros.
          rewrite 2 conc_asociativa.
          apply MApp.
          rewrite <- conc_asociativa.
          apply H1.
          assumption.
    +
      apply IH2 in H.
      destruct H, H, H, H.
      exists (s1++x), x0, x1.
      split.
      *
        rewrite <- conc_asociativa.
        rewrite H.
        reflexivity.
      *
        destruct H0.
        split.
        assumption.
        intros.
        rewrite <- conc_asociativa.
        apply MApp.
        assumption.
        apply H1.
  - simpl.
    intros.
    apply (le_trans (pumping_constant re1)) in H.
    apply IH in H.
    destruct H, H, H, H.
    exists x, x0, x1.
    split.
    +
      assumption.
    +
      destruct H0.
      split.
      *
        assumption.
      *
        intros.
        apply MUnionL.
        apply H1.
    +
      apply le_plus_l.
  -
    simpl.
    intros.
    rewrite suma_conmutativa in H.
    rewrite <- le_plus_l in H.
    apply IH in H.
    destruct H, H, H, H.
    exists x, x0, x1.
    split.
    +
      assumption.
    +
      destruct H0.
      split.
      *
        assumption.
      *
        intros.
        apply MUnionR.
        apply H1.
  -
    simpl.
    intros.
    inversion H.
  -
    destruct s1 eqn:Hs1.
    +
      simpl in *.
      intros.
      apply IH2.
      assumption.
    +
      simpl in *.
      intros.
      exists [], s1, s2.
      split.
      --
        rewrite Hs1.
        reflexivity.
      --
        split.
        ++
          intros contra.
          rewrite contra in Hs1.
          inversion Hs1.
        ++
          intros.
          simpl.
          apply star_app.
      *
        apply napp_star.
        rewrite Hs1.
        assumption.
      *
        assumption.
Qed.

End Pumping.

(* =====================================================================
   § 5. Caso de estudio: Mejora de la reflexión
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.1. Demostrar que
      forall (n : nat) (xs : list nat),
        filtra (iguales_nat n) xs <> [] ->
        En n xs.
   ------------------------------------------------------------------ *)

Theorem filter_not_empty_In :
  forall (n : nat) (xs : list nat),
    filtra (iguales_nat n) xs <> [] ->
    En n xs.
Proof.
  intros n xs.
  induction xs as [|x xs' IHxs'].
  -
    simpl.
    intros H.
    apply H.
    reflexivity.
  -
    simpl.
    destruct (iguales_nat n x) eqn:H.
    +
      intros _.
      rewrite iguales_nat_bool_prop in H.
      rewrite H.
      left.
      reflexivity.
    +
      intros H'.
      right.
      apply IHxs'.
      apply H'.
Qed.

(* ---------------------------------------------------------------------
   Nota. Se simplifica la demostración en filter_not_empty_In'.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 5.2. Definir inductivamente la propiedad
      reflect (P : Prop) : bool -> Prop
   que expresa que la propiedad P se refleja en el booleano b; es decir,
   (reflect P b) se verifica syss (P <-> b = true).
   ------------------------------------------------------------------ *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

(* ---------------------------------------------------------------------
   Ejemplo 5.3. Demostrar que
      forall (P : Prop) (b : bool),
        (P <-> b = true) -> reflect P b.
   ------------------------------------------------------------------ *)

Theorem iff_reflect :
  forall (P : Prop) (b : bool),
    (P <-> b = true) -> reflect P b.
Proof.
  intros P b H.
  destruct b.
  -
    apply ReflectT.
    rewrite H.
    reflexivity.
  -
    apply ReflectF.
    rewrite H.
    intros H'.
    inversion H'.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.1. Demostrar que
      forall (P : Prop) (b : bool),
        reflect P b -> (P <-> b = true).
   ------------------------------------------------------------------ *)

Theorem reflect_iff :
  forall (P : Prop) (b : bool),
    reflect P b -> (P <-> b = true).
Proof.
  intros.
  inversion H.
  -
    split.
    +
      intros.
      reflexivity.
    +
      intros _.
      assumption.
  -
    split.
    +
      intros.
      apply H0 in H2.
      inversion H2.
    +
      intros.
      inversion H2.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.4. Demostrar que
      forall n m : nat,
        reflect (n = m) (iguales_nat n m).
   ------------------------------------------------------------------ *)

Lemma iguales_natP :
  forall n m : nat,
    reflect (n = m) (iguales_nat n m).
Proof.
  intros n m.
  apply iff_reflect.
  rewrite iguales_nat_bool_prop.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.5. Demostrar que
      forall (n : nat) (xs : list nat),
        filtra (iguales_nat n) xs <> [] ->
        En n xs.
   ------------------------------------------------------------------ *)

Theorem filter_not_empty_In' :
  forall (n : nat) (xs : list nat),
    filtra (iguales_nat n) xs <> [] ->
    En n xs.
Proof.
  intros n xs.
  induction xs as [|x xs' HI].
  -
    simpl.
    intros H.
    apply H.
    reflexivity.
  -
    simpl.
    destruct (iguales_natP n x) as [H | H].
    +
      intros _.
      rewrite H.
      left.
      reflexivity.
    +
      intros H'.
      right.
      apply HI.
      apply H'.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.2. Se considera la función
      count : nat -> list nat -> nat
   definida por
      Fixpoint count (n : nat) (xs : list nat) : nat :=
        match xs with
        | [] => 0
        | x :: xs' => (if iguales_nat n x then 1 else 0) + count n xs'
        end.

   Demostrar que
      forall (n : nat) (xs : list nat),
        count n xs = 0 -> ~(En n xs).
   ------------------------------------------------------------------ *)

Fixpoint count (n : nat) (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => (if iguales_nat n x then 1 else 0) + count n xs'
  end.

Theorem iguales_natP_practice :
  forall (n : nat) (xs : list nat),
    count n xs = 0 -> ~(En n xs).
Proof.
  induction xs as [|x xs' HI].
  -
    simpl.
    intros _.
    intros H.
    assumption.
  -
    simpl.
    destruct (iguales_natP n x) as [H | H].
    +
      intros H1.
      inversion H1.
    +
      simpl.
      intros H1 [H2 | H2].
      *
        apply H.
        symmetry.
        apply H2.
      *
        apply HI in H1.
        apply H1.
        apply H2.
Qed.

(* =====================================================================
   § 6. Ejercicios adicionales.
   ================================================================== *)


(* ---------------------------------------------------------------------
   Ejercicio 6.1.1. Definir inductivamente la propiedad
      noTartamudea {X:Type} : list X -> Prop
   tal que (noTartamudea xs) expresa que xs es una lista sin elementos
   consecutivos iguales.
   ------------------------------------------------------------------ *)

Inductive noTartamudea {X:Type} : list X -> Prop :=
  | nt_vacia    : noTartamudea []
  | nt_unitaria : forall x, noTartamudea [x]
  | nt_general  : forall x y xs, x <> y ->
                            noTartamudea (y::xs) ->
                            noTartamudea (x::y::xs).

(* ---------------------------------------------------------------------
   Ejercicio 6.1.2. Demostrar que
      noTartamudea [3;1;4;1;5;6].
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Example prop_noTartamudea_1: noTartamudea [3;1;4;1;5;6].
Proof.
  apply nt_general.
  -
    apply iguales_nat_falso_syss.
    auto.
  -
    apply nt_general.
    +
      apply iguales_nat_falso_syss.
      auto.
    +
      apply nt_general.
      *
        apply iguales_nat_falso_syss.
        auto.
      *
        apply nt_general.
        --
          apply iguales_nat_falso_syss.
          auto.
        --
          apply nt_general.
          ++
            apply iguales_nat_falso_syss.
            auto.
          ++
            apply nt_unitaria.
Qed.

(* 2ª demostración *)
Example prop_noTartamudea_1a: noTartamudea [3;1;4;1;5;6].
Proof.
  repeat constructor; apply iguales_nat_falso_syss; auto.
Qed.

(* ---------------------------------------------------------------------
   Nota. Uso de repetición de repeticiones (con repeat) y concatenación
   (con ;) de tácticas.
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio 6.1.3. Demostrar que
      noTartamudea (@nil nat).
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Example prop_noTartamudea_2a:
  noTartamudea (@nil nat).
Proof.
  apply nt_vacia.
Qed.

(* 2ª demostración *)
Example prop_noTartamudea_2:
  noTartamudea (@nil nat).
Proof.
  repeat constructor; apply iguales_nat_falso_syss; auto.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6.1.4. Demostrar que
      noTartamudea [5].
   ------------------------------------------------------------------ *)

Example prop_noTartamudea_3a:
  noTartamudea [5].
Proof.
  apply nt_unitaria.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6.1.5. Demostrar que
      not (noTartamudea [3;1;1;4]).
   ------------------------------------------------------------------ *)

(* 1ª demostración *)
Example prop_noTartamudea_4a:
  not (noTartamudea [3;1;1;4]).
Proof.
  intro.
  inversion H.
  subst.
  clear H H2.
  inversion H4.
  subst.
  apply H1.
  reflexivity.
Qed.

(* 2ª demostración *)
Example prop_noTartamudea_4:
  not (noTartamudea [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
           h: noTartamudea _ |- _ => inversion h; clear h; subst
         end.
  apply H1 ; reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6.2.1. Definir inductivamente la relación
      in_merge {X : Type} : list X -> list X -> list X
   tal que (in_merge xs ys zs) expresa que zs es la lista obtenida
   intercalando los elementos de xs e ys. Por ejemplo,
      in_merge [1;6;2] [4;3] [1;4;6;2;3]
   ------------------------------------------------------------------ *)

Inductive in_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | merge_vacioI  : forall xs, in_merge [] xs xs
  | merge_vacioD  : forall xs, in_merge xs [] xs
  | merge_general : forall x xs y ys zs, in_merge xs ys zs ->
                                    in_merge (x::xs) (y::ys) (x::y::zs).

(* ---------------------------------------------------------------------
   Ejercicio 6.2.2. Demostrar que
      forall (X : Type) (xs ys zs : list X) (p : X -> bool),
        in_merge xs ys zs ->
        Todos (fun x => p x = true) xs ->
        Todos (fun x => p x = false) ys ->
        filtra p zs = xs.
   ------------------------------------------------------------------ *)

Lemma filter_nothing :
  forall (X : Type) (p: X -> bool) (xs: list X),
    Todos (fun x => p x = false) xs ->
    filtra p xs = [].
Proof.
  intros X p.
  induction xs as [|x xs' HI].
  -
    reflexivity.
  -
    simpl.
    intros [H1 H2].
    rewrite H1.
    apply HI.
    apply H2.
Qed.

Lemma filter_everything :
  forall (X : Type) (p : X -> bool) (xs : list X),
    Todos (fun x => p x = true) xs ->
    filtra p xs = xs.
Proof.
  intros X p.
  induction xs as [|s xs' HI].
  -
    reflexivity.
  -
    simpl.
    intros [H1 H2].
    rewrite H1.
    rewrite HI.
    +
      reflexivity.
    +
      apply H2.
Qed.

Theorem filter_spec :
  forall (X : Type) (xs ys zs : list X) (p : X -> bool),
  in_merge xs ys zs ->
  Todos (fun x => p x = true) xs ->
  Todos (fun x => p x = false) ys ->
  filtra p zs = xs.
Proof.
  intros X xs ys zs p H Hxs Hys.
  induction H as [ xs'
                 | xs'
                 | x xs' y ys' zs' HI].
  -
    apply filter_nothing.
    apply Hys.
  -
    apply filter_everything.
    apply Hxs.
  -
    assert (Hx : p x = true).
    +
      apply Hxs.
    +
      simpl.
      rewrite Hx.
      apply f_equal.
      *
        assert (Hy : p y = false).
        --
          apply Hys.
        --
          rewrite Hy.
          apply IHHI.
          ++
            apply Hxs.
          ++
            apply Hys.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6.3.1. Definir inductivamente la propiedad
      pal {X : Type} : list X -> Prop
   tal que (pal xs) expresa que xs es un palíndromo.
   ------------------------------------------------------------------ *)

Inductive pal {X : Type} : list X -> Prop :=
  | pal_vacio   : pal []
  | pal_unit    : forall x, pal [x]
  | pal_general : forall x xs, pal xs -> pal (x::xs++[x]).

(* ---------------------------------------------------------------------
   Ejercicio 6.3.2. Demostrar que
      pal [3;3].
   ------------------------------------------------------------------ *)

Lemma pa_ej1 : pal [3;3].
Proof.
  assert ([3;3] = (3::[]++[3])).
  -
    simpl.
    reflexivity.
  -
    rewrite H.
    apply pal_general.
    apply pal_vacio.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6.3.3. Demostrar que
      pal [3;5;3].
   ------------------------------------------------------------------ *)

Lemma pa_ej2 : pal [3;5;3].
Proof.
  assert ([3;5;3] = (3::[5]++[3])).
  -
    simpl.
    reflexivity.
  -
    rewrite H.
    apply pal_general.
    apply pal_unit.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.6.4. Demostrar que
      forall (X : Type) (xs : list X),
        pal (xs ++ inversa xs).
   ------------------------------------------------------------------ *)

Lemma pal_app_rev : forall (X : Type) (xs : list X),
    pal (xs ++ inversa xs).
Proof.
  intros X xs.
  induction xs as [| x xs' HI].
  -
    simpl.
    apply pal_vacio.
  -
    simpl.
    assert (x :: xs' ++ inversa xs' ++ [x] =
            x :: (xs' ++ inversa xs') ++ [x]).
    +
      rewrite conc_asociativa.
      reflexivity.
    +
      rewrite H.
      apply pal_general.
      apply HI.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.6.5. Demostrar que
      forall (X : Type) (xs : list X),
         pal xs -> xs = inversa xs.
   ------------------------------------------------------------------ *)

Lemma pal_rev : forall (X : Type) (xs : list X),
    pal xs -> xs = inversa xs.
Proof.
  intros X xs H.
  induction H as [ | x | x xs _ HI].
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite inversa_conc.
    simpl.
    rewrite <- HI.
    reflexivity.
Qed.

Lemma palindrome_converse_aux1 : forall (X:Type) (l l': list X) (a b: X),
    a :: l = l' ++ b :: nil -> (a = b /\ l = nil) \/ exists k, l = k ++ b :: nil.

Lemma tool2 : forall (X:Type) (l1 l2 : list X) (a b: X),
     l1 ++ a :: nil = l2 ++ b :: nil -> a = b /\ l1 = l2.

Lemma palindrome_converse_aux: forall (X: Type) (n: nat) (xs: list X),
    longitud xs <= n -> xs = inversa xs -> pal xs.
Proof.
  induction n as [|n' HI].
  -
    intros xs H H0.
    assert (xs = []).
    +
      destruct xs as [|y ys].
      *
        reflexivity.
      *
        simpl in H.
        inversion H.
    +
      rewrite H1.
      apply pal_vacio.
  -
    intros xs H H0.
    destruct xs as [|y ys].
    +
      apply pal_vacio.
    +





Lemma palindrome_converse : forall (X : Type) (xs : list X),
    xs = inversa xs -> pal xs.
Proof.
  intros X xs H.
  induction xs as [|x xs' HI].
  -
    apply pal_vacio.
  -
    destruct xs' as [|y ys].
    +
      apply pal_unit.
    +



(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  En x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (En x
    l) \/ ~ (En x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, En x l1 -> En x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represeneted
    as lists of ASCII characters: *)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)


(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. inversion H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, optional (app_ne)  *)
(** [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, optional (star_ne)  *)
(** [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, optional (match_eps)  *)
(** Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (match_eps_refl)  *)
(** Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)


(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, optional (derive)  *)
(** Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example prop_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example prop_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example prop_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example prop_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example prop_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example prop_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example prop_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example prop_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, optional (derive_corr)  *)
(** Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)


(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, optional (regex_match)  *)
(** Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (regex_refl)  *)
(** Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* =====================================================================
   § Bibliografía
   =====================================================================

+ "Inductively defined propositions" de Peirce et als.
  http://bit.ly/2Lejw7s *)
