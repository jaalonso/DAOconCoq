(* T3: Datos estructurados en Coq *)

Require Export T2_Induccion.

(* El contenido de la teoría es
   1. Pares de números 
   2. Listas de números 
      1. El tipo de la lista de números. 
      2. La función repite (repeat)  
      3. La función longitud (length)  
      4. La función conc (app)  
      5. Las funciones primero (hd) y resto (tl)
      6. Ejercicios sobre listas de números 
      7. Multiconjuntos como listas 
   3. Razonamiento sobre listas
      1. Demostraciones por simplificación 
      2. Demostraciones por casos 
      3. Demostraciones por inducción
      4. Ejercicios 
   4. Opcionales
   5. Diccionarios (o funciones parciales)
   6. Bibliografía
*)

(* =====================================================================
   § 1. Pares de números 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Nota. Se inicia el módulo ListaNat.
   ------------------------------------------------------------------ *)

Module ListaNat. 

(* ---------------------------------------------------------------------
   Ejemplo 1.1. Definir el tipo ProdNat para los pares de números
   naturales con el constructor
      par : nat -> nat -> ProdNat.
   ------------------------------------------------------------------ *)

Inductive ProdNat : Type :=
  par : nat -> nat -> ProdNat.

(* ---------------------------------------------------------------------
   Ejemplo 1.2. Calcular el tipo de la expresión (par 3 5)
   ------------------------------------------------------------------ *)

Check (par 3 5).
(* ===> par 3 5 : ProdNat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.3. Definir la función
      fst : ProdNat -> nat
   tal que (fst p) es la primera componente de p.
   ------------------------------------------------------------------ *)

Definition fst (p : ProdNat) : nat := 
  match p with
  | par x y => x
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.4. Evaluar la expresión 
      fst (par 3 5)
   ------------------------------------------------------------------ *)

Compute (fst (par 3 5)).
(* ===> 3 : nat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.5. Definir la función
      snd : ProdNat -> nat
   tal que (snd p) es la segunda componente de p.
   ------------------------------------------------------------------ *)

Definition snd (p : ProdNat) : nat := 
  match p with
  | par x y => y
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.6. Definir la notación (x,y) como una abreviaura de 
   (par x y).
   ------------------------------------------------------------------ *)

Notation "( x , y )" := (par x y).

(* ---------------------------------------------------------------------
   Ejemplo 1.7. Evaluar la expresión 
      fst (3,5)
   ------------------------------------------------------------------ *)

Compute (fst (3,5)).
(* ===> 3 : nat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.8. Redefinir la función fst usando la abreviatura de pares.
   ------------------------------------------------------------------ *)

Definition fst' (p : ProdNat) : nat := 
  match p with
  | (x,y) => x
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.9. Redefinir la función snd usando la abreviatura de pares.
   ------------------------------------------------------------------ *)

Definition snd' (p : ProdNat) : nat := 
  match p with
  | (x,y) => y
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.10. Definir la función
      intercambia : ProdNat -> ProdNat
   tal que (intercambia p) es el par obtenido intercambiando las
   componentes de p.
   ------------------------------------------------------------------ *)

Definition intercambia (p : ProdNat) : ProdNat := 
  match p with
  | (x,y) => (y,x)
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.11. Demostrar que para todos los naturales
      (n,m) = (fst (n,m), snd (n,m)).
   ------------------------------------------------------------------ *)

Theorem par_componentes1 : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.12. Demostrar que para todo par de naturales
      p = (fst p, snd p).
   ------------------------------------------------------------------ *)

(* 1º intento *)
Theorem par_componentes2 : forall (p : ProdNat),
  p = (fst p, snd p).
Proof.
  simpl. (* 
            ============================
            forall p : ProdNat, p = (fst p, snd p) *)
Abort.

(* 2º intento *)
Theorem par_componentes : forall (p : ProdNat),
  p = (fst p, snd p).
Proof.
  intros p.            (* p : ProdNat
                          ============================
                          p = (fst p, snd p) *)
  destruct p as [n m]. (* n, m : nat
                          ============================
                          (n, m) = (fst (n, m), snd (n, m)) *)
  simpl.               (* (n, m) = (n, m) *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1. Demostrar que para todo par de naturales p,
      (snd p, fst p) = intercambia p.
   ------------------------------------------------------------------ *)

Theorem ejercicio_1_1: forall p : ProdNat,
  (snd p, fst p) = intercambia p.
Proof.
  intro p.             (* p : ProdNat
                          ============================
                          (snd p, fst p) = intercambia p *)
  destruct p as [n m]. (* n, m : nat
                          ============================
                          (snd (n, m), fst (n, m)) = intercambia (n, m) *)
  simpl.               (* (m, n) = (m, n) *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.2. Demostrar que para todo par de naturales p,
      fst (intercambia p) = snd p.
   ------------------------------------------------------------------ *)

Theorem ejercicio_1_2: forall p : ProdNat,
  fst (intercambia p) = snd p.
Proof.
  intro p.             (* p : ProdNat
                          ============================
                          fst (intercambia p) = snd p *)
  destruct p as [n m]. (* n, m : nat
                          ============================
                          fst (intercambia (n, m)) = snd (n, m) *)
  simpl.               (* m = m *)
  reflexivity.
Qed.

(* =====================================================================
   § 2. Listas de números 
   ================================================================== *)

(* =====================================================================
   §§ 2.1. El tipo de la lista de números. 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.1. Definir el tipo ListaNat de la lista de los números
   naturales y cuyo constructores son 
   + nil (la lista vacía) y 
   + cons (tal que (cons x ys) es la lista obtenida añadiéndole x a ys. 
   ------------------------------------------------------------------ *)

Inductive ListaNat : Type :=
  | nil  : ListaNat
  | cons : nat -> ListaNat -> ListaNat.

(* ---------------------------------------------------------------------
   Ejemplo 2.1.2. Definir la constante 
      ejLista : ListaNat
   que es la lista cuyos elementos son 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition ejLista := cons 1 (cons 2 (cons 3 nil)).

(* ---------------------------------------------------------------------
   Ejemplo 2.1.3. Definir la notación (x :: ys) como una abreviatura de 
   (cons x ys).
   ------------------------------------------------------------------ *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

(* ---------------------------------------------------------------------
   Ejemplo 2.1.4. Definir la notación de las listas finitas escribiendo
   sus elementos entre corchetes y separados por puntos y comas.
   ------------------------------------------------------------------ *)

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* ---------------------------------------------------------------------
   Ejemplo 2.1.5. Definir la lista cuyos elementos son 1, 2 y 3 mediante
   sistintas represerntaciones.
   ------------------------------------------------------------------ *)

Definition ejLista1 := 1 :: (2 :: (3 :: nil)).
Definition ejLista2 := 1 :: 2 :: 3 :: nil.
Definition ejLista3 := [1;2;3].

(* =====================================================================
   §§ 2.2. La función repite (repeat)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.1. Definir la función
      repite : nat -> nat -> ListaNat
   tal que (repite n k) es la lista formada por k veces el número n. Por
   ejemplo, 
      repite 5 3 = [5; 5; 5]

   Nota: La función repite es quivalente a la predefinida repeat.
   ------------------------------------------------------------------ *)

Fixpoint repite (n k : nat) : ListaNat :=
  match k with
  | O        => nil
  | S k' => n :: (repite n k')
  end.

Compute (repite 5 3).
(* ===> [5; 5; 5] : ListaNat*)

(* =====================================================================
   §§ 2.3. La función longitud (length)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.3.1. Definir la función
      longitud : ListaNat -> nat
   tal que (longitud xs) es el número de elementos de xs. Por ejemplo, 
      longitud [4;2;6] = 3

   Nota: La función longitud es equivalente a la predefinida length
   ------------------------------------------------------------------ *)

Fixpoint longitud (l:ListaNat) : nat :=
  match l with
  | nil    => O
  | h :: t => S (longitud t)
  end.

Compute (longitud [4;2;6]).
(* ===> 3 : nat *)

(* =====================================================================
   §§ 2.4. La función conc (app)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.4.1. Definir la función
      conc : ListaNat -> ListaNat -> ListaNat
   tal que (conc xs ys) es la concatenación de xs e ys. Por ejemplo, 
      conc [1;3] [4;2;3;5] =  [1; 3; 4; 2; 3; 5]

   Nota:La función conc es equivalente a la predefinida app.
   ------------------------------------------------------------------ *)

Fixpoint conc (xs ys : ListaNat) : ListaNat :=
  match xs with
  | nil    => ys
  | x :: zs => x :: (conc zs ys)
  end.

Compute (conc [1;3] [4;2;3;5]).
(* ===> [1; 3; 4; 2; 3; 5] : ListaNat *)

(* ---------------------------------------------------------------------
   Ejemplo 2.4.2. Definir la notación (xs ++ ys) como una abreviaura de 
   (conc xs ys).
   ------------------------------------------------------------------ *)

Notation "x ++ y" := (conc x y)
                     (right associativity, at level 60).

(* ---------------------------------------------------------------------
   Ejemplo 2.4.3. Demostrar que
      [1;2;3] ++ [4;5] = [1;2;3;4;5].
      nil     ++ [4;5] = [4;5].
      [1;2;3] ++ nil   = [1;2;3].
   ------------------------------------------------------------------ *)

Example test_conc1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.

Example test_conc2: nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.

Example test_conc3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.5. Las funciones primero (hd) y resto (tl)
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.5.1. Definir la función
      primero : nat -> ListaNat -> ListaNat
   tal que (primero d xs) es el primer elemento de xs o d, si xs es la lista
   vacía. Por ejemplo,
      primero 7 [3;2;5] = 3 
      primero 7 []      = 7 

   Nota. La función primero es equivalente a la predefinida hd
   ------------------------------------------------------------------ *)

Definition primero (d : nat) (xs : ListaNat) : nat :=
  match xs with
  | nil     => d
  | y :: ys => y
  end.

Compute (primero 7 [3;2;5]).
(* ===> 3 : nat *)
Compute (primero 7 []).
(* ===> 7 : nat *)

(* ---------------------------------------------------------------------
   Ejemplo 2.5.2. Demostrar que 
       primero 0 [1;2;3] = 1.
       resto [1;2;3]     = [2;3].
   ------------------------------------------------------------------ *)

Example prop_primero1: primero 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.

Example prop_primero2: primero 0 [] = 0.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.5.3. Definir la función
      resto : ListaNat -> ListaNat
   tal que (resto xs) es el resto de xs. Por ejemplo.
      resto [3;2;5] = [2; 5]
      resto []      = [ ]

   Nota. La función resto es equivalente la predefinida tl.
   ------------------------------------------------------------------ *)

Definition resto (xs:ListaNat) : ListaNat :=
  match xs with
  | nil     => nil
  | y :: ys => ys
  end.

Compute (resto [3;2;5]).
(* ===> [2; 5] : ListaNat *)
Compute (resto []).
(* ===> [ ] : ListaNat *)

(* ---------------------------------------------------------------------
   Ejemplo 2.5.4. Demostrar que 
       resto [1;2;3] = [2;3].
   ------------------------------------------------------------------ *)

Example prop_resto: resto [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.6. Ejercicios sobre listas de números 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 2.6.1. Definir la función
      noCeros : ListaNat -> ListaNat
   tal que (noCeros xs) es la lista de los elementos de xs distintos de
   cero. Por ejemplo,
      noCeros [0;1;0;2;3;0;0] = [1;2;3].
   ------------------------------------------------------------------ *)

Fixpoint noCeros (xs:ListaNat) : ListaNat :=
  match xs with
  | nil => nil
  | a::bs => match a with
            | 0 => noCeros bs 
            | _ =>  a :: noCeros bs
            end
 end.

Compute (noCeros [0;1;0;2;3;0;0]).
(* ===> [1; 2; 3] : ListaNat  *)

(* ---------------------------------------------------------------------
   Ejercicio 2.6.2. Definir la función
      impares : ListaNat -> ListaNat
   tal que (impares xs) es la lista de los elementos impares de
   xs. Por ejemplo,
      impares [0;1;0;2;3;0;0] = [1;3].
   ------------------------------------------------------------------ *)

Fixpoint impares (xs:ListaNat) : ListaNat :=
  match xs with
  | nil   => nil
  | y::ys => if esImpar y
             then y :: impares ys 
             else impares ys
  end.
 
Compute (impares [0;1;0;2;3;0;0]).
(* ===> [1; 3] : ListaNat *)

(* ---------------------------------------------------------------------
   Ejercicio 2.6.3. Definir la función
      nImpares : ListaNat -> nat
   tal que (nImpares xs) es el número de elementos impares de xs. Por 
   ejemplo,
      nImpares [1;0;3;1;4;5] = 4.
      nImpares [0;2;4]       = 0.
      nImpares nil           = 0.
   ------------------------------------------------------------------ *)

Definition nImpares (xs:ListaNat) : nat :=
  longitud (impares xs). 

Example prop_nImpares1: nImpares [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example prop_nImpares2: nImpares [0;2;4] = 0.
Proof. reflexivity. Qed.

Example prop_nImpares3: nImpares nil = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.6.4. Definir la función
      intercaladas : ListaNat -> ListaNat -> ListaNat
   tal que (intercaladas xs ys) es la lista obtenida intercalando los
   elementos de xs e ys. Por ejemplo,
      intercaladas [1;2;3] [4;5;6] = [1;4;2;5;3;6].
      intercaladas [1] [4;5;6]     = [1;4;5;6].
      intercaladas [1;2;3] [4]     = [1;4;2;3].
      intercaladas [] [20;30]      = [20;30].
   ------------------------------------------------------------------ *)

Fixpoint intercaladas (xs ys : ListaNat) : ListaNat :=
  match xs with
  | nil    => ys
  | x::xs' => match ys with
              | nil    => xs
              | y::ys' => x::y::intercaladas xs' ys'
              end
  end.

Example prop_intercaladas1: intercaladas [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example prop_intercaladas2: intercaladas [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example prop_intercaladas3: intercaladas [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example prop_intercaladas4: intercaladas [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.7. Multiconjuntos como listas 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.7.1. Un multiconjunto es una colección de elementos donde
   no importa el orden de los elementos, pero sí el número de
   ocurrencias de cada elemento.

   Definir el tipo multiconjunto de los multiconjuntos de números
   naturales. 
   ------------------------------------------------------------------ *)

Definition multiconjunto := ListaNat.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.2. Definir la función
      nOcurrencias : nat -> multiconjunto -> nat 
   tal que (nOcurrencias x ys) es el número de veces que aparece el
   elemento x en el multiconjunto ys. Por ejemplo,
      nOcurrencias 1 [1;2;3;1;4;1] = 3.
      nOcurrencias 6 [1;2;3;1;4;1] = 0.
   ------------------------------------------------------------------ *)

Fixpoint nOcurrencias (x:nat) (ys:multiconjunto) : nat :=
  match ys with
  | nil    => 0
  | y::ys' => if iguales_nat y x
              then 1 + nOcurrencias x ys'
              else nOcurrencias x ys'
  end.

Example prop_nOcurrencias1: nOcurrencias 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example prop_nOcurrencias2: nOcurrencias 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed. 

(* ---------------------------------------------------------------------
   Ejercicio 2.7.3. Definir la función
      suma : multiconjunto -> multiconjunto -> multiconjunto
   tal que (suma xs ys) es la suma de los multiconjuntos xs e ys. Por
   ejemplo, 
      suma [1;2;3] [1;4;1]                  = [1; 2; 3; 1; 4; 1]
      nOcurrencias 1 (suma [1;2;3] [1;4;1]) = 3.
   ------------------------------------------------------------------ *)

Definition suma : multiconjunto -> multiconjunto -> multiconjunto :=
  conc.

Example prop_sum: nOcurrencias 1 (suma [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.4. Definir la función
      agrega : nat -> multiconjunto -> multiconjunto 
   tal que (agrega x ys) es el multiconjunto obtenido añadiendo el
   elemento x al multiconjunto ys. Por ejemplo,
      nOcurrencias 1 (agrega 1 [1;4;1]) = 3.
      nOcurrencias 5 (agrega 1 [1;4;1]) = 0.
   ------------------------------------------------------------------ *)

Definition agrega (x:nat) (ys:multiconjunto) : multiconjunto :=
  x :: ys.

Example prop_agrega1: nOcurrencias 1 (agrega 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example prop_agrega2: nOcurrencias 5 (agrega 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.5. Definir la función
      pertenece : nat -> multiconjunto -> bool
   tal que (pertenece x ys) se verfica si x pertenece al multiconjunto
   ys. Por ejemplo,  
      pertenece 1 [1;4;1] = true.
      pertenece 2 [1;4;1] = false.
   ------------------------------------------------------------------ *)

Definition pertenece (x:nat) (ys:multiconjunto) : bool := 
  negacion (iguales_nat 0 (nOcurrencias x ys)).

Example prop_pertenece1: pertenece 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example prop_pertenece2: pertenece 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.6. Definir la función
      eliminaUna : nat -> multiconjunto -> multiconjunto
   tal que (eliminaUna x ys) es el multiconjunto obtenido eliminando una
   ocurrencia de x en el multiconjunto ys. Por ejemplo, 
      nOcurrencias 5 (eliminaUna 5 [2;1;5;4;1])     = 0.
      nOcurrencias 4 (eliminaUna 5 [2;1;4;5;1;4])   = 2.
      nOcurrencias 5 (eliminaUna 5 [2;1;5;4;5;1;4]) = 1.
   ------------------------------------------------------------------ *)

Fixpoint eliminaUna (x:nat) (ys:multiconjunto) : multiconjunto :=
  match ys with
  | nil      => nil
  | y :: ys' => if iguales_nat y x
               then ys'
               else y :: eliminaUna x ys'
  end.

Example prop_eliminaUna1: nOcurrencias 5 (eliminaUna 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example prop_eliminaUna2: nOcurrencias 5 (eliminaUna 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example prop_eliminaUna3: nOcurrencias 4 (eliminaUna 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example prop_eliminaUna4: nOcurrencias 5 (eliminaUna 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.7. Definir la función
      eliminaTodas : nat -> multiconjunto -> multiconjunto
   tal que (eliminaTodas x ys) es el multiconjunto obtenido eliminando
   todas las ocurrencias de x en el multiconjunto ys. Por ejemplo,
      nOcurrencias 5 (eliminaTodas 5 [2;1;5;4;1])           = 0.
      nOcurrencias 5 (eliminaTodas 5 [2;1;4;1])             = 0.
      nOcurrencias 4 (eliminaTodas 5 [2;1;4;5;1;4])         = 2.
      nOcurrencias 5 (eliminaTodas 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
   ------------------------------------------------------------------ *)

Fixpoint eliminaTodas (x:nat) (ys:multiconjunto) : multiconjunto :=
  match ys with
  | nil      => nil
  | y :: ys' => if iguales_nat y x
               then eliminaTodas x ys'
               else y :: eliminaTodas x ys'
  end.

Example prop_eliminaTodas1: nOcurrencias 5 (eliminaTodas 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example prop_eliminaTodas2: nOcurrencias 5 (eliminaTodas 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example prop_eliminaTodas3: nOcurrencias 4 (eliminaTodas 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example prop_eliminaTodas4: nOcurrencias 5 (eliminaTodas 5 [1;5;4;5;4;5;1]) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.8. Definir la función
      submulticonjunto : multiconjunto -> multiconjunto -> bool
   tal que (submulticonjunto xs ys) se verifica si xs es un
   submulticonjunto de ys. Por ejemplo,
      submulticonjunto [1;2]   [2;1;4;1] = true.
      submulticonjunto [1;2;2] [2;1;4;1] = false.
   ------------------------------------------------------------------ *)

Fixpoint submulticonjunto (xs:multiconjunto) (ys:multiconjunto) : bool :=
  match xs with
  | nil    => true
  | x::xs' => pertenece x ys && submulticonjunto xs' (eliminaUna x ys)
  end.

Example prop_submulticonjunto1: submulticonjunto [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example prop_submulticonjunto2: submulticonjunto [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.7.9. Escribir una propiedad sobre multiconjuntos con las
   funciones nOcurrencias y demostrarla. 
   ------------------------------------------------------------------ *)

Theorem nOcurrencias_conc: forall xs ys : multiconjunto, forall n:nat,
  nOcurrencias n (conc xs ys) = nOcurrencias n xs + nOcurrencias n ys.
Proof.
  intros xs ys n.               (* xs, ys : multiconjunto
                                   n : nat
                                   ============================
                                   nOcurrencias n (xs ++ ys) = 
                                    nOcurrencias n xs + nOcurrencias n ys *)
  induction xs as [|x xs' HI].
  -                             (* ys : multiconjunto
                                   n : nat
                                   ============================
                                   nOcurrencias n ([ ] ++ ys) = 
                                    nOcurrencias n [ ] + nOcurrencias n ys *)
    simpl.                      (* nOcurrencias n ys = nOcurrencias n ys *)
    reflexivity.
  -                             (* x : nat
                                   xs' : ListaNat
                                   ys : multiconjunto
                                   n : nat
                                   HI : nOcurrencias n (xs' ++ ys) = 
                                        nOcurrencias n xs' + nOcurrencias n ys
                                   ============================
                                   nOcurrencias n ((x :: xs') ++ ys) =
                                    nOcurrencias n (x :: xs') + 
                                    nOcurrencias n ys *)
    simpl.                      (* (if iguales_nat x n
                                    then S (nOcurrencias n (xs' ++ ys))
                                    else nOcurrencias n (xs' ++ ys)) =
                                   (if iguales_nat x n 
                                    then S (nOcurrencias n xs') 
                                    else nOcurrencias n xs') +
                                   nOcurrencias n ys  *)
    destruct (iguales_nat x n). 
    +                           (* S (nOcurrencias n (xs' ++ ys)) = 
                                   S (nOcurrencias n xs') + 
                                   nOcurrencias n ys *)
      simpl.                    (* S (nOcurrencias n (xs' ++ ys)) = 
                                   S (nOcurrencias n xs' + 
                                      nOcurrencias n ys) *)
      rewrite HI.               (* S (nOcurrencias n xs' + nOcurrencias n ys) =
                                   S (nOcurrencias n xs' + nOcurrencias n ys) *)
      reflexivity.
    +                           (* nOcurrencias n (xs' ++ ys) = 
                                   nOcurrencias n xs' + nOcurrencias n ys *)
      rewrite HI.               (* nOcurrencias n xs' + nOcurrencias n ys =
                                   nOcurrencias n xs' + nOcurrencias n ys *)
      reflexivity.
Qed.

(* =====================================================================
   § 3. Razonamiento sobre listas
   ================================================================== *)

(* =====================================================================
   §§ 3.1. Demostraciones por simplificación 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 3.1.1. Demostrar que, para toda lista de naturales xs,
      [] ++ xs = xs
   ------------------------------------------------------------------ *)

Theorem nil_conc : forall xs:ListaNat,
  [] ++ xs = xs.
Proof.
  reflexivity.
Qed.

(* =====================================================================
   §§ 3.2. Demostraciones por casos 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 3.2.1. Demostrar que, para toda lista de naturales xs,
      pred (longitud xs) = longitud (resto xs)
   ------------------------------------------------------------------ *)

Theorem resto_longitud_pred : forall xs:ListaNat,
  pred (longitud xs) = longitud (resto xs).
Proof.
  intros xs.                (* xs : ListaNat
                               ============================
                               Nat.pred (longitud xs) = longitud (resto xs) *)
  destruct xs as [|x xs']. 
  -                         (* 
                               ============================
                               Nat.pred (longitud []) = longitud (resto []) *)
    reflexivity.
  -                         (* x : nat
                               xs' : ListaNat
                               ============================
                               Nat.pred (longitud (x :: xs')) = 
                                longitud (resto (x :: xs')) *)
    reflexivity.
Qed.

(* =====================================================================
   §§ 3.3. Demostraciones por inducción
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 3.3.1. Demostrar que la concatenación de listas de naturales
   es asociativa; es decir,
      (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
   ------------------------------------------------------------------ *)

Theorem conc_asociativa: forall xs ys zs : ListaNat,
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  intros xs ys zs.             (* xs, ys, zs : ListaNat
                                  ============================
                                  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) *)
  induction xs as [|x xs' HI]. 
  -                            (* ys, zs : ListaNat
                                  ============================
                                  ([ ] ++ ys) ++ zs = [ ] ++ (ys ++ zs) *)
    reflexivity.
  -                            (* x : nat
                                  xs', ys, zs : ListaNat
                                  HI : (xs' ++ ys) ++ zs = xs' ++ (ys ++ zs)
                                  ============================
                                  ((x :: xs') ++ ys) ++ zs = 
                                   (x :: xs') ++ (ys ++ zs) *)
    simpl.                     (* (x :: (xs' ++ ys)) ++ zs = 
                                  x :: (xs' ++ (ys ++ zs)) *)
    rewrite -> HI.             (* x :: (xs' ++ (ys ++ zs)) = 
                                  x :: (xs' ++ (ys ++ zs)) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.3.2. Definir la función
      inversa : ListaNat -> ListaNat
   tal que (inversa xs) es la inversa de xs. Por ejemplo,
      inversa [1;2;3] = [3;2;1].
      inversa nil     = nil.

   Nota. La función inversa es equivalente a la predefinida rev.
   ------------------------------------------------------------------ *)

Fixpoint inversa (xs:ListaNat) : ListaNat :=
  match xs with
  | nil    => nil
  | x::xs' => inversa xs' ++ [x]
  end.

Example prop_inversa1: inversa [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.

Example prop_inversa2: inversa nil = nil.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.3.3. Demostrar que
      longitud (inversa xs) = longitud xs
   ------------------------------------------------------------------ *)

(* 1º intento *)
Theorem longitud_inversa1: forall xs:ListaNat,
  longitud (inversa xs) = longitud xs.
Proof.
  intros xs.
  induction xs as [|x xs' HI]. 
  -                            (* 
                                  ============================
                                  longitud (inversa [ ]) = longitud [ ] *)
    reflexivity.
  -                            (* x : nat
                                  xs' : ListaNat
                                  HI : longitud (inversa xs') = longitud xs'
                                  ============================
                                  longitud (inversa (x :: xs')) = 
                                   longitud (x :: xs') *)
    simpl.                     (* longitud (inversa xs' ++ [x]) = 
                                   S (longitud xs')*)
    rewrite <- HI.             (* longitud (inversa xs' ++ [x]) = 
                                   S (longitud (inversa xs')) *)
Abort.

(* Nota: Para simplificar la última expresión se necesita el siguiente lema. *)

Lemma longitud_conc : forall xs ys : ListaNat,
  longitud (xs ++ ys) = longitud xs + longitud ys.
Proof.
  intros xs ys.                 (* xs, ys : ListaNat
                                   ============================
                                   longitud (xs ++ ys) = 
                                    longitud xs + longitud ys *)
  induction xs as [| x xs' HI]. 
  -                             (* ys : ListaNat
                                   ============================
                                   longitud ([ ] ++ ys) = 
                                    longitud [ ] + longitud ys *)
    reflexivity.
  -                             (* x : nat
                                   xs', ys : ListaNat
                                   HI : longitud (xs' ++ ys) = 
                                         longitud xs' + longitud ys
                                   ============================
                                   longitud ((x :: xs') ++ ys) = 
                                   longitud (x :: xs') + longitud ys *)
    simpl.                      (* S (longitud (xs' ++ ys)) = 
                                   S (longitud xs' + longitud ys) *)
    rewrite -> HI.              (* S (longitud xs' + longitud ys) = 
                                   S (longitud xs' + longitud ys) *)
    reflexivity.
Qed.

(* 2º intento *)
Theorem longitud_inversa : forall xs:ListaNat,
  longitud (inversa xs) = longitud xs.
Proof.
  intros xs.                    (* xs : ListaNat
                                   ============================
                                   longitud (inversa xs) = longitud xs *)
  induction xs as [| x xs' HI].
  -                             (* 
                                   ============================
                                   longitud (inversa [ ]) = longitud [ ] *)
    reflexivity.
  -                             (* x : nat
                                   xs' : ListaNat
                                   HI : longitud (inversa xs') = longitud xs'
                                   ============================
                                   longitud (inversa (x :: xs')) = 
                                    longitud (x :: xs') *)
    simpl.                      (* longitud (inversa xs' ++ [x]) = 
                                   S (longitud xs') *)
    rewrite longitud_conc.      (* longitud (inversa xs') + longitud [x] = 
                                   S (longitud xs') *)
    rewrite HI.                 (* longitud xs' + longitud [x] = 
                                   S (longitud xs') *)
    simpl.                      (* longitud xs' + 1 = S (longitud xs') *)
    rewrite suma_conmutativa.   (* 1 + longitud xs' = S (longitud xs') *)
    reflexivity.
Qed.

(* =====================================================================
   §§ 3.4. Ejercicios 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 3.4.1. Demostrar que la lista vacía es el elemento neutro
   por la derecha de la concatenación de listas. 
   ------------------------------------------------------------------ *)

Theorem conc_nil: forall xs:ListaNat,
  xs ++ [] = xs.
Proof.
  intros xs.                    (* xs : ListaNat
                                   ============================
                                   xs ++ [ ] = xs *)
  induction xs as [| x xs' HI]. 
  -                             (* 
                                   ============================
                                   [ ] ++ [ ] = [ ] *)
    reflexivity.
  -                             (* x : nat
                                   xs' : ListaNat
                                   HI : xs' ++ [ ] = xs'
                                   ============================
                                   (x :: xs') ++ [ ] = x :: xs' *)
    simpl.                      (* x :: (xs' ++ [ ]) = x :: xs' *)
    rewrite HI.                 (* x :: xs' = x :: xs' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.2. Demostrar que inversa es un endomorfismo en 
   (ListaNat,++); es decir,
      inversa (xs ++ ys) = inversa ys ++ inversa xs.
   ------------------------------------------------------------------ *)

Theorem inversa_conc: forall xs ys : ListaNat,
  inversa (xs ++ ys) = inversa ys ++ inversa xs.
Proof.
  intros xs ys.                (* xs, ys : ListaNat
                                  ============================
                                  inversa (xs ++ ys) = 
                                  inversa ys ++ inversa xs *)
  induction xs as [|x xs' HI]. 
  -                            (* ys : ListaNat
                                  ============================
                                  inversa ([ ] ++ ys) = 
                                  inversa ys ++ inversa [ ] *)
    simpl.                     (* inversa ys = inversa ys ++ [ ] *)
    rewrite conc_nil.          (* inversa ys = inversa ys *)
    reflexivity.
  -                            (* x : nat
                                  xs', ys : ListaNat
                                  HI : inversa (xs' ++ ys) = 
                                       inversa ys ++ inversa xs'
                                  ============================
                                  inversa ((x :: xs') ++ ys) = 
                                  inversa ys ++ inversa (x :: xs') *)
    simpl.                     (* inversa (xs' ++ ys) ++ [x] = 
                                  inversa ys ++ (inversa xs' ++ [x]) *)
    rewrite HI.                (* (inversa ys ++ inversa xs') ++ [x] = 
                                  inversa ys ++ (inversa xs' ++ [x]) *)
    rewrite conc_asociativa.   (* inversa ys ++ (inversa xs' ++ [x]) = 
                                  inversa ys ++ (inversa xs' ++ [x]) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.3. Demostrar que inversa es involutiva; es decir,
      inversa (inversa xs) = xs.
   ------------------------------------------------------------------ *)

Theorem inversa_involutiva: forall xs:ListaNat,
  inversa (inversa xs) = xs.
Proof.
  induction xs as [|x xs' HI]. 
  -                            (* 
                                  ============================
                                  inversa (inversa [ ]) = [ ] *)
    reflexivity.
  -                            (* x : nat
                                  xs' : ListaNat
                                  HI : inversa (inversa xs') = xs'
                                  ============================
                                  inversa (inversa (x :: xs')) = x :: xs' *)
    simpl.                     (* inversa (inversa xs' ++ [x]) = x :: xs' *)
    rewrite inversa_conc.      (* inversa [x] ++ inversa (inversa xs') = 
                                  x :: xs' *)
    simpl.                     (* x :: inversa (inversa xs') = x :: xs' *)
    rewrite HI.                (* x :: xs' = x :: xs' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.4. Demostrar que
      xs ++ (ys ++ (zs ++ vs)) = ((xs ++ ys) ++ zs) ++ vs.
   ------------------------------------------------------------------ *)

Theorem conc_asociativa4 : forall xs ys zs vs : ListaNat,
  xs ++ (ys ++ (zs ++ vs)) = ((xs ++ ys) ++ zs) ++ vs.
Proof.
  intros xs ys zs vs.      (* xs, ys, zs, vs : ListaNat
                              ============================
                              xs ++ (ys ++ (zs ++ vs)) = 
                              ((xs ++ ys) ++ zs) ++ vs *)
  rewrite conc_asociativa. (* xs ++ (ys ++ (zs ++ vs)) = 
                              (xs ++ ys) ++ (zs ++ vs) *)
  rewrite conc_asociativa. (* xs ++ (ys ++ (zs ++ vs)) =
                              xs ++ (ys ++ (zs ++ vs)) *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.5. Demostrar que al concatenar dos listas no aparecen ni
   desaparecen ceros. 
   ------------------------------------------------------------------ *)

Lemma noCeros_conc : forall xs ys : ListaNat,
  noCeros (xs ++ ys) = (noCeros xs) ++ (noCeros ys).
Proof.
  intros xs ys.                (* xs, ys : ListaNat
                                  ============================
                                  noCeros (xs ++ ys) = 
                                  noCeros xs ++ noCeros ys *)
  induction xs as [|x xs' HI]. 
  -                            (* ys : ListaNat
                                  ============================
                                  noCeros ([] ++ ys) = 
                                  noCeros [] ++ noCeros ys *)
    reflexivity.
  -                            (* x : nat
                                  xs', ys : ListaNat
                                  HI : noCeros (xs' ++ ys) = 
                                       noCeros xs' ++ noCeros ys
                                  ============================
                                  noCeros ((x :: xs') ++ ys) = 
                                  noCeros (x :: xs') ++ noCeros ys *)
    destruct x.
    +                          (* noCeros ((0 :: xs') ++ ys) = 
                                  noCeros (0 :: xs') ++ noCeros ys *)
      simpl.                   (* noCeros (xs' ++ ys) = 
                                  noCeros xs' ++ noCeros ys *)
      rewrite HI.              (* noCeros xs' ++ noCeros ys = 
                                  noCeros xs' ++ noCeros ys *)
      reflexivity.
    +                          (* noCeros ((S x :: xs') ++ ys) = 
                                  noCeros (S x :: xs') ++ noCeros ys *)
      simpl.                   (* S x :: noCeros (xs' ++ ys) = 
                                  (S x :: noCeros xs') ++ noCeros ys *)
      rewrite HI.              (* S x :: (noCeros xs' ++ noCeros ys) = 
                                  (S x :: noCeros xs') ++ noCeros ys *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.6. Definir la función
      iguales_lista : ListaNat -> ListaNat -> bool
   tal que (iguales_lista xs ys) se verifica si las listas xs e ys son
   iguales. Por ejemplo,
      iguales_lista nil nil         = true.
      iguales_lista [1;2;3] [1;2;3] = true.
      iguales_lista [1;2;3] [1;2;4] = false. 
   ------------------------------------------------------------------ *)

Fixpoint iguales_lista (xs ys : ListaNat) : bool:=
  match xs, ys with
  | nil,    nil    => true
  | x::xs', y::ys' => iguales_nat x y && iguales_lista xs' ys'
  | _, _           => false
 end.

Example prop_iguales_lista1: (iguales_lista nil nil = true).
Proof. reflexivity. Qed.

Example prop_iguales_lista2: iguales_lista [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example prop_iguales_lista3: iguales_lista [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.7. Demostrar que la igualdad de listas cumple la
   propiedad reflexiva. 
   ------------------------------------------------------------------ *)

Theorem iguales_lista_refl : forall xs:ListaNat,
  iguales_lista xs xs = true.
Proof.
  induction xs as [|x xs' HI]. 
  -                            (* 
                                  ============================
                                  iguales_lista [ ] [ ] = true *)
    reflexivity.
  -                            (* x : nat
                                  xs' : ListaNat
                                  HI : iguales_lista xs' xs' = true
                                  ============================
                                  iguales_lista (x :: xs') (x :: xs') = true *)
    simpl.                     (* iguales_nat x x && 
                                  iguales_lista xs' xs' = true *)
    rewrite HI.                (* iguales_nat x x && true = true *)
    rewrite iguales_nat_refl.  (* true && true = true *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.8. Demostrar que al incluir un elemento en un
   multiconjunto, ese elemento aparece al menos una vez en el
   resultado. 
   ------------------------------------------------------------------ *)

Theorem nOcurrencias_agrega: forall (x:nat) (xs:multiconjunto),
  menor_o_igual 1 (nOcurrencias x (agrega x xs)) = true.
Proof.
  intros x xs.              (* x : nat
                               xs : multiconjunto
                               ============================
                               menor_o_igual 1 (nOcurrencias x (agrega x xs)) =
                               true *)
  simpl.                    (* match
                                (if iguales_nat x x then S (nOcurrencias x xs) 
                                                    else nOcurrencias x xs)
                                with
                                | 0 => false
                                | S _ => true
                                end = 
                               true *)
  rewrite iguales_nat_refl. (* true = true *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.9. Demostrar que cada número natural es menor o igual
   que su siguiente. 
   ------------------------------------------------------------------ *)

Theorem menor_o_igual_n_Sn: forall n:nat,
  menor_o_igual n (S n) = true.
Proof.
  intros n.                (* n : nat
                              ============================
                              menor_o_igual n (S n) = true *)
  induction n as [|n' HI]. 
  -                        (* 
                              ============================
                              menor_o_igual 0 1 = true *)
    reflexivity.
  -                        (* n' : nat
                              HI : menor_o_igual n' (S n') = true
                              ============================
                              menor_o_igual (S n') (S (S n')) = true *)
    simpl.                 (* menor_o_igual n' (S n') = true *)
    rewrite HI.            (* true = true *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.10. Demostrar que al borrar una ocurrencia de 0 de un
   multiconjunto el número de ocurrencias de 0 en el resultado es menor
   o igual que en el original.
   ------------------------------------------------------------------ *)

Theorem remove_decreases_nOcurrencias: forall (xs : multiconjunto),
  menor_o_igual (nOcurrencias 0 (eliminaUna 0 xs)) (nOcurrencias 0 xs) = true.
Proof.
  induction xs as [|x xs' HI].
  -                               (* 
                                     ============================
                                     menor_o_igual (nOcurrencias 0 (eliminaUna 0 [])) 
                                                   (nOcurrencias 0 []) 
                                     = true *)
    reflexivity.
  -                               (* x : nat
                                     xs' : ListaNat
                                     HI: menor_o_igual (nOcurrencias 0 (eliminaUna 0 xs'))
                                                        (nOcurrencias 0 xs') 
                                         = true 
                                     ============================
                                     menor_o_igual (nOcurrencias 0 (eliminaUna 0 (x::xs')))
                                                    (nOcurrencias 0 (x :: xs')) 
                                     = true *)
    destruct x.
    +                             (* menor_o_igual (nOcurrencias 0 (eliminaUna 0 (0::xs')))
                                                   (nOcurrencias 0 (0 :: xs')) 
                                     = true *)
      simpl.                      (* menor_o_igual (nOcurrencias 0 xs') 
                                                   (S (nOcurrencias 0 xs')) 
                                     = true *)
      rewrite menor_o_igual_n_Sn. (* true = true *)
      reflexivity.
    +                             (* menor_o_igual (nOcurrencias 0 
                                                     (eliminaUna 0 (S x :: xs')))
                                                   (nOcurrencias 0 (S x :: xs')) 
                                     = true *)
      simpl.                      (* menor_o_igual (nOcurrencias 0 (eliminaUna 0 xs')) 
                                                   (nOcurrencias 0 xs') 
                                     = true *)
      rewrite HI.                 (* true = true *)
      reflexivity.
Qed.    

(* ---------------------------------------------------------------------
   Ejercicio 3.4.11. Escribir un teorema con las funciones nOcurrencias
   y suma de los multiconjuntos. 
   ------------------------------------------------------------------ *)

Theorem nOcurrencias_suma:
  forall x : nat, forall xs ys : multiconjunto,
   nOcurrencias x (suma xs ys) = nOcurrencias x xs + nOcurrencias x ys.
Proof.
  intros x xs ys.                (* x : nat
                                    xs, ys : multiconjunto
                                    ============================
                                    nOcurrencias x (suma xs ys) = 
                                    nOcurrencias x xs + nOcurrencias x ys *)
  induction xs as [|x' xs' HI].
  -                              (* x : nat
                                    ys : multiconjunto
                                    ============================
                                    nOcurrencias x (suma [ ] ys) = 
                                    nOcurrencias x [ ] + nOcurrencias x ys *)
    reflexivity.
  -                              (* x, x' : nat
                                    xs' : ListaNat
                                    ys : multiconjunto
                                    HI : nOcurrencias x (suma xs' ys) = 
                                         nOcurrencias x xs' + nOcurrencias x ys
                                    ============================
                                    nOcurrencias x (suma (x' :: xs') ys) = 
                                    nOcurrencias x (x' :: xs') + nOcurrencias x ys *)
    simpl.                       (* (if iguales_nat x' x
                                        then S (nOcurrencias x (suma xs' ys))
                                        else nOcurrencias x (suma xs' ys)) 
                                    =
                                    (if iguales_nat x' x 
                                        then S (nOcurrencias x xs') 
                                        else nOcurrencias x xs') + nOcurrencias x ys *)
    destruct (iguales_nat x' x). 
    +                            (* S (nOcurrencias x (suma xs' ys)) = 
                                    S (nOcurrencias x xs') + nOcurrencias x ys *)
      rewrite HI.                (* S (nOcurrencias x xs' + nOcurrencias x ys) = 
                                    S (nOcurrencias x xs') + nOcurrencias x ys *)
      reflexivity.
    +                            (* nOcurrencias x (suma xs' ys) = 
                                    nOcurrencias x xs' + nOcurrencias x ys *)
      rewrite HI.                (* nOcurrencias x xs' + nOcurrencias x ys = 
                                    nOcurrencias x xs' + nOcurrencias x ys *)
      reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.4.12. Demostrar que la función inversa es inyectiva; es
   decir, 
      forall (xs ys : ListaNat), inversa xs = inversa ys -> xs = ys. 
   ------------------------------------------------------------------ *)

Theorem inversa_inyectiva: forall (xs ys : ListaNat),
  inversa xs = inversa ys -> xs = ys.
Proof.
  intros xs ys H.                (* xs, ys : ListaNat
                                    H : inversa xs = inversa ys
                                    ============================
                                    xs = ys *)
  rewrite <- inversa_involutiva. (* xs = inversa (inversa ys) *)
  rewrite <- H.                  (* xs = inversa (inversa xs) *)
  rewrite inversa_involutiva.    (* xs = xs *)
  reflexivity.
Qed.

(* =====================================================================
   § 4. Opcionales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 4.1. Definir el tipo OpcionalNat con los contructores
      Some : nat -> OpcionalNat
      None : OpcionalNat.
   ------------------------------------------------------------------ *)

Inductive OpcionalNat : Type :=
  | Some : nat -> OpcionalNat
  | None : OpcionalNat.

(* ---------------------------------------------------------------------
   Ejemplo 4.2. Definir la función
      nthOpcional : ListaNat -> nat -> OpcionalNat
   tal que (nthOpcional xs n) es el n-ésimo elemento de la lista xs o None
   si la lista tiene menos de n elementos. Por ejemplo,
      nthOpcional [4;5;6;7] 0 = Some 4.
      nthOpcional [4;5;6;7] 3 = Some 7.
      nthOpcional [4;5;6;7] 9 = None.
   ------------------------------------------------------------------ *)

Fixpoint nthOpcional (xs:ListaNat) (n:nat) : OpcionalNat :=
  match xs with
  | nil      => None
  | x :: xs' => match iguales_nat n O with
                | true  => Some x
                | false => nthOpcional xs' (pred n)
                end
  end.

Example prop_nthOpcional1 : nthOpcional [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example prop_nthOpcional2 : nthOpcional [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example prop_nthOpcional3 : nthOpcional [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Introduciendo condicionales nos queda: *)
Fixpoint nthOpcional' (xs:ListaNat) (n:nat) : OpcionalNat :=
  match xs with
  | nil      => None
  | x :: xs' => if iguales_nat x O
                then Some x
                else nthOpcional' xs' (pred n)
  end.

(* ---------------------------------------------------------------------
   Ejemplo 4.3. Definir la función
      eliminaOpcionalNat -> OpcionalNat -> nat
   tal que (option_elim d o) es el valor de o, si o tiene valor o es d
   en caso contrario. Por ejemplo,
      eliminaOpcionalNat 3 (Some 7) = 7
      eliminaOpcionalNat 3 None     = 3
   ------------------------------------------------------------------ *)

Definition eliminaOpcionalNat (d : nat) (o : OpcionalNat) : nat :=
  match o with
  | Some n' => n'
  | None    => d
  end.

Compute (eliminaOpcionalNat 3 (Some 7)).
(* ===> 7 : nat *)
Compute (eliminaOpcionalNat 3 None).
(* ===> 3 : nat *)

(* ---------------------------------------------------------------------
   Ejercicio 4.1. Definir la función
      primeroOpcional : ListaNat -> OpcionalNat
   tal que (primeroOpcional xs) es el primer elemento de xs, si xs es no
   vacía; o es None, en caso contrario. Por ejemplo,
      primeroOpcional []    = None.
      primeroOpcional [1]   = Some 1.
      primeroOpcional [5;6] = Some 5.
   ------------------------------------------------------------------ *)

Definition primeroOpcional (xs : ListaNat) : OpcionalNat :=
  match xs with
  | nil    => None
  | x::xs' => Some x
  end.

Example prop_primeroOpcional1 : primeroOpcional [] = None.
Proof. reflexivity. Qed.

Example prop_primeroOpcional2 : primeroOpcional [1] = Some 1.
Proof. reflexivity. Qed.

Example prop_primeroOpcional3 : primeroOpcional [5;6] = Some 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4.2. Demostrar que
      primero d xs = eliminaOpcionalNat d (primeroOpcional xs).
   ------------------------------------------------------------------ *)

Theorem primero_primeroOpcional: forall (xs:ListaNat) (d:nat),
  primero d xs = eliminaOpcionalNat d (primeroOpcional xs).
Proof.
  intros xs d.             (* xs : ListaNat
                              d : nat
                              ============================
                              primero d xs = eliminaOpcionalNat d (primeroOpcional xs) *)
  destruct xs as [|x xs']. 
  -                        (* d : nat
                              ============================
                              primero d [] = eliminaOpcionalNat d (primeroOpcional []) *)
    reflexivity.
  -                        (* x : nat
                              xs' : ListaNat
                              d : nat
                              ============================
                              primero d (x :: xs') = 
                              eliminaOpcionalNat d (primeroOpcional (x :: xs')) *)
    simpl.                 (* x = x *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Finalizar el módulo ListaNat.
   ------------------------------------------------------------------ *)

End ListaNat.

(* =====================================================================
   § 5. Diccionarios (o funciones parciales)
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 5.1. Definir el tipo id (por identificador) con el
   constructor 
      Id : nat -> id.
   ------------------------------------------------------------------ *)

Inductive id : Type :=
  | Id : nat -> id.

(* ---------------------------------------------------------------------
   Ejemplo 5.2. Definir la función
      iguales_id : id -> id -> bool
   tal que (iguales_id x1 x2) se verifica si tienen la misma clave. Por
   ejemplo, 
      iguales_id (Id 3) (Id 3) = true : bool
      iguales_id (Id 3) (Id 4) = false : bool
   ------------------------------------------------------------------ *)

Definition iguales_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => iguales_nat n1 n2
  end.

Compute (iguales_id (Id 3) (Id 3)).
(* ===> true : bool *)
Compute (iguales_id (Id 3) (Id 4)).
(* ===> false : bool *)

(* ---------------------------------------------------------------------
   Ejercicio 5.1. Demostrar que iguales_id es reflexiva.
   ------------------------------------------------------------------ *)

Theorem iguales_id_refl : forall x:id, iguales_id x x = true.
Proof.
  intro x.                  (* x : id
                               ============================
                               iguales_id x x = true *)
  destruct x.               (* iguales_id (Id n) (Id n) = true *)
  simpl.                    (* iguales_nat n n = true *)
  rewrite iguales_nat_refl. (* true = true *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.3. Iniciar el módulo Diccionario que importa a ListaNat.
   ------------------------------------------------------------------ *)

Module Diccionario.
Export ListaNat.

(* ---------------------------------------------------------------------
   Ejemplo 5.4. Definir el tipo diccionario con los contructores
      vacio    : diccionario
      registro : id -> nat -> diccionario -> diccionario.
   ------------------------------------------------------------------ *)

Inductive diccionario : Type :=
  | vacio    : diccionario
  | registro : id -> nat -> diccionario -> diccionario.

(* ---------------------------------------------------------------------
   Ejemplo 5.5. Definir los diccionarios cuyos elementos son
      + []
      + [(3,6)]
      + [(2,4), (3,6)]
   ------------------------------------------------------------------ *)

Definition diccionario1 := vacio.
Definition diccionario2 := registro (Id 3) 6 diccionario1.
Definition diccionario3 := registro (Id 2) 4 diccionario2.

(* ---------------------------------------------------------------------
   Ejemplo 5.6. Definir la función
      valor : id -> diccionario -> OpcionalNat 
   tal que (valor i d) es el valor de la entrada de d con clave i, o
   None si d no tiene ninguna entrada con clave i. Por ejemplo,
      valor (Id 2) diccionario3 = Some 4
      valor (Id 2) diccionario2 = None
   ------------------------------------------------------------------ *)

Fixpoint valor (x : id) (d : diccionario) : OpcionalNat :=
  match d with
  | vacio           => None
  | registro y v d' => if iguales_id x y
                      then Some v
                      else valor x d'
  end.

Compute (valor (Id 2) diccionario3).
(* = Some 4 : OpcionalNat *)
Compute (valor (Id 2) diccionario2).
(* = None : OpcionalNat*)

(* ---------------------------------------------------------------------
   Ejemplo 5.7. Definir la función
      actualiza : diccionario -> id -> nat -> diccionario
   tal que (actualiza d x v) es el diccionario obtenido a partir del d
   + si d tiene un elemento con clave x, le cambia su valor a v
   + en caso contrario, le añade el elemento v con clave x 
   ------------------------------------------------------------------ *)

Definition actualiza (d : diccionario)
                     (x : id) (v : nat)
                     : diccionario :=
  registro x v d.

(* ---------------------------------------------------------------------
   Ejercicio 5.2. Demostrar que
      forall (d : diccionario) (x : id) (v: nat),
        valor x (actualiza d x v) = Some v.
   ------------------------------------------------------------------ *)

Theorem valor_actualiza: forall (d : diccionario) (x : id) (v: nat),
    valor x (actualiza d x v) = Some v.
Proof.
  intros d x v.             (* d : diccionario
                               x : id
                               v : nat
                               ============================
                               valor x (actualiza d x v) = Some v *)
  destruct x.               (* valor (Id n) (actualiza d (Id n) v) = Some v *)
  simpl.                    (* (if iguales_nat n n then Some v 
                                                   else valor (Id n) d) 
                               = Some v *)
  rewrite iguales_nat_refl. (* Some v = Some v *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5.3. Demostrar que
      forall (d : diccionario) (x y : id) (o: nat),
        iguales_id x y = false -> valor x (actualiza d y o) = valor x d.
   ------------------------------------------------------------------ *)

Theorem actualiza_neq :
  forall (d : diccionario) (x y : id) (o: nat),
    iguales_id x y = false -> valor x (actualiza d y o) = valor x d.
Proof.
  intros d x y o p. (* d : diccionario
                       x, y : id
                       o : nat
                       p : iguales_id x y = false
                       ============================
                       valor x (actualiza d y o) = valor x d *)
  simpl.            (* (if iguales_id x y then Some o 
                                          else valor x d) 
                       = valor x d *)
  rewrite p.        (* valor x d = valor x d *)
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 5.8. Finalizar el módulo Diccionario
   ------------------------------------------------------------------ *)

End Diccionario.

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Working with structured data" de Peirce et als. 
   http://bit.ly/2LQABsv
 *)
