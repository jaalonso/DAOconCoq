(* T3: Datos estructurados en Coq *)

Require Export T2_Induccion.

(* Pendiente de borrar la siguiente importación. *)
Require Export Lists.List.

(* =====================================================================
   § 1. Pares de números 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Nota. Se iniciar el módulo ListaNat.
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
   § 2.1. El tipo de la lista de números. 
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
   § 2.2. La función repite (repeat)  
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
   § 2.3. La función longitud (length)  
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
   § 2.4. La función conc (app)  
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
   § 2.5. Las funciones primero (hd) y resto (tl)
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
   § 2.6. Ejercicios sobre listas de números 
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
   Ejercicio 12. Definir la función
      remove_all : nat -> multiconjunto -> multiconjunto
   tal que (remove_all x ys) es el multiconjunto obtenido eliminando
   todas las ocurrencias de x en el multiconjunto ys. Por ejemplo,
      nOcurrencias 5 (remove_all 5 [2;1;5;4;1])           = 0.
      nOcurrencias 5 (remove_all 5 [2;1;4;1])             = 0.
      nOcurrencias 4 (remove_all 5 [2;1;4;5;1;4])         = 2.
      nOcurrencias 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
   ------------------------------------------------------------------ *)

Fixpoint remove_all (v:nat) (s:multiconjunto) : multiconjunto :=
   match s with
  | nil => nil
  | t :: xs => if iguales_nat t v
               then remove_all v xs
               else t :: remove_all v xs
  end.

Example prop_remove_all1: nOcurrencias 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example prop_remove_all2: nOcurrencias 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example prop_remove_all3: nOcurrencias 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example prop_remove_all4: nOcurrencias 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 13. Definir la función
      subset : multiconjunto -> multiconjunto -> bool
   tal que (subset xs ys) se verifica si xs es un sub,ulticonjunto de
   ys. Por ejemplo,
      subset [1;2]   [2;1;4;1] = true.
      subset [1;2;2] [2;1;4;1] = false.
   ------------------------------------------------------------------ *)

Fixpoint subset (s1:multiconjunto) (s2:multiconjunto) : bool :=
  match s1 with
  | nil   => true
  | x::xs => pertenece x s2 && subset xs (eliminaUna x s2)
  end.

Example prop_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example prop_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 14. Escribir un teorema sobre multiconjuntos con las funciones
   nOcurrencias y agrega y probarlo. 
   ------------------------------------------------------------------ *)

Theorem multiconjunto_theorem : forall s1 s2 : multiconjunto, forall n : nat,
  nOcurrencias n s1 + nOcurrencias n s2 = nOcurrencias n (conc s1 s2).                 
Proof.
  intros s1 s2 n. induction s1 as [|s s'].
 - simpl. reflexivity.
 - simpl. destruct (iguales_nat s n).
    + simpl. rewrite IHs'. reflexivity.
    + rewrite IHs'. reflexivity.
Qed.

(* =====================================================================
   § 3. Razonamiento sobre listas
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que, para toda lista de naturales l,
      [] ++ l = l
   ------------------------------------------------------------------ *)

Theorem nil_conc : forall l:ListaNat,
  [] ++ l = l.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que, para toda lista de naturales l,
      pred (longitud l) = longitud (resto l)
   ------------------------------------------------------------------ *)

Theorem resto_longitud_pred : forall l:ListaNat,
  pred (longitud l) = longitud (resto l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

(* =====================================================================
   §§ 3.1. Inducción sobre listas
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que la concatenación de listas de naturales es
   asociativa. 
   ------------------------------------------------------------------ *)

Theorem conc_assoc : forall l1 l2 l3 : ListaNat,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* Comentar los nombres dados en la hipótesis de inducción. *)

(* =====================================================================
   §§§ Inversa de una lista  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      rev : ListaNat -> ListaNat
   tal que (rev xs) es la inversa de xs. Por ejemplo,
      rev [1;2;3] = [3;2;1].
      rev nil     = nil.
   ------------------------------------------------------------------ *)

Fixpoint rev (l:ListaNat) : ListaNat :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example prop_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example prop_rev2: rev nil = nil.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§§ Propiedaes de la función rev  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      longitud (rev l) = longitud l
   ------------------------------------------------------------------ *)

Theorem rev_longitud_firsttry : forall l : ListaNat,
  longitud (rev l) = longitud l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* Probamos simplificando *)
    simpl.
    rewrite <- IHl'.
    (* Nos encontramos sin más que hacer, así que buscamos un lema que
       nos ayude. *) 
Abort.

Theorem conc_longitud : forall l1 l2 : ListaNat,
  longitud (l1 ++ l2) = (longitud l1) + (longitud l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* Ahora completamos la prueba original. *)

Theorem rev_longitud : forall l : ListaNat,
  longitud (rev l) = longitud l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> conc_longitud, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(* =====================================================================
   § Ejercicios 
   ================================================================== *)

(* =====================================================================
   §§ Ejercicios: 1ª parte 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 15. Demostrar que la lista vacía es el elemento neutro por la
   derecha de la concatenación de listas. 
   ------------------------------------------------------------------ *)

Theorem conc_nil_r : forall l : ListaNat,
  l ++ [] = l.
Proof.
  intros l. induction l as [| x xs HI].
  - reflexivity.
  - simpl. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 16. Demostrar que rev es un endomorfismo en (ListaNat,++)
   ------------------------------------------------------------------ *)
Theorem rev_conc_distr: forall l1 l2 : ListaNat,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|x xs HI].
  - simpl. rewrite conc_nil_r. reflexivity.
  - simpl. rewrite HI, conc_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 17. Demostrar que rev es involutiva.
   ------------------------------------------------------------------ *)

Theorem rev_involutive : forall l : ListaNat,
  rev (rev l) = l.
Proof.
  induction l as [|x xs HI].
  - reflexivity.
  - simpl. rewrite rev_conc_distr. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 18. Demostrar que
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
   ------------------------------------------------------------------ *)

Theorem conc_assoc4 : forall l1 l2 l3 l4 : ListaNat,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite conc_assoc. rewrite conc_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 19. Demostrar que al concatenar dos listas no aparecen ni
   desaparecen ceros. 
   ------------------------------------------------------------------ *)

Lemma noCeros_conc : forall l1 l2 : ListaNat,
  noCeros (l1 ++ l2) = (noCeros l1) ++ (noCeros l2).
Proof.
  intros l1 l2. induction l1 as [|x xs HI].
  - reflexivity.
  - simpl. destruct x.
    + rewrite HI. reflexivity.
    + simpl. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 20. Definir la función
      beq_ListaNat : ListaNat -> ListaNat -> bool
   tal que (beq_ListaNat xs ys) se verifica si las listas xs e ys son
   iguales. Por ejemplo,
      beq_ListaNat nil nil         = true.
      beq_ListaNat [1;2;3] [1;2;3] = true.
      beq_ListaNat [1;2;3] [1;2;4] = false. 
   ------------------------------------------------------------------ *)

Fixpoint beq_ListaNat (l1 l2 : ListaNat) : bool:=
  match l1, l2 with
  | nil,   nil   => true
  | x::xs, y::ys => iguales_nat x y && beq_ListaNat xs ys
  | _, _         => false
 end.

Example prop_beq_ListaNat1: (beq_ListaNat nil nil = true).
Proof. reflexivity. Qed.
Example prop_beq_ListaNat2: beq_ListaNat [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example prop_beq_ListaNat3: beq_ListaNat [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 21. Demostrar que la igualdad de listas cumple la propiedad
   reflexiva. 
   ------------------------------------------------------------------ *)

Theorem beq_ListaNat_refl : forall l:ListaNat,
  true = beq_ListaNat l l.
Proof.
  induction l as [|n xs HI].
  - reflexivity.
  - simpl. rewrite <- HI. replace (iguales_nat n n) with true.  reflexivity.
    + rewrite <- iguales_nat_refl. reflexivity.
Qed.

(* =====================================================================
   §§ Ejercicios: 1ª parte 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 22. Demostrar que al incluir un elemento en un multiconjunto,
   ese elemento aparece al menos una vez en el resultado.
   ------------------------------------------------------------------ *)

Theorem nOcurrencias_pertenece_nonzero : forall (s : multiconjunto),
  leb 1 (nOcurrencias 1 (1 :: s)) = true.
Proof.
 intro s.  simpl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 23. Demostrar que cada número natural es menor o igual que
   su siguiente. 
   ------------------------------------------------------------------ *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 24. Demostrar que al borrar una ocurrencia de 0 de un
   multiconjunto el número de ocurrencias de 0 en el resultado es menor
   o igual que en el original.
   ------------------------------------------------------------------ *)

Theorem remove_decreases_nOcurrencias: forall (s : multiconjunto),
  leb (nOcurrencias 0 (eliminaUna 0 s)) (nOcurrencias 0 s) = true.
Proof.
  induction s as [|x xs HI].
  - reflexivity.
  - simpl. destruct x.
    + rewrite ble_n_Sn. reflexivity.
    + simpl. rewrite HI. reflexivity.
Qed.    

(* ---------------------------------------------------------------------
   Ejercicio 25. Escribir un teorema con las funciones nOcurrencias y suma de los
   multiconjuntos. 
   ------------------------------------------------------------------ *)

Theorem multiconjunto_nOcurrencias_sum: forall n : nat, forall b1 b2 : multiconjunto,
  nOcurrencias n b1 + nOcurrencias n b2 = nOcurrencias n (suma b1 b2).
Proof.
  intros n b1 b2. induction b1 as [|b bs HI].
  - reflexivity.
  - simpl. destruct (iguales_nat b n).
    + simpl. rewrite HI. reflexivity.
    + rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 26. Demostrar que la función rev es inyectiva; es decir,
      forall (l1 l2 : ListaNat), rev l1 = rev l2 -> l1 = l2.
   ------------------------------------------------------------------ *)

Theorem rev_injective : forall (l1 l2 : ListaNat),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. rewrite <- rev_involutive, <- H, rev_involutive. reflexivity.
Qed.

(* =====================================================================
   § 4. Opcionales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      nth_bad : ListaNat -> n -> nat
   tal que (nth_bad xs n) es el n-ésimo elemento de la lista xs y 42 si
   la lista tiene menos de n elementos. 
   ------------------------------------------------------------------ *)

Fixpoint nth_bad (l:ListaNat) (n:nat) : nat :=
  match l with
  | nil     => 42  (* un valor arbitrario *)
  | a :: l' => match iguales_nat n O with
               | true  => a
               | false => nth_bad l' (pred n)
               end
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo natoption con los contructores
      Some : nat -> natoption
      None : natoption.
   ------------------------------------------------------------------ *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      nth_error : ListaNat -> nat -> natoption
   tal que (nth_error xs n) es el n-ésimo elemento de la lista xs o None
   si la lista tiene menos de n elementos. Por ejemplo,
      nth_error [4;5;6;7] 0 = Some 4.
      nth_error [4;5;6;7] 3 = Some 7.
      nth_error [4;5;6;7] 9 = None.
   ------------------------------------------------------------------ *)

Fixpoint nth_error (l:ListaNat) (n:nat) : natoption :=
  match l with
  | nil     => None
  | a :: l' => match iguales_nat n O with
               | true  => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example prop_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example prop_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example prop_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Introduciendo condicionales nos queda: *)

Fixpoint nth_error' (l:ListaNat) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if iguales_nat n O
               then Some a
               else nth_error' l' (pred n)
  end.

(* Nota: Los condicionales funcionan sobre todo tipo inductivo con dos 
   constructores en Coq, sin booleanos. *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      option_elim nat -> natoption -> nat
   tal que (option_elim d o) es el valor de o, si o tienve valor o es d
   en caso contrario.
   ------------------------------------------------------------------ *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* ---------------------------------------------------------------------
   Ejercicio 27. Definir la función
      primero_error : ListaNat -> natoption
   tal que (primero_error xs) es el primer elemento de xs, si xs es no vacía;
   o es None, en caso contrario. Por ejemplo,
      primero_error []    = None.
      primero_error [1]   = Some 1.
      primero_error [5;6] = Some 5.
   ------------------------------------------------------------------ *)

Definition primero_error (l : ListaNat) : natoption :=
  match l with
  | nil   => None
  | x::xs => Some x
  end.

Example prop_primero_error1 : primero_error [] = None.
Proof. reflexivity. Qed.
Example prop_primero_error2 : primero_error [1] = Some 1.
Proof. reflexivity. Qed.
Example prop_primero_error3 : primero_error [5;6] = Some 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 28. Demostrar que
      primero default l = option_elim default (primero_error l).
   ------------------------------------------------------------------ *)

Theorem option_elim_primero : forall (l:ListaNat) (default:nat),
  primero default l = option_elim default (primero_error l).
Proof.
  intros l default. destruct l as [|x xs].
  - reflexivity.
  - simpl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Finalizar el módulo ListaNat.
   ------------------------------------------------------------------ *)

End ListaNat.

(* =====================================================================
   § 5. Funciones parciales (o diccionarios)
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo id con el constructor
      Id : nat -> id.
   La idea es usarlo como clave de los dicccionarios.
   ------------------------------------------------------------------ *)

Inductive id : Type :=
  | Id : nat -> id.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      beq_id : id -> id -> bool
   tal que  (beq_id x1 x2) se verifcia si tienen la misma clave.
   ------------------------------------------------------------------ *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => iguales_nat n1 n2
  end.

(* ---------------------------------------------------------------------
   Ejercicio 29. Demostrar que beq_id es reflexiva.
   ------------------------------------------------------------------ *)

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intro x. destruct x. simpl. rewrite <- iguales_nat_refl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Iniciar el módulo PartialMap que importa a ListaNat.
   ------------------------------------------------------------------ *)

Module PartialMap.
Export ListaNat.

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo partial_map (para representar los
   diccionarios) con los contructores
      empty  : partial_map
      record : id -> nat -> partial_map -> partial_map.
   ------------------------------------------------------------------ *)

Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.


(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      update : partial_map -> id -> nat -> partial_map
   tal que (update d i v) es el diccionario obtenido a partir del d
   + si d tiene un elemento con clave i, le cambia su valor a v
   + en caso contrario, le añade el elemento v con clave i 
   ------------------------------------------------------------------ *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      find : id -> partial_map -> natoption 
   tal que (find i d) es el valor de la entrada de d con clave i, o None
   si d no tiene ninguna entrada con clave i.
   ------------------------------------------------------------------ *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

(* ---------------------------------------------------------------------
   Ejercicio 30. Demostrar que
      forall (d : partial_map) (x : id) (v: nat),
        find x (update d x v) = Some v.
   ------------------------------------------------------------------ *)

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. destruct d as [|d' x' v'].
  - simpl. destruct x. simpl. rewrite <- iguales_nat_refl. reflexivity.
  - simpl. destruct x. simpl. rewrite <- iguales_nat_refl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 31. Demostrar que
      forall (d : partial_map) (x y : id) (o: nat),
        beq_id x y = false -> find x (update d y o) = find x d.
   ------------------------------------------------------------------ *)

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o p. simpl. rewrite p. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Nota. Finalizr el módulo PartialMap
   ------------------------------------------------------------------ *)

End PartialMap.

(* ---------------------------------------------------------------------
   Ejercicio 32. Se define el tipo baz por
      Inductive baz : Type :=
        | Baz1 : baz -> baz
        | Baz2 : baz -> bool -> baz.
   ¿Cuántos elementos tiene el tipo baz?
   ------------------------------------------------------------------ *)

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Working with structured data" de Peirce et als. http://bit.ly/2LQABsv
 *)
