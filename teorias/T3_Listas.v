(* T3: Datos estructurados en Coq *)

Require Export T2_Induccion.

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

(* ---------------------------------------------------------------------
   Ejemplo. natlist es la lista de los números naturales y sus
   constructores son 
   + nil (la lista vacía) y 
   + cons (tal que (cons x ys) es la lista obtenida añadiéndole x a ys. 
   ------------------------------------------------------------------ *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la constante 
      mylist : natlist
   que es la lista cuyos elementos son 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la notación (x :: ys) como una abreviatura de 
   (cons x ys).
   ------------------------------------------------------------------ *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la notación de las listas finitas escribiendo sus
   elementos entre corchetes y separados por puntos y comas.
   ------------------------------------------------------------------ *)

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* ---------------------------------------------------------------------
   Ejemplo. Distintas representaciones de mylist.
   ------------------------------------------------------------------ *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(* =====================================================================
   §§ 2.1. Repeat  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      repeat : nat -> nat -> natlist
   tal que (repeat n k) es la lista formada por k veces el número n.
   ------------------------------------------------------------------ *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O        => nil
  | S count' => n :: (repeat n count')
  end.

(* =====================================================================
   §§ Length  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      length : natlist -> nat
   tal que (length xs) es el número de elementos de xs.
   ------------------------------------------------------------------ *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil    => O
  | h :: t => S (length t)
  end.

(* =====================================================================
   §§ Append  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      append : natlist -> natlist -> natlist
   tal que (append xs ys) es la concatenación de xs e ys.
   ------------------------------------------------------------------ *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la notación (xs ++ ys) como una abreviaura de 
   (append xs ys).
   ------------------------------------------------------------------ *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      [1;2;3] ++ [4;5] = [1;2;3;4;5].
      nil     ++ [4;5] = [4;5].
      [1;2;3] ++ nil   = [1;2;3].
   ------------------------------------------------------------------ *)

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ Head y tail  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      hd : nat -> natlist -> natlist
   tal que (hd d xs) es el primer elemento de xs o d, si xs es la lista
   vacía. 
   ------------------------------------------------------------------ *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil    => default
  | h :: t => h
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      tl : natlist -> natlist
   tal que (tl xs) es el resto de xs.
   ------------------------------------------------------------------ *)

Definition tl (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => t
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que 
       hd 0 [1;2;3] = 1.
       hd 0 []      = 0.
       tl [1;2;3]   = [2;3].
   ------------------------------------------------------------------ *)

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3. Definir la función
      nonzeros : natlist -> natlist
   tal que (nonzeros xs) es la lista de los elementos de xs distintos de
   cero. Por ejemplo,
      nonzeros [0;1;0;2;3;0;0] = [1;2;3].
   ------------------------------------------------------------------ *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | a::bs => match a with
            | 0 => nonzeros bs 
            | _ =>  a:: nonzeros bs end
 end.
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint nonzeros2 (l:natlist) : natlist :=
 match l with
  | nil => nil
  | h :: t => if(beq_nat h 0) then nonzeros2 t else h :: nonzeros2 t end.

Example test_nonzeros2: nonzeros2 [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 4. Definir la función
      oddmembers : natlist -> natlist
   tal que (oddmembers xs) es la lista de los elementos impares de
   xs. Por ejemplo,
      oddmembers [0;1;0;2;3;0;0] = [1;3].
   ------------------------------------------------------------------ *)

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | t::xs => if oddb t then t :: oddmembers xs else oddmembers xs
  end.
 
Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 5. Definir la función
      countoddmembers : natlist -> nat
   tal que (countoddmembers xs) es el número de elementos impares de
   xs. Por ejemplo,
      countoddmembers [1;0;3;1;4;5] = 4.
      countoddmembers [0;2;4]       = 0.
      countoddmembers nil           = 0.
   ------------------------------------------------------------------ *)

Definition countoddmembers (l:natlist) : nat :=
 length (oddmembers l). 

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 6. Definir la función
      alternate : natlist -> natlist -> natlist
   tal que (alternate xs ys) es la lista obtenida intercalando los
   elementos de xs e ys. Por ejemplo,
      alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
      alternate [1] [4;5;6]     = [1;4;5;6].
      alternate [1;2;3] [4]     = [1;4;2;3].
      alternate [] [20;30]      = [20;30].
   ------------------------------------------------------------------ *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | t::xs => match l2 with
            | nil => t::xs
            | p::ys => t::p::alternate xs ys end
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(* =====================================================================
   §§ Multiconjuntos como listas 
   ================================================================== *)

(* Un multiconjunto es como un conjunto donde los elementos pueden
   repetirse más de una vez. Podemos implementarlos como listas.  *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo baf de los multiconjuntos de números
   naturales. 
   ------------------------------------------------------------------ *)

Definition bag := natlist.

(* ---------------------------------------------------------------------
   Ejercicio 7. Definir la función
      count : nat -> bag -> nat 
   tal que (count v s) es el número des veces que aparece el elemento v
   en el multiconjunto s. Por ejemplo,
      count 1 [1;2;3;1;4;1] = 3.
      count 6 [1;2;3;1;4;1] = 0.
   ------------------------------------------------------------------ *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil   => 0
  | t::xs => if beq_nat t v
            then 1 + count v xs
            else count v xs
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed. 

(* ---------------------------------------------------------------------
   Ejercicio 8. Definir la función
      sum : bag -> bag -> bag
   tal que (sum xs ys) es la suma de los multiconjuntos xs e ys. Por
   ejemplo, 
      count 1 (sum [1;2;3] [1;4;1]) = 3.
   ------------------------------------------------------------------ *)

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 9. Definir la función
      add : nat -> bag -> bag
   tal que (add x ys) es el multiconjunto obtenido añadiendo el elemento
   x al multiconjunto ys. Por ejemplo,
      count 1 (add 1 [1;4;1]) = 3.
      count 5 (add 1 [1;4;1]) = 0.
   ------------------------------------------------------------------ *)

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 10. Definir la función
      member : nat -> bag -> bool
   tal que (member x ys) se verfica si x pertenece al multiconjunto
   ys. Por ejemplo,  
      member 1 [1;4;1] = true.
      member 2 [1;4;1] = false.
   ------------------------------------------------------------------ *)

Definition member (v:nat) (s:bag) : bool := 
  if beq_nat 0 (count v s)
  then false
  else true.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Definition member2 (v:nat) (s:bag) : bool :=
  negb (beq_nat O (count v s)).

Example test_member2_1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2_2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 11. Definir la función
      remove_one : nat -> bag -> bag
   tal que (remove_one x ys) es el multiconjunto obtenido eliminando una
   ocurrencia de x en el multiconjunto ys. Por ejemplo, 
      count 5 (remove_one 5 [2;1;5;4;1])     = 0.
      count 4 (remove_one 5 [2;1;4;5;1;4])   = 2.
      count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
   ------------------------------------------------------------------ *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil     => nil
  | t :: xs => if beq_nat t v
               then xs
               else t :: remove_one v xs
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 12. Definir la función
      remove_all : nat -> bag -> bag
   tal que (remove_all x ys) es el multiconjunto obtenido eliminando
   todas las ocurrencias de x en el multiconjunto ys. Por ejemplo,
      count 5 (remove_all 5 [2;1;5;4;1])           = 0.
      count 5 (remove_all 5 [2;1;4;1])             = 0.
      count 4 (remove_all 5 [2;1;4;5;1;4])         = 2.
      count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
   ------------------------------------------------------------------ *)

Fixpoint remove_all (v:nat) (s:bag) : bag :=
   match s with
  | nil => nil
  | t :: xs => if beq_nat t v
               then remove_all v xs
               else t :: remove_all v xs
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 13. Definir la función
      subset : bag -> bag -> bool
   tal que (subset xs ys) se verifica si xs es un sub,ulticonjunto de
   ys. Por ejemplo,
      subset [1;2]   [2;1;4;1] = true.
      subset [1;2;2] [2;1;4;1] = false.
   ------------------------------------------------------------------ *)

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil   => true
  | x::xs => member x s2 && subset xs (remove_one x s2)
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 14. Escribir un teorema sobre multiconjuntos con las funciones
   count y add y probarlo. 
   ------------------------------------------------------------------ *)

Theorem bag_theorem : forall s1 s2 : bag, forall n : nat,
  count n s1 + count n s2 = count n (app s1 s2).                 
Proof.
  intros s1 s2 n. induction s1 as [|s s'].
 - simpl. reflexivity.
 - simpl. destruct (beq_nat s n).
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

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que, para toda lista de naturales l,
      pred (length l) = length (tl l)
   ------------------------------------------------------------------ *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
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

Theorem app_assoc : forall l1 l2 l3 : natlist,
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
      rev : natlist -> natlist
   tal que (rev xs) es la inversa de xs. Por ejemplo,
      rev [1;2;3] = [3;2;1].
      rev nil     = nil.
   ------------------------------------------------------------------ *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§§ Propiedaes de la función rev  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      length (rev l) = length l
   ------------------------------------------------------------------ *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
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

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* Ahora completamos la prueba original. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
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

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| x xs HI].
  - reflexivity.
  - simpl. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 16. Demostrar que rev es un endomorfismo en (natlist,++)
   ------------------------------------------------------------------ *)
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|x xs HI].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite HI, app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 17. Demostrar que rev es involutiva.
   ------------------------------------------------------------------ *)

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [|x xs HI].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 18. Demostrar que
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
   ------------------------------------------------------------------ *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 19. Demostrar que al concatenar dos listas no aparecen ni
   desaparecen ceros. 
   ------------------------------------------------------------------ *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [|x xs HI].
  - reflexivity.
  - simpl. destruct x.
    + rewrite HI. reflexivity.
    + simpl. rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 20. Definir la función
      beq_natlist : natlist -> natlist -> bool
   tal que (beq_natlist xs ys) se verifica si las listas xs e ys son
   iguales. Por ejemplo,
      beq_natlist nil nil         = true.
      beq_natlist [1;2;3] [1;2;3] = true.
      beq_natlist [1;2;3] [1;2;4] = false. 
   ------------------------------------------------------------------ *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool:=
  match l1, l2 with
  | nil,   nil   => true
  | x::xs, y::ys => beq_nat x y && beq_natlist xs ys
  | _, _         => false
 end.

Example test_beq_natlist1: (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2: beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3: beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 21. Demostrar que la igualdad de listas cumple la propiedad
   reflexiva. 
   ------------------------------------------------------------------ *)

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  induction l as [|n xs HI].
  - reflexivity.
  - simpl. rewrite <- HI. replace (beq_nat n n) with true.  reflexivity.
    + rewrite <- beq_nat_refl. reflexivity.
Qed.

(* =====================================================================
   §§ Ejercicios: 1ª parte 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 22. Demostrar que al incluir un elemento en un multiconjunto,
   ese elemento aparece al menos una vez en el resultado.
   ------------------------------------------------------------------ *)

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
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

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  induction s as [|x xs HI].
  - reflexivity.
  - simpl. destruct x.
    + rewrite ble_n_Sn. reflexivity.
    + simpl. rewrite HI. reflexivity.
Qed.    

(* ---------------------------------------------------------------------
   Ejercicio 25. Escribir un teorema con las funciones count y sum de los
   multiconjuntos. 
   ------------------------------------------------------------------ *)

Theorem bag_count_sum: forall n : nat, forall b1 b2 : bag,
  count n b1 + count n b2 = count n (sum b1 b2).
Proof.
  intros n b1 b2. induction b1 as [|b bs HI].
  - reflexivity.
  - simpl. destruct (beq_nat b n).
    + simpl. rewrite HI. reflexivity.
    + rewrite HI. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 26. Demostrar que la función rev es inyectiva; es decir,
      forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
   ------------------------------------------------------------------ *)

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. rewrite <- rev_involutive, <- H, rev_involutive. reflexivity.
Qed.

(* =====================================================================
   § 4. Opcionales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      nth_bad : natlist -> n -> nat
   tal que (nth_bad xs n) es el n-ésimo elemento de la lista xs y 42 si
   la lista tiene menos de n elementos. 
   ------------------------------------------------------------------ *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil     => 42  (* un valor arbitrario *)
  | a :: l' => match beq_nat n O with
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
      nth_error : natlist -> nat -> natoption
   tal que (nth_error xs n) es el n-ésimo elemento de la lista xs o None
   si la lista tiene menos de n elementos. Por ejemplo,
      nth_error [4;5;6;7] 0 = Some 4.
      nth_error [4;5;6;7] 3 = Some 7.
      nth_error [4;5;6;7] 9 = None.
   ------------------------------------------------------------------ *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil     => None
  | a :: l' => match beq_nat n O with
               | true  => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Introduciendo condicionales nos queda: *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O
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
      hd_error : natlist -> natoption
   tal que (hd_error xs) es el primer elemento de xs, si xs es no vacía;
   o es None, en caso contrario. Por ejemplo,
      hd_error []    = None.
      hd_error [1]   = Some 1.
      hd_error [5;6] = Some 5.
   ------------------------------------------------------------------ *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil   => None
  | x::xs => Some x
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 28. Demostrar que
      hd default l = option_elim default (hd_error l).
   ------------------------------------------------------------------ *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
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
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(* ---------------------------------------------------------------------
   Ejercicio 29. Demostrar que beq_id es reflexiva.
   ------------------------------------------------------------------ *)

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intro x. destruct x. simpl. rewrite <- beq_nat_refl. reflexivity.
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
  - simpl. destruct x. simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl. destruct x. simpl. rewrite <- beq_nat_refl. reflexivity.
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
