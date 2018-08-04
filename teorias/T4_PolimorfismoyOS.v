(* T4: Polimorfismo y funciones de orden superior en Coq *)

Require Export T3_Listas.

(* =====================================================================
   § 1. Polimorfismo
   ================================================================== *)

(* =====================================================================
   §§ 1.1. Listas polimórficas  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Nota. Se suprime algunos avisos.
   ------------------------------------------------------------------ *)

Set Warnings "-notation-overridden,-parsing".

(* ---------------------------------------------------------------------
   Ejemplo 1.1.1. Definir el tipo (list X) para representar las listas
   de elementos de tipo X con los constructores nil y cons tales que 
   + nil es la lista vacía y
   + (cons x ys) es la lista obtenida añadiendo el elemento x a la
     lista ys.
   ------------------------------------------------------------------ *)

Inductive list (X:Type) : Type :=
  | nil  : list X
  | cons : X -> list X -> list X.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.2. Calcular el tipo de list.
   ------------------------------------------------------------------ *)

Check list.
(* ===> list : Type -> Type *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.3. Calcular el tipo de (nil nat).
   ------------------------------------------------------------------ *)

Check (nil nat).
(* ===> nil nat : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.4. Calcular el tipo de (cons nat 3 (nil nat)).
   ------------------------------------------------------------------ *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.5. Calcular el tipo de nil.
   ------------------------------------------------------------------ *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.6. Calcular el tipo de cons.
   ------------------------------------------------------------------ *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.7. Calcular el tipo de 
      (cons nat 2 (cons nat 1 (nil nat))).
   ------------------------------------------------------------------ *)

Check (cons nat 2 (cons nat 1 (nil nat))).
(* ==> cons nat 2 (cons nat 1 (nil nat)) : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.8. Definir la función
      repite (X : Type) (x : X) (n : nat) : list X
   tal que (repite X x n) es la lista, de elementos de tipo X, obtenida
   repitiendo n veces el elemento x. Por ejemplo,
      repite nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repite bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repite (X : Type) (x : X) (n : nat) : list X :=
  match n with
  | 0    => nil X
  | S n' => cons X x (repite X x n')
  end.

Example prop_repite1 :
  repite nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

Example prop_repite2 :
  repite bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.

(* =====================================================================
   §§§ 1.1.1. Inferencia de tipos
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.9. Definir la función
      repite' X x n : list X
   tal que (repite' X x n) es la lista obtenida repitiendo n veces el
   elemento x. Por ejemplo,
      repite' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repite' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repite' X x n : list X :=
  match n with
  | 0    => nil X
  | S n' => cons X x (repite' X x n')
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.10. Calcular los tipos de repite' y repite.
   ------------------------------------------------------------------ *)

Check repite'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repite.
(* ===> forall X : Type, X -> nat -> list X *)

(* =====================================================================
   §§§ 1.1.2. Síntesis de los tipos de los argumentos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.11. Definir la función
      repite'' X x n : list X
   tal que (repite'' X x n) es la lista obtenida repitiendo n veces el
   elemento x, usando argumentos implícitos. Por ejemplo,
      repite'' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repite'' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repite'' X x n : list X :=
  match n with
  | 0    => nil _
  | S n' => cons _ x (repite'' _ x n')
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.12. Definir la lista formada por los números naturales 1,
   2 y 3. 
   ------------------------------------------------------------------ *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* =====================================================================
   §§§ 1.1.3. Argumentos implícitos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.13. Especificar las siguientes funciones y sus argumentos
   explícitos e implícitos:
   + nil
   + constructor
   + repite
   ------------------------------------------------------------------ *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repite {X} x n.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.14. Definir la lista formada por los números naturales 1,
   2 y 3. 
   ------------------------------------------------------------------ *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* ---------------------------------------------------------------------
   Ejemplo 1.1.15. Definir la función
      repite''' {X : Type} (x : X) (n : nat) : list X
   tal que (repite'' X x n) es la lista obtenida repitiendo n veces el
   elemento x, usando argumentos implícitos. Por ejemplo,
      repite'' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repite'' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repite''' {X : Type} (x : X) (n : nat) : list X :=
  match n with
  | 0    => nil
  | S n' => cons x (repite''' x n')
  end.

Example prop_repite'''1 :
  repite''' 4 2 = cons 4 (cons 4 nil).
Proof. reflexivity.  Qed.

Example prop_repite'''2 :
  repite false 1 = cons false nil.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.16. Definir el tipo (list' {X}) para representar las
   listas de elementos de tipo X con los constructores nil' y cons'
   tales que  
   + nil' es la lista vacía y
   + (cons' x ys) es la lista obtenida añadiendo el elemento x a la
     lista ys.
   ------------------------------------------------------------------ *)

Inductive list' {X:Type} : Type :=
  | nil'  : list'
  | cons' : X -> list' -> list'.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.17. Definir la función
      conc {X : Type} (xs ys : list X) : (list X)
   tal que (conc xs ys) es la concatenación de xs e ys.
   ------------------------------------------------------------------ *)

Fixpoint conc {X : Type} (xs ys : list X) : (list X) :=
  match xs with
  | nil        => ys
  | cons x xs' => cons x (conc xs' ys)
  end.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.18. Definir la función
      inversa {X:Type} (l:list X) : list X
   tal que (inversa xs) es la inversa de xs. Por ejemplo,
      inversa (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
      inversa (cons true nil)       = cons true nil.
   ------------------------------------------------------------------ *)

Fixpoint inversa {X:Type} (xs:list X) : list X :=
  match xs with
  | nil        => nil
  | cons x xs' => conc (inversa xs') (cons x nil)
  end.

Example prop_inversa1 :
  inversa (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example prop_inversa2:
  inversa (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.19. Definir la función
      longitud {X : Type} (xs : list X) : nat 
   tal que (longitud xs) es el número de elementos de xs. Por ejemplo,
      longitud (cons 1 (cons 2 (cons 3 nil))) = 3.
   ------------------------------------------------------------------ *)

Fixpoint longitud {X : Type} (xs : list X) : nat :=
  match xs with
  | nil        => 0
  | cons _ xs' => S (longitud xs')
  end.

Example prop_longitud1:
  longitud (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§§ 1.1.4. Explicitación de argumentos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.20. Evaluar la siguiente expresión
      Fail Definition n_nil := nil.
   ------------------------------------------------------------------ *)

Fail Definition n_nil := nil.
(* ==> Error: Cannot infer the implicit parameter X of nil. *)

(* ---------------------------------------------------------------------
   Ejemplo 1.1.21. Completar la definición anterior para obtener la
   lista vacía de números naturales.
   ------------------------------------------------------------------ *)

(* 1ª solución *)
Definition n_nil : list nat := nil.

(* 2ª solución *)
Definition n_nil' := @nil nat.

(* ---------------------------------------------------------------------
   Ejemplo 1.1.22. Definir las siguientes abreviaturas
   + "x :: y"         para (cons x y)
   + "[ ]"            para nil
   + "[ x ; .. ; y ]" para (cons x .. (cons y []) ..).
   + "x ++ y"         para (conc x y)
   ------------------------------------------------------------------ *)

Notation "x :: y"         := (cons x y)
                             (at level 60, right associativity).
Notation "[ ]"            := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y"         := (conc x y)
                              (at level 60, right associativity).

(* ---------------------------------------------------------------------
   Ejemplo 1.1.23. Definir la lista cuyos elementos son 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition list123''' := [1; 2; 3].

(* =====================================================================
   §§§ 1.1.5. Ejercicios  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 1.1.1. Demostrar que la lista vacía es el elemento neutro
   por la derecha de la concatenación.
   ------------------------------------------------------------------ *)

Theorem conc_nil: forall (X:Type), forall xs:list X,
  xs ++ [] = xs.
Proof.
  induction xs as [|x xs' HI]. 
  -                            (* X : Type
                                  ============================
                                  [ ] ++ [ ] = [ ] *)
    reflexivity.
  -                            (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : xs' ++ [ ] = xs'
                                  ============================
                                  (x :: xs') ++ [ ] = x :: xs' *)
    simpl.                     (* x :: (xs' ++ [ ]) = x :: xs' *)
    rewrite HI.                (* x :: xs' = x :: xs' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1.2. Demostrar que la concatenación es asociativa.
   ------------------------------------------------------------------ *)

Theorem conc_asociativa : forall A (xs ys zs:list A),
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  intros A xs ys zs.           (* A : Type
                                  xs, ys, zs : list A
                                  ============================
                                  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs *)
  induction xs as [|x xs' HI]. 
  +                            (* A : Type
                                  ys, zs : list A
                                  ============================
                                  [ ] ++ (ys ++ zs) = ([ ] ++ ys) ++ zs *)
    reflexivity.
  +                            (* A : Type
                                  x : A
                                  xs', ys, zs : list A
                                  HI : xs' ++ (ys ++ zs) = (xs' ++ ys) ++ zs
                                  ============================
                                  (x :: xs') ++ (ys ++ zs) = 
                                  ((x :: xs') ++ ys) ++ zs *)
    simpl.                     (* x :: (xs' ++ (ys ++ zs)) = 
                                  x :: ((xs' ++ ys) ++ zs) *)
    rewrite HI.                (* x :: ((xs' ++ ys) ++ zs) = 
                                  x :: ((xs' ++ ys) ++ zs) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1.3. Demostrar que la longitud de una concatenación es la
   suma de las longitudes de las listas (es decir, es un homomorfismo).
   ------------------------------------------------------------------ *)

Lemma conc_longitud: forall (X:Type) (xs ys : list X),
  longitud (xs ++ ys) = longitud xs + longitud ys.
Proof.
  intros X xs ys.              (* X : Type
                                  xs, ys : list X
                                  ============================
                                  longitud (xs ++ ys) = 
                                  longitud xs + longitud ys *)
  induction xs as [|x xs' HI]. 
  +                            (* X : Type
                                  ys : list X
                                  ============================
                                  longitud ([ ] ++ ys) = 
                                  longitud [ ] + longitud ys *)
    reflexivity.
  +                            (* X : Type
                                  x : X
                                  xs', ys : list X
                                  HI : longitud (xs' ++ ys) = 
                                       longitud xs' + longitud ys
                                  ============================
                                  longitud ((x :: xs') ++ ys) = 
                                  longitud (x :: xs') + longitud ys *)
    simpl.                     (* S (longitud (xs' ++ ys)) = 
                                  S (longitud xs' + longitud ys) *)
    rewrite HI.                (* S (longitud xs' + longitud ys) = 
                                  S (longitud xs' + longitud ys) *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1.4. Demostrar que
      inversa (xs ++ ys) = inversa ys ++ inversa xs.
   ------------------------------------------------------------------ *)

Theorem inversa_conc: forall X (xs ys : list X),
  inversa (xs ++ ys) = inversa ys ++ inversa xs.
Proof.
  intros X xs ys.              (* X : Type
                                  xs, ys : list X
                                  ============================
                                  inversa (xs ++ ys) = 
                                  inversa ys ++ inversa xs *)
  induction xs as [|x xs' HI]. 
  -                            (* X : Type
                                  ys : list X
                                  ============================
                                  inversa ([ ] ++ ys) = 
                                  inversa ys ++ inversa [ ] *)
    simpl.
    rewrite conc_nil.
    reflexivity.
  -                            (* X : Type
                                  x : X
                                  xs', ys : list X
                                  HI : inversa (xs' ++ ys) = 
                                       inversa ys ++ inversa xs'
                                  ============================
                                  inversa ((x :: xs') ++ ys) = 
                                  inversa ys ++ inversa (x :: xs') *)
    simpl.                     (* inversa (xs' ++ ys) ++ [x] = 
                                  inversa ys ++ (inversa xs' ++ [x]) *)
    rewrite HI.                (* (inversa ys ++ inversa xs') ++ [x] = 
                                  inversa ys ++ (inversa xs' ++ [x]) *)
    rewrite conc_asociativa.   (* (inversa ys ++ inversa xs') ++ [x] = 
                                  (inversa ys ++ inversa xs') ++ [x] *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.1.5. Demostrar que la inversa es involutiva; es decir,
      inversa (inversa xs) = xs.
   ------------------------------------------------------------------ *)

Theorem inversa_involutiva : forall X : Type, forall xs : list X,
  inversa (inversa xs) = xs.
Proof.
  intros X xs.                 (* X : Type
                                  xs : list X
                                  ============================
                                  inversa (inversa xs) = xs *)
  induction xs as [|x xs' HI]. 
  +                            (* X : Type
                                  ============================
                                  inversa (inversa [ ]) = [ ] *)
    reflexivity.
  +                            (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : inversa (inversa xs') = xs'
                                  ============================
                                  inversa (inversa (x :: xs')) = x :: xs' *)
    simpl.                     (* inversa (inversa xs' ++ [x]) = x :: xs' *)
    rewrite inversa_conc.      (* inversa [x] ++ inversa (inversa xs') = 
                                  x :: xs' *)
    rewrite HI.                (* inversa [x] ++ xs' = x :: xs' *)
    reflexivity.
Qed.

(* =====================================================================
   §§ 1.2. Polimorfismo de pares  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.2.1. Definir el tipo prod (X Y) con el constructor par tal
   que (par x y) es el par cuyas componentes son x e y.
   ------------------------------------------------------------------ *)

Inductive prod (X Y : Type) : Type :=
  | par : X -> Y -> prod X Y.

Arguments par {X} {Y} _ _.

(* ---------------------------------------------------------------------
   Ejemplo 1.2.2. Definir la abreviaturas
      "( x , y )" para (par x y).
   ------------------------------------------------------------------ *)

Notation "( x , y )" := (par x y).

(* ---------------------------------------------------------------------
   Ejemplo 1.2.3. Definir la abreviatura
      "X * Y" para (prod X Y) 
   ------------------------------------------------------------------ *)

Notation "X * Y" := (prod X Y) : type_scope.

(* ---------------------------------------------------------------------
   Ejemplo 1.2.4. Definir la función
      fst {X Y : Type} (p : X * Y) : X
   tal que (fst p) es la primera componente del par p. Por ejemplo,
      fst (par 3 5) = 3
   ------------------------------------------------------------------ *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Compute (fst (par 3 5)).
(* = 3 : nat*)

Example prop_fst: fst (par 3 5) = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.2.5. Definir la función
      snd {X Y : Type} (p : X * Y) 
   tal que (snd p) es la segunda componente del par p. Por ejemplo,
      snd (par 3 5) = 5 
   ------------------------------------------------------------------ *)

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Compute (snd (par 3 5)).
(* = 5 : nat*)

Example prop_snd: snd (par 3 5) = 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.1. Definir la función
      empareja {X Y : Type} (xs : list X) (ys : list Y) : list (X*Y) 
   tal que (empareja xs ys) es la lista obtenida emparejando los
   elementos de xs y ys. Por ejemplo,
      empareja [2;6] [3;5;7]     = [(2, 3); (6, 5)].
      empareja [2;6;4;8] [3;5;7] = [(2, 3); (6, 5); (4, 7)].
   ------------------------------------------------------------------ *)

Fixpoint empareja {X Y : Type} (xs : list X) (ys : list Y) : list (X*Y) :=
  match xs, ys with
  | []     , _       => []
  | _      , []      => []
  | x :: tx, y :: ty => (x, y) :: (empareja tx ty)
  end.

Compute (empareja [2;6] [3;5;7]).
(* = [(2, 3); (6, 5)] : list (nat * nat)*)
Compute (empareja [2;6;4;8] [3;5;7]).
(* = [(2, 3); (6, 5); (4, 7)] : list (nat * nat)*)

Example prop_combina1: empareja [2;6] [3;5;7] = [(2, 3); (6, 5)].
Proof. reflexivity. Qed.

Example prop_combina2: empareja [2;6;4;8] [3;5;7] = [(2,3);(6, 5);(4,7)].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.2. Evaluar la expresión
      Check @empareja
   ------------------------------------------------------------------ *)

Check @empareja.
(* ==> forall X Y : Type, list X -> list Y -> list (X * Y)*)

(* ---------------------------------------------------------------------
   Ejercicio 2.2.3. Definir la función
      desempareja {X Y : Type} (ps : list (X*Y)) : (list X) * (list Y)
   tal que (desempareja ps) es el par de lista (xs,ys) cuyo
   emparejamiento es l. Por ejemplo,
      desempareja [(1,false);(2,false)] = ([1;2],[false;false]).
   ------------------------------------------------------------------ *)

Fixpoint desempareja {X Y:Type} (ps:list (X*Y)) : (list X) * (list Y) :=
  match ps with
  | []            => ([], [])
  | (x, y) :: ps' => let ps'' := desempareja ps'
                    in (x :: fst ps'', y :: snd ps'')
end.

Compute (desempareja [(2, 3); (6, 5)]).
(* = ([2; 6], [3; 5]) : list nat * list nat*)

Example prop_desempareja:
  desempareja [(2, 3); (6, 5)] = ([2; 6], [3; 5]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 1.3. Resultados opcionales polimórficos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 1.3.1. Definir el tipo (Opcional X) con los constructores Some
   y None tales que 
   + (Some x) es un valor de tipo X.
   + None es el valor nulo.
   ------------------------------------------------------------------ *)

Inductive Opcional (X:Type) : Type :=
  | Some : X -> Opcional X
  | None : Opcional X.

Arguments Some {X} _.
Arguments None {X}.

(* ---------------------------------------------------------------------
   Ejercicio 1.3.1. Definir la función
      nthOpcional {X : Type} (xs : list X) (n : nat) : Opcional X :=
   tal que (nthOpcional xs n) es el n-ésimo elemento de xs o None
   si la lista tiene menos de n elementos. Por ejemplo, 
      nthOpcional [4;5;6;7] 0 = Some 4.
      nthOpcional [[1];[2]] 1 = Some [2].
      nthOpcional [true] 2    = None.
   ------------------------------------------------------------------ *)

Fixpoint nthOpcional {X : Type} (xs : list X) (n : nat) : Opcional X :=
  match xs with
  | []       => None
  | x :: xs' => if iguales_nat n O
               then Some x
               else nthOpcional xs' (pred n)
  end.

Example prop_nthOpcional1 : nthOpcional [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example prop_nthOpcional2 : nthOpcional [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.

Example prop_nthOpcional3 : nthOpcional [true] 2 = None.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 1.3.2. Definir la función
      primeroOpcional {X : Type} (xs : list X) : Opcional X
   tal que (primeroOpcional xs) es el primer elemento de xs, si xs es no
   vacía; o es None, en caso contrario. Por ejemplo,
      primeroOpcional [1;2]     = Some 1.
      primeroOpcional [[1];[2]] = Some [1].
   ------------------------------------------------------------------ *)

Definition primeroOpcional {X : Type} (xs : list X) : Opcional X :=
 match xs with 
    | []     => None
    | x :: _ => Some x
 end.

Check @primeroOpcional.

Example prop_primeroOpcional1 : primeroOpcional [1;2] = Some 1.
Proof. reflexivity. Qed.

Example prop_primeroOpcional2 : primeroOpcional  [[1];[2]]  = Some [1].
 Proof. reflexivity. Qed.

(* =====================================================================
   § 2. Funciones como datos
   ================================================================== *)

(* =====================================================================
   §§ 2.1. Funciones de orden superior 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.1.1. Definir la función 
      aplica3veces {X : Type} (f : X -> X) (n : X) : X 
   tal que (aplica3veces f) aplica 3 veces la función f. Por ejemplo,
      aplica3veces menosDos 9     = 3.
      aplica3veces negacion true  = false.
   ------------------------------------------------------------------ *)

Definition aplica3veces {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @aplica3veces.
(* ===> aplica3veces : forall X : Type, (X -> X) -> X -> X *)

Example prop_aplica3veces: aplica3veces menosDos 9 = 3.
Proof. reflexivity.  Qed.

Example prop_aplica3veces': aplica3veces negacion true = false.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.2. Filtrado  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.2.1. Definir la función
      filtra {X : Type} (p : X -> bool) (xs : list X) : (list X)
   tal que (filtra p xs) es la lista de los elementos de xs que
   verifican p. Por ejemplo,
      filtra esPar [1;2;3;4] = [2;4].
   ------------------------------------------------------------------ *)

Fixpoint filtra {X : Type} (p : X -> bool) (xs : list X) : (list X) :=
  match xs with
  | []       => []
  | x :: xs' => if p x
               then x :: (filtra p xs')
               else filtra p xs'
  end.

Example prop_filtra1: filtra esPar [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.2.2. Definir la función
      unitarias {X : Type} (xss : list (list X)) : list (list X) :=
   tal que (unitarias xss) es la lista de listas unitarias de xss. Por
   ejemplo, 
      unitarias [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]]
   ------------------------------------------------------------------ *)

Definition esUnitaria {X : Type} (xs : list X) : bool :=
  iguales_nat (longitud xs) 1.

Definition unitarias {X : Type} (xss : list (list X)) : list (list X) :=
  filtra esUnitaria xss.
  
Compute (unitarias [[1; 2]; [3]; [4]; [5;6;7]; []; [8]]).
(* = [[3]; [4]; [8]] : list (list nat)*)

Example prop_unitarias:
  unitarias [[1; 2]; [3]; [4]; [5;6;7]; []; [8]]
  = [[3]; [4]; [8]].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.2.3. Definir la función
      nImpares (xs : list nat) : nat 
   tal que nImpares xs) es el número de elementos impares de xs. Por
   ejemplo, 
      nImpares [1;0;3;1;4;5] = 4.
      nImpares [0;2;4]       = 0.
      nImpares nil           = 0.
   ------------------------------------------------------------------ *)

Definition nImpares (xs : list nat) : nat :=
  longitud (filtra esImpar xs).

Example prop_nImpares1:   nImpares [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.

Example prop_nImpares2:   nImpares [0;2;4] = 0.
Proof. reflexivity.  Qed.

Example prop_nImpares3:   nImpares nil = 0.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.3. Funciones anónimas  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.3.1. Demostrar que
      aplica3veces (fun n => n * n) 2 = 256.
   ------------------------------------------------------------------ *)

Example prop_anon_fun':
  aplica3veces (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.3.2. Calcular
      filtra (fun xs => iguales_nat (longitud xs) 1)
             [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
   ------------------------------------------------------------------ *)

Compute (filtra (fun xs => iguales_nat (longitud xs) 1)
                [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]).
(* = [[3]; [4]; [8]] : list (list nat)*)

(* ---------------------------------------------------------------------
   Ejercicio 2.3.3. Definir la función
      filtra_pares_menores7 (xs : list nat) : list nat
   tal que (filtra_pares_mayores7 xs) es la lista de los elementos de xs
   que son pares y mayores que 7. Por ejemplo,
      filtra_pares_mayores7 [1;2;6;9;10;3;12;8] = [10;12;8].
      filtra_pares_mayores7 [5;2;6;19;129]      = [].
   ------------------------------------------------------------------ *)

Definition filtra_pares_mayores7 (xs : list nat) : list nat :=
  filtra (fun x => esPar x && menor_o_igual 7 x) xs.

Example prop_filtra_pares_mayores7_1 :
  filtra_pares_mayores7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example prop_filtra_pares_mayores7_2 :
  filtra_pares_mayores7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.3.4. Definir la función
      partition {X : Type} (p : X -> bool) (xs : list X) : list X * list X
   tal que (patition p xs) es el par de listas (ys,zs) donde xs es la
   lista de los elementos de xs que cumplen p y zs la de las que no lo
   cumplen. Por ejemplo,
      partition esImpar [1;2;3;4;5]         = ([1;3;5], [2;4]).
      partition (fun x => false) [5;9;0] = ([], [5;9;0]).
   ------------------------------------------------------------------ *)

Definition partition {X : Type}
                     (p : X -> bool)
                     (xs : list X)
                   : list X * list X :=
  (filtra p xs, filtra (fun x => negacion (p x)) xs).

Example prop_partition1: partition esImpar [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example prop_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.4. Aplicación a todos los elementos (map)
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio 2.4.1. Definir la función
      map {X Y:Type} (f : X -> Y) (xs:list X) : list Y 
   tal que (map f xs) es la lista obtenida aplicando f a todos los
   elementos de xs. Por ejemplo,
      map (fun x => plus 3 x) [2;0;2] = [5;3;5].
      map esImpar [2;1;2;5] = [false;true;false;true].
      map (fun n => [evenb n;esImpar n]) [2;1;2;5]
        = [[true;false];[false;true];[true;false];[false;true]].
   ------------------------------------------------------------------ *)

Fixpoint map {X Y:Type} (f : X -> Y) (xs : list X) : list Y :=
  match xs with
  | []       => []
  | x :: xs' => f x :: map f xs'
  end.

Example prop_map1:
  map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

Example prop_map2:
  map esImpar [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

Example prop_map3:
    map (fun n => [esPar n ; esImpar n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.4.2. Demostrar que
      map f (inversa l) = inversa (map f l).
   ------------------------------------------------------------------ *)

Lemma map_conc: forall (X Y : Type) (f : X -> Y) (xs ys : list X),
    map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  intros X Y f xs ys.          (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  xs, ys : list X
                                  ============================
                                  map f (xs ++ ys) = map f xs ++ map f ys *)
  induction xs as [|x xs' HI]. 
  +                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  ys : list X
                                  ============================
                                  map f ([ ] ++ ys) = map f [ ] ++ map f ys *)
    reflexivity.
  +                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  x : X
                                  xs', ys : list X
                                  HI : map f (xs' ++ ys) = 
                                       map f xs' ++ map f ys
                                  ============================
                                  map f ((x :: xs') ++ ys) = 
                                  map f (x :: xs') ++ map f ys *)
    simpl.                     (* f x :: map f (xs' ++ ys) = 
                                  f x :: (map f xs' ++ map f ys) *)
    rewrite HI.                (* f x :: (map f xs' ++ map f ys) = 
                                  f x :: (map f xs' ++ map f ys) *)
    reflexivity.
Qed.

Theorem map_inversa : forall (X Y : Type) (f : X -> Y) (xs : list X),
  map f (inversa xs) = inversa (map f xs).
Proof.
  intros X Y f xs.             (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  xs : list X
                                  ============================
                                  map f (inversa xs) = inversa (map f xs) *)
  induction xs as [|x xs' HI]. 
  +                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  ============================
                                  map f (inversa [ ]) = inversa (map f [ ]) *)
    reflexivity.
  +                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  x : X
                                  xs' : list X
                                  HI : map f (inversa xs') = inversa (map f xs')
                                  ============================
                                  map f (inversa (x :: xs')) = 
                                  inversa (map f (x :: xs')) *)
    simpl.                     (* map f (inversa xs' ++ [x]) = 
                                  inversa (map f xs') ++ [f x] *)
    rewrite map_conc.          (* map f (inversa xs') ++ map f [x] = 
                                  inversa (map f xs') ++ [f x] *)
    rewrite HI.                (* inversa (map f xs') ++ map f [x] = 
                                  inversa (map f xs') ++ [f x] *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.4.3. Definir la función
      conc_map {X Y : Type} (f : X -> list Y) (xs :list X) : (list Y)
   tal que (conc_map f xs) es la concatenación de las listas obtenidas
   aplicando f a l. Por ejemplo,
      conc_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
   ------------------------------------------------------------------ *)

Fixpoint conc_map {X Y : Type} (f : X -> list Y) (xs : list X) : (list Y) :=
   match xs with
  | []       => []
  | x :: xs' => f x ++ conc_map f xs'
  end.

Example prop_conc_map:
  conc_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2.4.4. Definir la función
      map_opcional {X Y : Type} (f : X -> Y) (o : Opcional X) : Opcional Y
   tal que (map_opcional f o) es la aplicación de f a o. Por ejemplo,
      map_opcional S (Some 3) = Some 4
      map_opcional S None     = None
   ------------------------------------------------------------------ *)

Definition map_opcional {X Y : Type} (f : X -> Y) (o : Opcional X)
                        : Opcional Y :=
  match o with
    | None   => None
    | Some x => Some (f x)
  end.

Compute (map_opcional S (Some 3)).
(* = Some 4 : Opcional nat*)
Compute (map_opcional S None).
(* = None : Opcional nat*)

Example prop_map_opcional1: map_opcional S (Some 3) = Some 4.
Proof. reflexivity. Qed.

Example prop_map_opcional2: map_opcional S None = None.
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.5. Plegados (fold)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.5.1. Definir la función
      fold {X Y:Type} (f: X -> Y- > Y) (xs : list X) (b : Y) : Y
   tal que (fold f xs b) es el plegado de xs con la operación f a partir
   del elemento b. Por ejemplo,
      fold mult [1;2;3;4] 1                       = 24.
      fold conjuncion [true;true;false;true] true = false.
      fold conc  [[1];[];[2;3];[4]] []            = [1;2;3;4].
   ------------------------------------------------------------------ *)

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (xs : list X) (b : Y) : Y :=
  match xs with
  | nil    => b
  | x :: xs' => f x (fold f xs' b)
  end.

Check (fold conjuncion).
(* ===> fold conjuncion : list bool -> bool -> bool *)

Example fold_example1:
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold conjuncion [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold conc  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.6. Funciones que construyen funciones  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo 2.6.1. Definir la función
      constante {X : Type} (x : X) : nat -> X
   tal que (constante x) es la función que a todos los naturales le
   asigna el x. Por ejemplo, 
      (constante 5) 99 = 5.
   ------------------------------------------------------------------ *)

Definition constante {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Example prop_constante: (constante 5) 99 = 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo 2.6.2. Calcular el tipo de plus.
   ------------------------------------------------------------------ *)

Check plus.
(* ==> nat -> nat -> nat *)

(* ---------------------------------------------------------------------
   Ejemplo 2.6.3. Definir la función
      plus3 : nat -> nat
   tal que (plus3 x) es tres más x. Por ejemplo,
      plus3 4                 = 7.
      aplica3veces plus3 0    = 9.
      aplica3veces (plus 3) 0 = 9.
   ------------------------------------------------------------------ *)

Definition plus3 := plus 3.

Example prop_plus3a: plus3 4 = 7.
Proof. reflexivity.  Qed.

Example prop_plus3b: aplica3veces plus3 0 = 9.
Proof. reflexivity.  Qed.

Example prop_plus3c: aplica3veces (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* =====================================================================
   § 3. Ejercicios 
   ================================================================== *)

Module Exercises.

(* ---------------------------------------------------------------------
   Ejercicio 3.1. Definir, usando fold, la función
      longitudF {X : Type} (xs : list X) : nat
   tal que (longitudF xs) es la longitud de xs. Por ejemplo,
      longitudF [4;7;0] = 3.
   ------------------------------------------------------------------ *)
  
Definition longitudF {X : Type} (xs : list X) : nat :=
  fold (fun _ n => S n) xs 0.

Example prop_longitudF1: longitudF [4;7;0] = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.2. Demostrar que
      longitudF l = longitud l.
   ------------------------------------------------------------------ *)

Theorem longitudF_longitud: forall X (xs : list X),
  longitudF xs = longitud xs.
Proof.
  intros X xs.                 (* X : Type
                                  xs : list X
                                  ============================
                                  longitudF xs = longitud xs *)
  unfold longitudF.            (* fold (fun (_ : X) (n : nat) => S n) xs 0 = 
                                  longitud xs *)
  induction xs as [|x xs' HI]. 
  -                            (* X : Type
                                  ============================
                                  fold (fun (_ : X) (n : nat) => S n) [ ] 0 = 
                                  longitud [ ] *)
    reflexivity.
  -                            (* X : Type
                                  x : X
                                  xs' : list X
                                  HI : fold (fun (_:X) (n:nat) => S n) xs' 0 =
                                       longitud xs'
                                  ============================
                                  fold (fun (_:X) (n:nat) => S n) (x::xs') 0 = 
                                  longitud (x :: xs') *)
    simpl.                     (* S (fold (fun (_:X) (n:nat) => S n) xs' 0) = 
                                  S (longitud xs') *)
    rewrite HI.                (* S (longitud xs') = S (longitud xs') *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.2. Definir, usando fold, la función
      mapF {X Y : Type} (f : X -> Y) (xs : list X) : list Y
   tal que (mapF f xs) es la lista obtenida aplicando f a los
   elementos de l.
   ------------------------------------------------------------------ *)

Definition mapF {X Y : Type} (f : X -> Y) (xs : list X) : list Y :=
   fold (fun x t => (f x) :: t)  xs [].

(* ---------------------------------------------------------------------
   Ejercicio 3.4. Demostrar que mapF es equivalente a map.
   ------------------------------------------------------------------ *)

Theorem mapF_correct : forall (X Y : Type) (f : X -> Y) (xs : list X),
    mapF f xs = map f xs.
Proof.
  intros X Y f xs.             (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  xs : list X
                                  ============================
                                  mapF f xs = map f xs *)
  unfold mapF.                 (* fold (fun (x:X) (t:list Y) => f x::t) xs [] 
                                  = map f xs *)
  induction xs as [|x xs' HI]. 
  -                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  ============================
                                  fold (fun (x:X) (t:list Y) => f x :: t) [] []
                                  = map f [ ] *)
    reflexivity.
  -                            (* X : Type
                                  Y : Type
                                  f : X -> Y
                                  x : X
                                  xs' : list X
                                  HI : fold (fun (x:X) (t:list Y) => f x :: t) 
                                            xs' [ ] 
                                       = map f xs'
                                  ============================
                                  fold (fun (x0:X) (t:list Y) => f x0 :: t) 
                                       (x :: xs') [ ] 
                                  = map f (x :: xs') *)
    simpl.                     (* f x :: fold (fun (x0:X) (t:list Y) => 
                                               f x0 :: t) xs' [ ] 
                                  = f x :: map f xs' *)
    rewrite HI.                (* f x :: map f xs' = f x :: map f xs' *)
    reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo 3.5. Definir la función
      curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z
   tal que (curry f x y) es la versión curryficada de f. Por ejemplo,
      curry fst 3 5 = 3.
   ------------------------------------------------------------------ *)

Definition curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Compute (curry fst 3 5).
(* = 3 : nat*)

Example prop_curry: curry fst 3 5 = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.6. Definir la función
      uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z
   tal que (uncurry f p) es la versión incurryficada de f.
   ------------------------------------------------------------------ *)

Definition uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Compute (uncurry mult (2,5)).
(* = 10 : nat*)

Example prop_uncurry: uncurry mult (2,5) = 10.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.7. Calcular el tipo de las funcciones curry y uncurry.
   ------------------------------------------------------------------ *)

Check @curry.
(* ===> forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)

Check @uncurry.
(* forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z *)

(* ---------------------------------------------------------------------
   Ejercicio 3.8. Demostrar que
      curry (uncurry f) x y = f x y
   ------------------------------------------------------------------ *)

Theorem uncurry_curry : forall (X Y Z : Type)
                          (f : X -> Y -> Z)
                          x y,
  curry (uncurry f) x y = f x y.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.9. Demostrar que
      uncurry (curry f) p = f p.
   ------------------------------------------------------------------ *)

Theorem curry_uncurry : forall (X Y Z : Type)
                          (f : (X * Y) -> Z)
                          (p : X * Y),
  uncurry (curry f) p = f p.
Proof.
  intros.      (* X : Type
                  Y : Type
                  Z : Type
                  f : X * Y -> Z
                  p : X * Y
                  ============================
                  uncurry (curry f) p = f p *)
  destruct p.  (* uncurry (curry f) (x, y) = f (x, y) *)
  reflexivity. 
Qed.

Module Church.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.1. En los siguientes ejercicios se trabajará con la
   definición de Church de los números naturales: el número natural n es
   la función que toma como argumento una función f y devuelve como
   valor la aplicación de n veces la función f. 

   Definir el tipo nat para los números naturales de Church. 
   ------------------------------------------------------------------ *)
  
Definition nat := forall X : Type, (X -> X) -> X -> X.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.2. Definir la función
      uno : nat
   tal que uno es el número uno de Church.
   ------------------------------------------------------------------ *)

Definition uno : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.3. Definir la función
      dos : nat
   tal que dos es el número dos de Church.
   ------------------------------------------------------------------ *)

Definition dos : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* ---------------------------------------------------------------------
   Ejercicio 3.11.4. Definir la función
      cero : nat
   tal que cero es el número cero de Church.
   ------------------------------------------------------------------ *)

Definition cero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.5. Definir la función
      tres : nat
   tal que tres es el número tres de Church.
   ------------------------------------------------------------------ *)

Definition tres : nat := @aplica3veces.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.5. Definir la función
      suc (n : nat) : nat
   tal que (suc n) es el siguiente del número n de Church. Por ejemplo, 
      suc cero = uno.
      suc uno  = dos.
      suc dos  = tres.
   ------------------------------------------------------------------ *)

Definition suc (n : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example prop_suc_1: suc cero = uno.
Proof. reflexivity. Qed.

Example prop_suc_2: suc uno = dos.
Proof. reflexivity. Qed.

Example prop_suc_3: suc dos = tres.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.6. Definir la función
      suma (n m : nat) : nat
   tal que (suma n m) es la suma de n y m. Por ejemplo,
      suma cero uno            = uno.
      suma dos tres            = suma tres dos.
      suma (suma dos dos) tres = suma uno (suma tres tres).
   ------------------------------------------------------------------ *)

Definition suma (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example prop_suma_1 : suma cero uno = uno.
Proof. reflexivity. Qed.

Example prop_suma_2 : suma dos tres = suma tres dos.
Proof. reflexivity. Qed.

Example prop_suma_3 :
  suma (suma dos dos) tres = suma uno (suma tres tres).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.7. Definir la función
      producto (n m : nat) : nat
   tal que (producto n m) es el producto de n y m. Por ejemplo,
      producto uno uno               = uno.
      producto cero (suma tres tres) = cero.
      producto dos tres              = suma tres tres.
   ------------------------------------------------------------------ *)

Definition producto (n m : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.

Example prop_producto_1: producto uno uno = uno.
Proof. reflexivity. Qed.

Example prop_producto_2: producto cero (suma tres tres) = cero.
Proof. reflexivity. Qed.

Example prop_producto_3: producto dos tres = suma tres tres.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio 3.11.8. Definir la función
      potencia (n m : nat) : nat
   tal que (potencia n m) es la potencia m-ésima de n. Por ejemplo, 
      potencia dos dos   = suma dos dos.
      potencia tres dos  = suma (producto dos (producto dos dos)) uno.
      potencia tres cero = uno.
   ------------------------------------------------------------------ *)

Definition potencia (n m : nat) : nat :=
  ( fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x).

Example prop_potencia_1: potencia dos dos = suma dos dos.
Proof. reflexivity. Qed.

Example prop_potencia_2:
  potencia tres dos = suma (producto dos (producto dos dos)) uno.
Proof. reflexivity. Qed.

Example prop_potencia_3: potencia tres cero = uno.
Proof. reflexivity. Qed.

End Church.

End Exercises.

(* =====================================================================
   § Bibliografía
   ================================================================== *)

(*
 + "Polymorphism and higher-order functions" de Peirce et als. 
   http://bit.ly/2Mj5gMf *)
