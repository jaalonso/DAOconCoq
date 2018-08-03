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
      inversa (l1 ++ l2) = inversa l2 ++ inversa l1.
   ------------------------------------------------------------------ *)

Theorem inversa_conc_distr: forall X (l1 l2 : list X),
  inversa (l1 ++ l2) = inversa l2 ++ inversa l1.
Proof.
  intros X l1 l2.
  induction l1.
  + simpl. rewrite conc_nil. reflexivity.
  + simpl. rewrite IHl1, conc_asociativa. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      inversa (inversa l) = l.
   ------------------------------------------------------------------ *)

Theorem inversa_involutive : forall X : Type, forall l : list X,
  inversa (inversa l) = l.
Proof.
  induction l.
  + reflexivity.
  + simpl. rewrite inversa_conc_distr, IHl. reflexivity.
Qed.

(* =====================================================================
   §§ 1.2. Polimorfismo de pares  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo prod (X Y) con el constructor pair tal que 
   (pair x y) es el par cuyas componentes son x e y.
   ------------------------------------------------------------------ *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la abinversaiatura
      "( x , y )" para (pair x y).
   ------------------------------------------------------------------ *)

Notation "( x , y )" := (pair x y).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la abinversaiatura
      "X * Y" para (prod X Y) 
   ------------------------------------------------------------------ *)

Notation "X * Y" := (prod X Y) : type_scope.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      fst {X Y : Type} (p : X * Y) : X
   tal que (fst p) es la primera componente del par p.
   ------------------------------------------------------------------ *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      snd {X Y : Type} (p : X * Y) 
   tal que (snd p) es la segunda componente del par p.
   ------------------------------------------------------------------ *)

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) 
   tal que (combine lx ly) es la lista obtenida emparejando los
   elementos de lx y ly (como zip de Haskell).
   ------------------------------------------------------------------ *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | []     , _       => []
  | _      , []      => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el resultado de 
      Check combine
   ------------------------------------------------------------------ *)

Check @combine.
(* ==> forall X Y : Type, list X -> list Y -> list (X * Y)*)

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el resultado de 
      Compute (combine [1;2] [false;false;true;true]).
   ------------------------------------------------------------------ *)

Compute (combine [1;2] [false;false;true;true]).
(* ==> [(1, false); (2, false)] : list (nat * bool) *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y)
   tal que (split l) es el par de lista (lx,ly) cuyo emparejamiento es
   l. (La función split es como unzip de Haskell). Por ejemplo,
      split [(1,false);(2,false)] = ([1;2],[false;false]).
   ------------------------------------------------------------------ *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
 match l with
 | []          => ([], [])
 | (x, y) :: t => let s := split t in (x :: fst s, y :: snd s)
end.

Example prop_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 1.3. Resultados opcionales polimórficos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo (option X) con los constructores Some y None
   tales que 
   + (Some x) es un valor de tipo X.
   + None es el valor nulo.
   ------------------------------------------------------------------ *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      nth_error {X : Type} (l : list X) (n : nat) : option X :=
   tal que (nth_error l n) es el n-ésimo elemento de l. Por ejemplo, 
      nth_error [4;5;6;7] 0 = Some 4.
      nth_error [[1];[2]] 1 = Some [2].
      nth_error [true] 2    = None.
   ------------------------------------------------------------------ *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | []      => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example prop_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example prop_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example prop_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      hd_error {X : Type} (l : list X) : option X
   tal que (hd_error l) es el primer elemento de l. Por ejemplo,
      hd_error [1;2]     = Some 1.
      hd_error [[1];[2]] = Some [1].
   ------------------------------------------------------------------ *)

Definition hd_error {X : Type} (l : list X) : option X :=
 match l with 
    | []     => None
    | x :: _ => Some x
 end.

Check @hd_error.

Example prop_hd_error1 : hd_error [1;2] = Some 1.
 Proof. reflexivity. Qed.
Example prop_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 Proof. reflexivity. Qed.

(* =====================================================================
   § 2. Funciones como datos
   ================================================================== *)

(* =====================================================================
   §§ 2.1. Funciones de orden superior 
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función 
      doit3times {X:Type} (f:X->X) (n:X) : X 
   tal que (doit3times f) aplica 3 veces la función f. Por ejemplo,
      doit3times minustwo 9 = 3.
      doit3times negb true  = false.
   ------------------------------------------------------------------ *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example prop_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.
Example prop_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.2. Filtrado  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      filter {X:Type} (test: X->bool) (l:list X) : (list X)
   tal que (filter p l) es la lista de los elementos de l que verifican
   p. Por ejemplo,
      filter evenb [1;2;3;4] = [2;4].
   ------------------------------------------------------------------ *)


Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                       else       filter test t
  end.

Example prop_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition longitud_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (longitud l) 1.

Example prop_filter2:
    filter longitud_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      countoddmembers' (l:list nat) : nat 
   tal que countoddmembers' l) es el número de elementos impares de
   l. Por ejemplo,
      countoddmembers' [1;0;3;1;4;5] = 4.
      countoddmembers' [0;2;4]       = 0.
      countoddmembers' nil           = 0.
   ------------------------------------------------------------------ *)

Definition countoddmembers' (l:list nat) : nat :=
  longitud (filter oddb l).

Example prop_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example prop_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example prop_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ 2.3. Funciones anónimas  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      doit3times (fun n => n * n) 2 = 256.
   ------------------------------------------------------------------ *)

Example prop_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Calcular
      filter (fun l => beq_nat (longitud l) 1)
             [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
   ------------------------------------------------------------------ *)

Example prop_filter2':
    filter (fun l => beq_nat (longitud l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      filter_even_gt7 (l : list nat) : list nat
   tal que (filter_even_gt7 l) es la lista de los elemntos de l que son
   pares y mayores que 7. Por ejemplo,
      filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
      filter_even_gt7 [5;2;6;19;129]      = [].
   ------------------------------------------------------------------ *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => evenb x && leb 7 x) l.

Example prop_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 Proof. reflexivity. Qed.

Example prop_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X
   tal que (patition p l) es el par de lista (lx,ly) tal que lx es la
   lista de los elementos de l que cumplen p y ly la de las que no lo
   cumplen. Por ejemplo,
      partition oddb [1;2;3;4;5]         = ([1;3;5], [2;4]).
      partition (fun x => false) [5;9;0] = ([], [5;9;0]).
   ------------------------------------------------------------------ *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example prop_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example prop_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.4. Aplicación a todos los elementos (map)
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      map {X Y:Type} (f:X->Y) (l:list X) : (list Y) 
   tal que (map f l) es la lista obtenida aplicando f a todos los
   elementos de l. Por ejemplo,
      map (fun x => plus 3 x) [2;0;2] = [5;3;5].
      map oddb [2;1;2;5] = [false;true;false;true].
      map (fun n => [evenb n;oddb n]) [2;1;2;5]
        = [[true;false];[false;true];[true;false];[false;true]].
   ------------------------------------------------------------------ *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example prop_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

Example prop_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

Example prop_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      map f (inversa l) = inversa (map f l).
   ------------------------------------------------------------------ *)

Lemma map_conc_distr : forall (X Y : Type) (f : X -> Y) (l t : list X),
    map f (l ++ t) = map f l ++ map f t.
Proof.
  intros X Y f l t.
  induction l.
  + reflexivity.
  + simpl. rewrite IHl. reflexivity.
Qed.

Theorem map_inversa : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (inversa l) = inversa (map f l).
Proof.
  intros X Y f l.
  induction l.
  + reflexivity.
  + simpl. rewrite map_conc_distr, IHl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y)
   tal que (flat_map f l) es la concatenación de las listas obtenidas
   aplicando f a l. Por ejemplo,
      flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
   ------------------------------------------------------------------ *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) 
                   : (list Y) :=
   match l with
  | [] => []
  | x :: t => f x ++ flat_map f t
  end.

Example prop_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y
   tal que (option_map f xo) es la aplicación de f a xo.
   ------------------------------------------------------------------ *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None   => None
    | Some x => Some (f x)
  end.

(* =====================================================================
   §§ 2.5. Plegados (fold)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y
   tal que (fold f l b) es el plegado de l con la operación f a partir
   del elemento b. Por ejemplo,
      fold mult [1;2;3;4] 1                 = 24.
      fold andb [true;true;false;true] true = false.
      fold conc  [[1];[];[2;3];[4]] []       = [1;2;3;4].
   ------------------------------------------------------------------ *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold conc  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* =====================================================================
   §§ 2.6. Funciones que construyen funciones  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      constfun {X: Type} (x: X) : nat->X
   tal que (constfun x) es la función que a todos los naturales le
   asigna el x. Por ejemplo, si se define 
      Definition ftrue := constfun true.
   entonces,
      ftrue 0         = true.
      (constfun 5) 99 = 5.
   ------------------------------------------------------------------ *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de plus.
   ------------------------------------------------------------------ *)

Check plus.
(* ==> nat -> nat -> nat *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      plus3 : nat -> nat
   tal que (plus3 x) es tres más x. Por ejemplo,
      plus3 4               = 7.
      doit3times plus3 0    = 9.
      doit3times (plus 3) 0 = 9.
   ------------------------------------------------------------------ *)

Definition plus3 := plus 3.

Example prop_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example prop_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example prop_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* =====================================================================
   § 3. Ejercicios 
   ================================================================== *)

Module Exercises.

(* ---------------------------------------------------------------------
   Ejercicio. Definir, usando fold, la función
      fold_longitud {X : Type} (l : list X) : nat
   tal que (fold_longitud l) es la longitud de l. Por ejemplo,
      fold_longitud [4;7;0] = 3.
   ------------------------------------------------------------------ *)
  
Definition fold_longitud {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example prop_fold_longitud1 : fold_longitud [4;7;0] = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      fold_longitud l = longitud l.
   ------------------------------------------------------------------ *)

Theorem fold_longitud_correct : forall X (l : list X),
  fold_longitud l = longitud l.
Proof.
  intros X l.
  unfold fold_longitud.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir, usando fold, la función
      fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y
   tal que (fold_map f l) es la lista obtenida aplicando f a los
   elementos de l.
   ------------------------------------------------------------------ *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
   fold (fun x t => (f x) :: t)  l [].


(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que fold_map es equivalente a map.
   ------------------------------------------------------------------ *)

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
     fold_map f l = map f l.
Proof.
  intros X Y f l.
  unfold fold_map.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z
   tal que (prod_curry f x y) es la versión curryficada de f.
   ------------------------------------------------------------------ *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z
   tal que (prod_uncurry f p) es la versión incurryficada de f.
   ------------------------------------------------------------------ *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      prod_curry (prod_uncurry f) x y = f x y
   ------------------------------------------------------------------ *)

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      prod_uncurry (prod_curry f) p = f p.
   ------------------------------------------------------------------ *)

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      forall X n l, longitud l = n -> @nth_error X l n = None
   ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
   Ejercicio. En los siguientes ejercicios se trabajará con la
   definición de Church de los números naturales: el número natural n es
   la función que toma como argumento una función f y devuelve como
   valor la aplicación de n veces la función f. 
   ------------------------------------------------------------------ *)

Module Church.

(* ---------------------------------------------------------------------
   Ejercicio. Definir el tipo nat para los números naturales de Church. 
   ------------------------------------------------------------------ *)
  
Definition nat := forall X : Type, (X -> X) -> X -> X.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      one : nat
   tal que one es el número uno de Church.
   ------------------------------------------------------------------ *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      two : nat
   tal que two es el número dos de Church.
   ------------------------------------------------------------------ *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      zero : nat
   tal que zero es el número cero de Church.
   ------------------------------------------------------------------ *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      three : nat
   tal que three es el número tres de Church.
   ------------------------------------------------------------------ *)

Definition three : nat := @doit3times.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      succ (n : nat) : nat
   tal que (succ n) es el siguiente del número n de Church. Por ejemplo, 
      succ zero = one.
      succ one  = two.
      succ two  = three.
   ------------------------------------------------------------------ *)

Definition succ (n : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      plus (n m : nat) : nat
   tal que (plus n m) es la suma de n y m. Por ejemplo,
      plus zero one             = one.
      plus two three            = plus three two.
      plus (plus two two) three = plus one (plus three three).
   ------------------------------------------------------------------ *)

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      mult (n m : nat) : nat
   tal que (mult n m) es el producto de n y m. Por ejemplo,
      mult one one = one.
      mult zero (plus three three) = zero.
      mult two three = plus three three.
   ------------------------------------------------------------------ *)

Definition mult (n m : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      exp (n m : nat) : nat
   tal que (exp n m) es la potencia m-ésima de n. Por ejemplo, 
      exp two two = plus two two.
      exp three two = plus (mult two (mult two two)) one.
      exp three zero = one.
   ------------------------------------------------------------------ *)

Definition exp (n m : nat) : nat :=
  ( fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x).

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.

End Exercises.
