(* T4: Polimorfismo y funciones deo orden superior en Coq *)

Require Export T3_Listas.

(* =====================================================================
   § Polimorfismo
   ================================================================== *)

(* =====================================================================
   §§ Listas polimórficas  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo boollist para representar las listas de
   booleanos con los constructores bool_nil y bool_cons tales que 
   + bool_nil es la lista vacía y
   + (bool_cons x ys) es la lista obtenida añadiendo el booleano x a la
     lista ys.
   ------------------------------------------------------------------ *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.


(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo (list X) para representar las listas de
   elementos de con los constructores nil y cons tales que 
   + nil es la lista vacía y
   + (cons x ys) es la lista obtenida añadiendo el elemento x a la
     lista ys.
   ------------------------------------------------------------------ *)

Inductive list (X:Type) : Type :=
  | nil  : list X
  | cons : X -> list X -> list X.

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de list.
   ------------------------------------------------------------------ *)

Check list.
(* ===> list : Type -> Type *)

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de (nil nat).
   ------------------------------------------------------------------ *)

Check (nil nat).
(* ===> nil nat : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de (cons nat 3 (nil nat)).
   ------------------------------------------------------------------ *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de nil.
   ------------------------------------------------------------------ *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de cons.
   ------------------------------------------------------------------ *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(* ---------------------------------------------------------------------
   Ejemplo. Calcular el tipo de (cons nat 2 (cons nat 1 (nil nat))).
   ------------------------------------------------------------------ *)

Check (cons nat 2 (cons nat 1 (nil nat))).
(* ==> cons nat 2 (cons nat 1 (nil nat)) : list nat *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      repeat (X : Type) (x : X) (count : nat) : list X
   tal que (repeat X x n) es la lista obtenida repitiendo n veces el
   elemento x. Por ejemplo,
      repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repeat bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Se definen los siguientes tipos
      Inductive mumble : Type :=
        | a : mumble
        | b : mumble -> nat -> mumble
        | c : mumble.
      
      Inductive grumble (X:Type) : Type :=
        | d : mumble -> grumble X
        | e : X -> grumble X.
  
   Decidir cuáles de los siguientes expresiones son del tipo (grumble X)
   para algún X:
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
   ------------------------------------------------------------------ *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

End MumbleGrumble.

(* =====================================================================
   §§§ Inferencia de tipos
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      repeat' X x count : list X
   tal que (repeat' X x n) es la lista obtenida repitiendo n veces el
   elemento x. Por ejemplo,
      repeat' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repeat' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Calcular los tipos de repeat' y repeat.
   ------------------------------------------------------------------ *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(* =====================================================================
   §§§ Síntesis de los tipos de los argumentos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      repeat'' X x count : list X
   tal que (repeat'' X x n) es la lista obtenida repitiendo n veces el
   elemento x, usando argumentos implícitos. Por ejemplo,
      repeat'' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repeat'' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la lista formada por los números naturales 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* =====================================================================
   §§§ Argumentos implícitos  
   ================================================================== *)


(* ---------------------------------------------------------------------
   Ejemplo. Especificar las siguientes funciones y sus argumentos
   explícitos e implícitos:
   + nil
   + constructor
   + repeat
   ------------------------------------------------------------------ *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la lista formada por los números naturales 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      repeat''' {X : Type} (x : X) (count : nat) : list X
   tal que (repeat'' X x n) es la lista obtenida repitiendo n veces el
   elemento x, usando argumentos implícitos. Por ejemplo,
      repeat'' nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
      repeat'' bool false 1 = cons bool false (nil bool).
   ------------------------------------------------------------------ *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

Example test_repeat'''1 :
  repeat''' 4 2 = cons 4 (cons 4 nil).
Proof. reflexivity.  Qed.

Example test_repeat'''2 :
  repeat false 1 = cons false nil.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo (list' {X}) para representar las listas de
   elementos de con los constructores nil y cons tales que 
   + nil' es la lista vacía y
   + (cons' x ys) es la lista obtenida añadiendo el elemento x a la
     lista ys.
   ------------------------------------------------------------------ *)

Inductive list' {X:Type} : Type :=
  | nil'  : list'
  | cons' : X -> list' -> list'.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      app {X : Type} (l1 l2 : list X) : (list X)
   tal que (app xs ys) es la concatenación de xs e ys.
   ------------------------------------------------------------------ *)

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      rev {X:Type} (l:list X) : list X
   tal que (rev xs) es la inversa de xs. Por ejemplo,
      rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
      rev (cons true nil) = cons true nil.
   ------------------------------------------------------------------ *)

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      length {X : Type} (l : list X) : nat 
   tal que (length xs) es el número de elementos de xs. Por ejemplo,
      length (cons 1 (cons 2 (cons 3 nil))) = 3.
   ------------------------------------------------------------------ *)

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => S (length l')
  end.

Example test_length1:
  length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§§ Explicitación de argumentos  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Especificar que la siguiente definición es errónea
      Fail Definition mynil := nil.
   ------------------------------------------------------------------ *)

Fail Definition mynil := nil.
(* ==> Error: Cannot infer the implicit parameter X of nil. *)

(* ---------------------------------------------------------------------
   Ejemplo. Completar la definición anterior para obtener la lista
   vacía de números naturales.
   ------------------------------------------------------------------ *)

Definition mynil : list nat := nil.

(* Alternativamente *)
Definition mynil' := @nil nat.

(* ---------------------------------------------------------------------
   Ejemplo. Definir las siguientes abreviaturas
   + "x :: y"         para (cons x y)
   + "[ ]"            para nil
   + "[ x ; .. ; y ]" para (cons x .. (cons y []) ..).
   + "x ++ y"         para (app x y)
   ------------------------------------------------------------------ *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la lista cuyos elementos son 1, 2 y 3.
   ------------------------------------------------------------------ *)

Definition list123''' := [1; 2; 3].

(* =====================================================================
   §§§ Ejercicios  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que la lista vacía es el elemento neutro por la
   derecha de la concatenación.
   ------------------------------------------------------------------ *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  induction l.
  + reflexivity.
  + simpl. rewrite IHl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que la concatenación es asociativa.
   ------------------------------------------------------------------ *)

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  + reflexivity.
  + simpl. rewrite IHl. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que la longitud de una concatenación es la suma de
   las longitudes de las listas (es decir, es un homomorfismo).
   ------------------------------------------------------------------ *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1.
  + reflexivity.
  + simpl. rewrite IHl1. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      rev (l1 ++ l2) = rev l2 ++ rev l1.
   ------------------------------------------------------------------ *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  + simpl. rewrite app_nil_r. reflexivity.
  + simpl. rewrite IHl1, app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      rev (rev l) = l.
   ------------------------------------------------------------------ *)

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l.
  + reflexivity.
  + simpl. rewrite rev_app_distr, IHl. reflexivity.
Qed.

(* =====================================================================
   §§ Polimorfismo de pares  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir el tipo prod (X Y) con el constructor pair tal que 
   (pair x y) es el par cuyas componentes son x e y.
   ------------------------------------------------------------------ *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(* ---------------------------------------------------------------------
   Ejemplo. Definir la abreviatura
      "( x , y )" para (pair x y).
   ------------------------------------------------------------------ *)

Notation "( x , y )" := (pair x y).

(* ---------------------------------------------------------------------
   Ejemplo. Definir la abreviatura
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

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ Resultados opcionales polimórficos  
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

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
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

Example test_hd_error1 : hd_error [1;2] = Some 1.
 Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 Proof. reflexivity. Qed.

(* =====================================================================
   § Funciones como datos
   ================================================================== *)

(* =====================================================================
   § Funciones de orden superior 
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

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ Filtrado  
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

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
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
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* =====================================================================
   §§ Funciones anónimas  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      doit3times (fun n => n * n) 2 = 256.
   ------------------------------------------------------------------ *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Calcular
      filter (fun l => beq_nat (length l) 1)
             [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
   ------------------------------------------------------------------ *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
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

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
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

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* =====================================================================
   §§ Aplicación a todos los elementos (map)
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

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ---------------------------------------------------------------------
   Ejercicio. Demostrar que
      map f (rev l) = rev (map f l).
   ------------------------------------------------------------------ *)

Lemma map_app_distr : forall (X Y : Type) (f : X -> Y) (l t : list X),
    map f (l ++ t) = map f l ++ map f t.
Proof.
  intros X Y f l t.
  induction l.
  + reflexivity.
  + simpl. rewrite IHl. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  + reflexivity.
  + simpl. rewrite map_app_distr, IHl. reflexivity.
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

Example test_flat_map1:
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
   §§ Plegados (fold)  
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejemplo. Definir la función
      fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y
   tal que (fold f l b) es el plegado de l con la operación f a partir
   del elemento b. Por ejemplo,
      fold mult [1;2;3;4] 1                 = 24.
      fold andb [true;true;false;true] true = false.
      fold app  [[1];[];[2;3];[4]] []       = [1;2;3;4].
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
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* =====================================================================
   §§ Funciones que construyen funciones  
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

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* =====================================================================
   § Ejercicios 
   ================================================================== *)

Module Exercises.

(* ---------------------------------------------------------------------
   Ejercicio. Definir, usando fold, la función
      fold_length {X : Type} (l : list X) : nat
   tal que (fold_length l) es la longitud de l. Por ejemplo,
      fold_length [4;7;0] = 3.
   ------------------------------------------------------------------ *)
  
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------
   Ejemplo. Demostrar que
      fold_length l = length l.
   ------------------------------------------------------------------ *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  unfold fold_length.
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
      forall X n l, length l = n -> @nth_error X l n = None
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
