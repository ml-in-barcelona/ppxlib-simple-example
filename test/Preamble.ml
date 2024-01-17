
type __ = Obj.t

type coq_UU = __

type 'x fromUUtoType = 'x

type empty = |

(** val empty_rect : empty -> 'a1 **)

let empty_rect _ =
  assert false (* absurd case *)

(** val empty_rec : empty -> 'a1 **)

let empty_rec _ =
  assert false (* absurd case *)

type coq_unit =
| Coq_tt

(** val unit_rect : 'a1 -> coq_unit -> 'a1 **)

let unit_rect f _ =
  f

(** val unit_rec : 'a1 -> coq_unit -> 'a1 **)

let unit_rec f _ =
  f

type bool =
| Coq_true
| Coq_false

(** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rect f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rec f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val negb : bool -> bool **)

let negb = function
| Coq_true -> Coq_false
| Coq_false -> Coq_true

type ('a, 'b) coprod =
| Coq_ii1 of 'a
| Coq_ii2 of 'b

(** val coprod_rect :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3 **)

let coprod_rect f f0 = function
| Coq_ii1 a -> f a
| Coq_ii2 b -> f0 b

(** val coprod_rec :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3 **)

let coprod_rec f f0 = function
| Coq_ii1 a -> f a
| Coq_ii2 b -> f0 b

type nat =
| O
| S of nat

(** val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

let rec nat_rect f f0 = function
| O -> f
| S n0 -> f0 n0 (nat_rect f f0 n0)

(** val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

let rec nat_rec f f0 = function
| O -> f
| S n0 -> f0 n0 (nat_rec f f0 n0)

(** val succ : nat -> nat **)

let succ x =
  S x

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S n0 -> add (mul n0 m) m

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

type 'a paths =
| Coq_paths_refl

(** val paths_rect : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2 **)

let paths_rect _ f _ _ =
  f

(** val paths_rec : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2 **)

let paths_rec _ f _ _ =
  f

(** val pr1 : ('a1, 'a2) total2 -> 'a1 **)

type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }
                       
let pr1 t =
  t.pr1

(** val pr2 : ('a1, 'a2) total2 -> 'a2 **)

let pr2 t =
  t.pr2



(** val total2_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3 **)

let total2_rect f t =
  f (pr1 t) (pr2 t)

(** val total2_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3 **)


let total2_rec f t =
  f (pr1 t) (pr2 t)
