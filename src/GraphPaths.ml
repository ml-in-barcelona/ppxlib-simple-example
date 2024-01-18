open PartA
open Preamble

type __ = Obj.t

type ('v, 'e) issymmetric = 'v -> 'v -> ('e, 'e) weq

type ('v, 'e) gpaths_of_length = __

type ('v, 'e) gpaths = (nat, ('v, 'e) gpaths_of_length) total2

(** val nil : 'a1 -> ('a1, 'a2) gpaths **)

let nil _ =
  { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }

(** val cons :
    'a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths **)

let cons _ _ v e p =
  { pr1 = (S p.pr1); pr2 =
    (Obj.magic { pr1 = v; pr2 = { pr1 = e; pr2 = p.pr2 } }) }

(** val gpaths_ind :
    'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> 'a3 -> 'a3) ->
    'a1 -> ('a1, 'a2) gpaths -> 'a3 **)

let gpaths_ind _ h1 h2 u p =
  let n = p.pr1 in
  let p0 = p.pr2 in
  let rec f n0 u0 p1 =
    match n0 with
    | O -> h1
    | S n1 ->
      let v = (Obj.magic p1).pr1 in
      let x = (Obj.magic p1).pr2 in
      let e = x.pr1 in
      let p2 = x.pr2 in h2 u0 v e { pr1 = n1; pr2 = p2 } (f n1 v p2)
  in f n u p0

(** val foldr :
    'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2)
    gpaths -> 'a3 **)

let foldr w f b =
  gpaths_ind w b (fun u v e _ b0 -> f u v e b0)

(** val concat :
    'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths -> ('a1, 'a2)
    gpaths **)

let concat u v w p q =
  foldr v (fun u0 v0 -> cons w u0 v0) q u p

(** val append :
    'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> 'a2 -> ('a1, 'a2) gpaths **)

let append u v w p e =
  concat u v w p (cons w v w e (nil w))

(** val reverse :
    ('a1, 'a2) issymmetric -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2)
    gpaths **)

let reverse h u v p =
  gpaths_ind v (nil v) (fun u0 u' e _ q ->
    append v u' u0 q (invmap (h u' u0) e)) u p

type ('v, 'e) symmetric_closure = ('e, 'e) coprod

(** val issymmetric_symmetric_closure :
    ('a1, ('a1, 'a2) symmetric_closure) issymmetric **)

let issymmetric_symmetric_closure _ _ =
  weqcoprodcomm

(** val reverse_in_closure :
    'a1 -> 'a1 -> ('a1, ('a1, 'a2) symmetric_closure) gpaths -> ('a1, ('a1,
    'a2) symmetric_closure) gpaths **)

let reverse_in_closure u v p =
  reverse issymmetric_symmetric_closure u v p
