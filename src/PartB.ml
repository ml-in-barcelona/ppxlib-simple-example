open PartA
open Preamble

type __ = Obj.t

type 'x isofhlevel = __

(** val hlevelretract :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1
    isofhlevel -> 'a2 isofhlevel **)

let rec hlevelretract n p s eps x0 =
  match n with
  | O -> Obj.magic iscontrretract p s eps x0
  | S n0 ->
    Obj.magic (fun x x' ->
      let is = Obj.magic x0 (s x) (s x') in
      let s' = maponpaths s x x' in
      let p' = pathssec2 s p eps x x' in
      let eps' = pathssec3 s p eps x x' in
      Obj.magic hlevelretract n0 p' s' eps' is)

(** val isofhlevelweqf :
    nat -> ('a1, 'a2) weq -> 'a1 isofhlevel -> 'a2 isofhlevel **)

let isofhlevelweqf n f x0 =
  hlevelretract n (pr1weq f) (invmap f) (homotweqinvweq f) x0

(** val isofhlevelweqb :
    nat -> ('a1, 'a2) weq -> 'a2 isofhlevel -> 'a1 isofhlevel **)

let isofhlevelweqb n f x0 =
  hlevelretract n (invmap f) (pr1weq f) (homotinvweqweq f) x0

(** val isofhlevelsn : nat -> ('a1 -> 'a1 isofhlevel) -> 'a1 isofhlevel **)

let isofhlevelsn _ f =
  Obj.magic (fun x x' -> Obj.magic f x x x')

(** val isofhlevelssn :
    nat -> ('a1 -> 'a1 paths isofhlevel) -> 'a1 isofhlevel **)

let isofhlevelssn n is =
  Obj.magic (fun x _ -> let x1 = fun _ -> is x in isofhlevelsn n x1)

type ('x, 'y) isofhlevelf = 'y -> ('x, 'y) hfiber isofhlevel

(** val isofhlevelfhomot :
    nat -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
    isofhlevelf -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfhomot n f f' h x0 y =
  isofhlevelweqf n (weqhfibershomot f f' h y) (x0 y)

(** val isofhlevelfpmap :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> (('a1, 'a3) total2,
    ('a2, 'a3) total2) isofhlevelf **)

let isofhlevelfpmap n f x0 y =
  let yy = y.pr1 in
  let g = hfiberfpmap f y in
  let is = isweqhfiberfp f y in
  let isy = x0 yy in isofhlevelweqb n (make_weq g is) isy

(** val isofhlevelfffromZ :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr
    -> 'a3 isofhlevel -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfffromZ n f g z fs isz y =
  let w = invweq (ezweq1 f g z fs y) in
  isofhlevelweqb n w (Obj.magic isz (g y) z)

(** val isofhlevelXfromg :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr
    -> ('a2, 'a3) isofhlevelf -> 'a1 isofhlevel **)

let isofhlevelXfromg n f g z fs isf =
  let w = make_weq (ezmap f g z fs.pr1) fs.pr2 in isofhlevelweqb n w (isf z)

(** val isofhlevelffromXY :
    nat -> ('a1 -> 'a2) -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2)
    isofhlevelf **)

let rec isofhlevelffromXY n f x0 x1 =
  match n with
  | O ->
    let is1 = { pr1 = (f (Obj.magic x0).pr1); pr2 = (fun t ->
      let is = Obj.magic x1 t (f (Obj.magic x0).pr1) in is.pr1) }
    in
    Obj.magic isweqcontrcontr f x0 is1
  | S n0 ->
    let is3 = fun y x xe' ->
      Obj.magic isofhlevelffromXY n0 (d2g f y x xe') (Obj.magic x0 xe'.pr1 x)
        (Obj.magic x1 (f x) y)
    in
    let is4 = fun y x xe' e ->
      isofhlevelweqb n0 (ezweq3g f y x xe' e) (is3 y x xe' e)
    in
    (fun y ->
    Obj.magic (fun xe xe' ->
      let t = xe.pr1 in let x = xe.pr2 in is4 y t xe' x))

(** val isofhlevelXfromfY :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> 'a2 isofhlevel -> 'a1
    isofhlevel **)

let rec isofhlevelXfromfY n f x0 x1 =
  match n with
  | O -> Obj.magic iscontrweqb (make_weq f (Obj.magic x0)) x1
  | S n0 ->
    let is1 = fun y xe xe' -> Obj.magic x0 y xe xe' in
    let is2 = fun y x xe' y0 ->
      isofhlevelweqf n0 (ezweq3g f y x xe' y0)
        (is1 y (make_hfiber f y x y0) xe')
    in
    Obj.magic (fun x' x ->
      let y = f x' in
      let e' = Coq_paths_refl in
      let xe' = make_hfiber f y x' e' in
      Obj.magic isofhlevelXfromfY n0 (d2g f y x xe') (is2 y x xe')
        (Obj.magic x1 (f x) y))

(** val isofhlevelffib :
    nat -> 'a1 -> ('a1 -> 'a1 paths isofhlevel) -> ('a2, ('a1, 'a2) total2)
    isofhlevelf **)

let isofhlevelffib n x is xp =
  isofhlevelweqf n (ezweq1pr1 x xp) (is xp.pr1)

(** val isofhlevelfhfiberpr1y :
    nat -> ('a1 -> 'a2) -> 'a2 -> ('a2 -> 'a2 paths isofhlevel) -> (('a1,
    'a2) hfiber, 'a1) isofhlevelf **)

let isofhlevelfhfiberpr1y n f y is x =
  isofhlevelweqf n (ezweq1g f y x) (is (f x))

(** val isofhlevelfsnfib :
    nat -> 'a1 -> 'a1 paths isofhlevel -> ('a2, ('a1, 'a2) total2) isofhlevelf **)

let isofhlevelfsnfib n x is xp =
  isofhlevelweqf (S n) (ezweq1pr1 x xp) (isofhlevelsn n (fun _ -> is))

(** val isofhlevelfsnhfiberpr1 :
    nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 paths isofhlevel -> (('a1, 'a2) hfiber,
    'a1) isofhlevelf **)

let isofhlevelfsnhfiberpr1 n f y is x =
  isofhlevelweqf (S n) (ezweq1g f y x) (isofhlevelsn n (fun _ -> is))

(** val isofhlevelfhfiberpr1 :
    nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 isofhlevel -> (('a1, 'a2) hfiber, 'a1)
    isofhlevelf **)

let isofhlevelfhfiberpr1 n f y is =
  isofhlevelfhfiberpr1y n f y (fun y' -> Obj.magic is y' y)

(** val isofhlevelff :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> ('a1, 'a2) isofhlevelf **)

let isofhlevelff n f g x0 x1 y =
  let ye = make_hfiber g (g y) y Coq_paths_refl in
  isofhlevelweqb n (ezweqhf f g (g y) ye)
    (isofhlevelffromXY n (hfibersgftog f g (g y)) (x0 (g y)) (x1 (g y)) ye)

(** val isofhlevelfgf :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> ('a1, 'a3) isofhlevelf **)

let isofhlevelfgf n f g x0 x1 z =
  let is1 = fun ye -> isofhlevelweqf n (ezweqhf f g z ye) (x0 ye.pr1) in
  let is2 = x1 z in isofhlevelXfromfY n (hfibersgftog f g z) is1 is2

(** val isofhlevelfgwtog :
    nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a3) isofhlevelf **)

let isofhlevelfgwtog n w g is z =
  let is' = fun ye -> iscontrweqf (ezweqhf (pr1weq w) g z ye) (w.pr2 ye.pr1)
  in
  isofhlevelweqf n (make_weq (hfibersgftog (pr1weq w) g z) is') (is z)

(** val isofhlevelfgtogw :
    nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isofhlevelf -> ('a1,
    'a3) isofhlevelf **)

let isofhlevelfgtogw n w g is z =
  let is' = fun ye -> iscontrweqf (ezweqhf (pr1weq w) g z ye) (w.pr2 ye.pr1)
  in
  isofhlevelweqb n (make_weq (hfibersgftog (pr1weq w) g z) is') (is z)

(** val isofhlevelfhomot2 :
    nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) weq -> ('a1 -> 'a3
    paths) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3) isofhlevelf **)

let isofhlevelfhomot2 n f f' w h x0 =
  let x1 = isofhlevelfhomot n f (fun x -> f' (pr1weq w x)) h x0 in
  isofhlevelfgwtog n w f' x1

(** val isofhlevelfonpaths :
    nat -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> ('a1, 'a2) isofhlevelf -> ('a1
    paths, 'a2 paths) isofhlevelf **)

let isofhlevelfonpaths n f x x' x0 =
  let y = f x' in
  let xe' = make_hfiber f (f x') x' Coq_paths_refl in
  let is1 = fun y0 ->
    isofhlevelweqf n (ezweq3g f (f x') x xe' y0)
      (Obj.magic x0 y (make_hfiber f (f x') x y0) xe')
  in
  let h = fun _ -> Coq_paths_refl in
  isofhlevelfhomot2 n (d2g f (f x') x xe') (maponpaths f x x')
    (make_weq (pathsinv0 x' x) (isweqpathsinv0 x' x)) h is1

(** val isofhlevelfsn :
    nat -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> ('a1 paths, 'a2 paths) isofhlevelf)
    -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfsn n f x0 _ =
  Obj.magic (fun x x' ->
    let x1 = x.pr1 in
    let e = x.pr2 in
    let x'0 = x'.pr1 in
    let xe' = make_hfiber f (f x'0) x'0 Coq_paths_refl in
    let is1 =
      let h = fun ee ->
        pathsinv0
          (pathscomp0 (f x1) (f x'0) (f x'0)
            (maponpaths f x1 x'0 (pathsinv0 x'0 x1 ee)) Coq_paths_refl)
          (maponpaths f x1 x'0 (pathsinv0 x'0 x1 ee))
          (pathscomp0rid (f x1) (f x'0)
            (maponpaths f x1 x'0 (pathsinv0 x'0 x1 ee)))
      in
      let is2 =
        isofhlevelfgtogw n
          (make_weq (pathsinv0 x'0 x1) (isweqpathsinv0 x'0 x1))
          (maponpaths f x1 x'0) (x0 x1 x'0)
      in
      isofhlevelfhomot n (fun ee ->
        maponpaths f x1 x'0 (pathsinv0 x'0 x1 ee)) (d2g f (f x'0) x1 xe') h
        is2
    in
    isofhlevelweqb n (ezweq3g f (f x'0) x1 xe' e) (is1 e))

(** val isofhlevelfssn :
    nat -> ('a1 -> 'a2) -> ('a1 -> ('a1 paths, 'a2 paths) isofhlevelf) ->
    ('a1, 'a2) isofhlevelf **)

let isofhlevelfssn n f x0 _ =
  let x1 = fun xe0 ->
    let x = xe0.pr1 in
    let e' = Coq_paths_refl in
    let xe' = make_hfiber f (f x) x e' in
    let is1 =
      let h = fun ee ->
        pathsinv0
          (pathscomp0 (f x) (f x) (f x) (maponpaths f x x (pathsinv0 x x ee))
            Coq_paths_refl) (maponpaths f x x (pathsinv0 x x ee))
          (pathscomp0rid (f x) (f x) (maponpaths f x x (pathsinv0 x x ee)))
      in
      let is2 =
        isofhlevelfgtogw (S n)
          (make_weq (pathsinv0 x x) (isweqpathsinv0 x x)) (maponpaths f x x)
          (x0 x)
      in
      isofhlevelfhomot (S n) (fun ee -> maponpaths f x x (pathsinv0 x x ee))
        (d2g f (f x) x xe') h is2
    in
    isofhlevelweqb (S n) (ezweq3g f (f x) x xe' e') (is1 e')
  in
  isofhlevelssn n x1

(** val isofhlevelfpr1 :
    nat -> ('a1 -> 'a2 isofhlevel) -> (('a1, 'a2) total2, 'a1) isofhlevelf **)

let isofhlevelfpr1 n is x =
  isofhlevelweqf n (ezweqpr1 x) (is x)

(** val isweqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) isweq **)

let isweqpr1 is1 y =
  let isy = is1 y in iscontrweqf (ezweqpr1 y) isy

(** val weqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) weq **)

let weqpr1 is =
  make_weq (fun t -> t.pr1) (isweqpr1 is)

(** val isofhleveltotal2 :
    nat -> 'a1 isofhlevel -> ('a1 -> 'a2 isofhlevel) -> ('a1, 'a2) total2
    isofhlevel **)

let isofhleveltotal2 n is1 is2 =
  isofhlevelXfromfY n (fun t -> t.pr1) (isofhlevelfpr1 n is2) is1

(** val isofhleveldirprod :
    nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) dirprod isofhlevel **)

let isofhleveldirprod n is1 is2 =
  isofhleveltotal2 n is1 (fun _ -> is2)

type 'x isaprop = 'x isofhlevel

type ('x, 'y) isPredicate = 'x -> 'y isaprop

(** val isapropunit : coq_unit isaprop **)

let isapropunit =
  Obj.magic iscontrpathsinunit

(** val isapropdirprod :
    'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) dirprod isaprop **)

let isapropdirprod x =
  isofhleveldirprod (S O) x

(** val isapropifcontr : 'a1 iscontr -> 'a1 isaprop **)

let isapropifcontr is =
  let f = fun _ -> Coq_tt in
  let isw = isweqcontrtounit is in
  isofhlevelweqb (S O) (make_weq f isw) (Obj.magic iscontrpathsinunit)

(** val hlevelntosn : nat -> 'a1 isofhlevel -> 'a1 isofhlevel **)

let rec hlevelntosn = function
| O -> Obj.magic isapropifcontr
| S n0 ->
  (fun x ->
    Obj.magic (fun t1 t2 -> let xX = Obj.magic x t1 t2 in hlevelntosn n0 xX))

(** val isofhlevelcontr : nat -> 'a1 iscontr -> 'a1 isofhlevel **)

let rec isofhlevelcontr n x0 =
  match n with
  | O -> Obj.magic x0
  | S n0 ->
    Obj.magic (fun x x' ->
      let is = Obj.magic isapropifcontr x0 x x' in isofhlevelcontr n0 is)

(** val isofhlevelfweq : nat -> ('a1, 'a2) weq -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfweq n f y =
  isofhlevelcontr n (f.pr2 y)

(** val isweqfinfibseq :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a3
    iscontr -> ('a1, 'a2) isweq **)

let isweqfinfibseq f g z fs isz =
  Obj.magic isofhlevelfffromZ O f g z fs (isapropifcontr isz)

(** val weqhfibertocontr :
    ('a1 -> 'a2) -> 'a2 -> 'a2 iscontr -> (('a1, 'a2) hfiber, 'a1) weq **)

let weqhfibertocontr f y is =
  { pr1 = (hfiberpr1 f y); pr2 =
    (Obj.magic isofhlevelfhfiberpr1 O f y (hlevelntosn O (Obj.magic is))) }

(** val weqhfibertounit : (('a1, coq_unit) hfiber, 'a1) weq **)

(* let weqhfibertounit =  *)
(*   weqhfibertocontr (fun _ -> Coq_tt) Coq_tt iscontrunit  *)

(** val isofhleveltofun :
    nat -> 'a1 isofhlevel -> ('a1, coq_unit) isofhlevelf **)

(* let isofhleveltofun n is _ = *)
(*   isofhlevelweqb n weqhfibertounit is *)

(** val isofhlevelfromfun :
    nat -> ('a1, coq_unit) isofhlevelf -> 'a1 isofhlevel **)

(* let isofhlevelfromfun n is = *)
(*   isofhlevelweqf n weqhfibertounit (is Coq_tt) *)

(** val weqhfiberunit :
    ('a1 -> 'a2) -> 'a2 -> (('a1, (coq_unit, 'a2) hfiber) total2, ('a1, 'a2)
    hfiber) weq **)

(* let weqhfiberunit i z = *)
(*   weq_iso (fun x0 -> *)
(*     let x = x0.pr1 in *)
(*     let pr3 = x0.pr2 in *)
(*     let e = pr3.pr2 in { pr1 = x; pr2 = (pathsinv0 z (i x) e) }) (fun x0 -> *)
(*     let x = x0.pr1 in *)
(*     let e = x0.pr2 in *)
(*     { pr1 = x; pr2 = { pr1 = Coq_tt; pr2 = (pathsinv0 (i x) z e) } }) *)
(*     (fun x0 -> *)
(*     let x = x0.pr1 in *)
(*     let pr3 = x0.pr2 in *)
(*     let t = pr3.pr1 in *)
(*     let e = pr3.pr2 in *)
(*     maponpaths (fun x1 -> { pr1 = x; pr2 = x1 }) { pr1 = Coq_tt; pr2 = *)
(*       (pathsinv0 (i x) z (pathsinv0 z (i x) e)) } { pr1 = t; pr2 = e } *)
(*       (two_arg_paths_f (fun x1 x2 -> { pr1 = x1; pr2 = x2 }) Coq_tt *)
(*         (pathsinv0 (i x) z (pathsinv0 z (i x) e)) t e *)
(*         (let x1 = Coq_tt in (Obj.magic isapropunit x1 t).pr1) *)
(*         (internal_paths_rew_r (pathsinv0 z z (pathsinv0 z z Coq_paths_refl)) *)
(*           Coq_paths_refl Coq_paths_refl (pathsinv0inv0 z z Coq_paths_refl)))) *)
(*     (fun y -> *)
(*     let x = y.pr1 in *)
(*     let e = y.pr2 in *)
(*     maponpaths (fun x0 -> { pr1 = x; pr2 = x0 }) *)
(*       (pathsinv0 z (i x) (pathsinv0 (i x) z e)) e (pathsinv0inv0 (i x) z e)) *)

(** val isofhlevelsnprop : nat -> 'a1 isaprop -> 'a1 isofhlevel **)

let isofhlevelsnprop n is =
  Obj.magic (fun x x' -> isofhlevelcontr n (Obj.magic is x x'))

(** val iscontraprop1 : 'a1 isaprop -> 'a1 -> 'a1 iscontr **)

let iscontraprop1 is x =
  { pr1 = x; pr2 = (fun t -> let is' = Obj.magic is t x in is'.pr1) }

(** val iscontraprop1inv : ('a1 -> 'a1 iscontr) -> 'a1 isaprop **)

let iscontraprop1inv f =
  isofhlevelsn O (fun x -> hlevelntosn O (Obj.magic f x))

type 'x isProofIrrelevant = 'x -> 'x -> 'x paths

(** val proofirrelevance : 'a1 isaprop -> 'a1 isProofIrrelevant **)

let proofirrelevance is x x' =
  iscontrpr1 (Obj.magic is x x')

(** val invproofirrelevance : 'a1 isProofIrrelevant -> 'a1 isaprop **)

let invproofirrelevance ee =
  Obj.magic (fun x x' ->
    Obj.magic isapropifcontr { pr1 = x; pr2 = (fun t -> ee t x) } x x')

(** val isProofIrrelevant_paths :
    'a1 isProofIrrelevant -> 'a1 -> 'a1 -> 'a1 paths isProofIrrelevant **)

let isProofIrrelevant_paths irr x y p q =
  let r = Obj.magic invproofirrelevance irr x y in
  pathscomp0 p r.pr1 q (r.pr2 p) (pathsinv0 q r.pr1 (r.pr2 q))

(** val isapropcoprod :
    'a1 isaprop -> 'a2 isaprop -> ('a1 -> 'a2 -> empty) -> ('a1, 'a2) coprod
    isaprop **)

let isapropcoprod i j _ =
  invproofirrelevance (fun a b ->
    inv_equality_by_case a b
      (match a with
       | Coq_ii1 a0 ->
         (match b with
          | Coq_ii1 a1 -> (Obj.magic i a0 a1).pr1
          | Coq_ii2 _ -> assert false (* absurd case *))
       | Coq_ii2 b0 ->
         (match b with
          | Coq_ii1 _ -> assert false (* absurd case *)
          | Coq_ii2 b1 -> (Obj.magic j b0 b1).pr1)))

(** val isweqimplimpl :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2)
    isweq **)

(* let isweqimplimpl f g isx isy = *)
(*   let isx0 = fun x -> proofirrelevance isx (g (f x)) x in *)
(*   let isy0 = fun y -> proofirrelevance isy (f (g y)) y in *)
(*   isweq_iso f g isx0 isy0 *)

(** val weqimplimpl :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2)
    weq **)

(* let weqimplimpl f g isx isy = *)
(*   make_weq f (isweqimplimpl f g isx isy) *)

(** val weqiff :
    ('a1, 'a2) logeq -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) weq **)

(* let weqiff f i j = *)
(*   make_weq f.pr1 (isweqimplimpl f.pr1 f.pr2 i j) *)

(** val weq_to_iff : ('a1, 'a2) weq -> ('a1, 'a2) logeq **)

let weq_to_iff f =
  { pr1 = (pr1weq f); pr2 = (invmap f) }

(** val isapropempty : empty isaprop **)

let isapropempty =
  Obj.magic (fun _ _ -> assert false (* absurd case *))

(** val isapropifnegtrue : ('a1 -> empty) -> 'a1 isaprop **)

let isapropifnegtrue a =
  let w = make_weq a (isweqtoempty a) in isofhlevelweqb (S O) w isapropempty

(** val isapropretract :
    'a2 isaprop -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a1) homot -> 'a1
    isaprop **)

let isapropretract i f g h =
  invproofirrelevance (fun p p' ->
    pathscomp0 p (g (f p)) p' (pathsinv0 (g (f p)) p (h p))
      (pathscomp0 (g (f p)) (g (f p')) p'
        (maponpaths g (f p) (f p') (proofirrelevance i (f p) (f p'))) 
        (h p')))

(** val isapropcomponent1 : ('a1, 'a2) coprod isaprop -> 'a1 isaprop **)

let isapropcomponent1 i =
  invproofirrelevance (fun p p' ->
    Obj.magic equality_by_case (Coq_ii1 p) (Coq_ii1 p')
      (proofirrelevance i (Coq_ii1 p) (Coq_ii1 p')))

(** val isapropcomponent2 : ('a1, 'a2) coprod isaprop -> 'a2 isaprop **)

let isapropcomponent2 i =
  invproofirrelevance (fun q q' ->
    Obj.magic equality_by_case (Coq_ii2 q) (Coq_ii2 q')
      (proofirrelevance i (Coq_ii2 q) (Coq_ii2 q')))

type ('x, 'y) isincl = ('x, 'y) isofhlevelf

type ('x, 'y) incl = ('x -> 'y, ('x, 'y) isincl) total2

(** val make_incl : ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) incl **)

let make_incl f is =
  { pr1 = f; pr2 = is }

(** val pr1incl : ('a1, 'a2) incl -> 'a1 -> 'a2 **)

let pr1incl x =
  x.pr1

(** val isinclweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isincl **)

let isinclweq f is =
  isofhlevelfweq (S O) (make_weq f is)

(** val isofhlevelfsnincl :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfsnincl n _ is y =
  isofhlevelsnprop n (is y)

(** val weqtoincl : ('a1, 'a2) weq -> ('a1, 'a2) incl **)

let weqtoincl w =
  make_incl (pr1weq w) (isinclweq w.pr1 w.pr2)

(** val isinclcomp :
    ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) isincl **)

let isinclcomp f g =
  isofhlevelfgf (S O) (pr1incl f) (pr1incl g) f.pr2 g.pr2

(** val inclcomp : ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) incl **)

let inclcomp f g =
  make_incl (funcomp f.pr1 g.pr1) (isinclcomp f g)

(** val isincltwooutof3a :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl ->
    ('a1, 'a2) isincl **)

let isincltwooutof3a f g isg isgf =
  isofhlevelff (S O) f g isgf (isofhlevelfsnincl (S O) g isg)

(** val isinclgwtog :
    ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isincl -> ('a2, 'a3) isincl **)

let isinclgwtog w g is =
  isofhlevelfgwtog (S O) w g is

(** val isinclgtogw :
    ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl **)

let isinclgtogw w g is =
  isofhlevelfgtogw (S O) w g is

(** val isinclhomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isincl ->
    ('a1, 'a2) isincl **)

let isinclhomot f g h isf =
  isofhlevelfhomot (S O) f g h isf

(** val isofhlevelsninclb :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isofhlevel -> 'a1
    isofhlevel **)

let isofhlevelsninclb n f is =
  isofhlevelXfromfY (S n) f (isofhlevelfsnincl n f is)

(** val isapropinclb :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isaprop -> 'a1 isaprop **)

let isapropinclb f isf =
  isofhlevelXfromfY (S O) f isf

(** val iscontrhfiberofincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> ('a1, 'a2) hfiber iscontr **)

let iscontrhfiberofincl f x0 x =
  let isy = x0 (f x) in
  iscontraprop1 isy (make_hfiber f (f x) x Coq_paths_refl)

type ('x, 'y) isInjective = 'x -> 'x -> ('x paths, 'y paths) isweq

(** val coq_Injectivity :
    ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a1 -> 'a1 -> ('a1 paths, 'a2
    paths) weq **)

let coq_Injectivity f i x x' =
  make_weq (maponpaths f x x') (i x x')

(** val isweqonpathsincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isInjective **)

let isweqonpathsincl f is x x' =
  Obj.magic isofhlevelfonpaths O f x x' is

(** val weqonpathsincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths)
    weq **)

let weqonpathsincl f is x x' =
  make_weq (maponpaths f x x') (isweqonpathsincl f is x x')

(** val invmaponpathsincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths **)

let invmaponpathsincl f is x x' =
  invmap (weqonpathsincl f is x x')

(** val isinclweqonpaths :
    ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> ('a1, 'a2) isincl **)

let isinclweqonpaths f x0 =
  isofhlevelfsn O f (Obj.magic x0)

(** val isinclpr1 :
    ('a1 -> 'a2 isaprop) -> (('a1, 'a2) total2, 'a1) isincl **)

let isinclpr1 is =
  isofhlevelfpr1 (S O) is

(** val subtypeInjectivity :
    ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 ->
    (('a1, 'a2) total2 paths, 'a1 paths) weq **)

let subtypeInjectivity x x0 y =
  coq_Injectivity (fun t -> t.pr1)
    (isweqonpathsincl (fun t -> t.pr1) (isinclpr1 x)) x0 y

(** val subtypePath :
    ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1
    paths -> ('a1, 'a2) total2 paths **)

let subtypePath is s s' e =
  total2_paths_f s s' e
    (let x = s'.pr1 in
     let x0 = transportf s.pr1 s'.pr1 e s.pr2 in
     let x' = s'.pr2 in (Obj.magic is x x0 x').pr1)

(** val subtypePath' :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 isaprop ->
    ('a1, 'a2) total2 paths **)

let subtypePath' s s' e is =
  total2_paths_f s s' e
    (let x = transportf s.pr1 s'.pr1 e s.pr2 in
     let x' = s'.pr2 in (Obj.magic is x x').pr1)

(** val unique_exists :
    'a1 -> 'a2 -> ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2 -> 'a1 paths) -> ('a1,
    'a2) total2 iscontr **)

let unique_exists x b h h0 =
  make_iscontr { pr1 = x; pr2 = b } (fun t ->
    subtypePath h t { pr1 = x; pr2 = b } (h0 t.pr1 t.pr2))

(** val subtypePairEquality :
    ('a1, 'a2) isPredicate -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1,
    'a2) total2 paths **)

let subtypePairEquality is x y p q e =
  two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 }) x p y q e
    (let x0 = transportf x y e p in (Obj.magic is y x0 q).pr1)

(** val subtypePairEquality' :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 isaprop -> ('a1, 'a2) total2
    paths **)

let subtypePairEquality' x y p q e is =
  two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 }) x p y q e
    (let x0 = transportf x y e p in (Obj.magic is x0 q).pr1)

(** val samehfibers :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> 'a2 -> (('a1, 'a2)
    hfiber, ('a1, 'a3) hfiber) weq **)

let samehfibers f g is1 y =
  { pr1 = (hfibersftogf f g (g y) (make_hfiber g (g y) y Coq_paths_refl));
    pr2 =
    (let z = g y in
     let ye = make_hfiber g (g y) y Coq_paths_refl in
     (fun xe ->
     iscontrweqf { pr1 =
       (ezmap
         (d1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
           (fibseqhf f g z ye) xe) (hfibersftogf f g z ye) xe
         (fibseqstrtocomplxstr
           (d1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
             (fibseqhf f g z ye) xe) (hfibersftogf f g z ye) xe
           (fibseq1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
             (fibseqhf f g z ye) xe))); pr2 =
       (isweqezmap1 (hfibersftogf f g z (make_hfiber g z y Coq_paths_refl))
         (hfibersgftog f g z) ye (fibseqhf f g z ye) xe) }
       (Obj.magic isapropifcontr (iscontrhfiberofincl g is1 y)
         (hfibersgftog f g z xe) ye))) }

type 'x isaset = 'x -> 'x -> 'x paths isaprop

(** val isasetunit : coq_unit isaset **)

let isasetunit =
  Obj.magic isofhlevelcontr (S (S O)) iscontrunit

(** val isasetempty : empty isaset **)

let isasetempty =
  Obj.magic isofhlevelsnprop (S O) isapropempty

(** val isasetifcontr : 'a1 iscontr -> 'a1 isaset **)

let isasetifcontr is =
  Obj.magic isofhlevelcontr (S (S O)) is

(** val isasetaprop : 'a1 isaprop -> 'a1 isaset **)

let isasetaprop is =
  Obj.magic isofhlevelsnprop (S O) is

(** val isaset_total2 :
    'a1 isaset -> ('a1 -> 'a2 isaset) -> ('a1, 'a2) total2 isaset **)

let isaset_total2 x x0 =
  Obj.magic isofhleveltotal2 (S (S O)) x x0

(** val isaset_dirprod :
    'a1 isaset -> 'a2 isaset -> ('a1, 'a2) dirprod isaset **)

let isaset_dirprod x x0 =
  isaset_total2 x (fun _ -> x0)

(** val isaset_hfiber :
    ('a1 -> 'a2) -> 'a2 -> 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) hfiber
    isaset **)

let isaset_hfiber f y isX isY =
  isaset_total2 isX (fun x -> isasetaprop (isY (f x) y))

(** val uip :
    'a1 isaset -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths **)

let uip is x x' e e' =
  proofirrelevance (is x x') e e'

(** val isofhlevelssnset : nat -> 'a1 isaset -> 'a1 isofhlevel **)

let isofhlevelssnset n is =
  Obj.magic (fun x x' -> isofhlevelsnprop n (is x x'))

(** val isasetifiscontrloops : ('a1 -> 'a1 paths iscontr) -> 'a1 isaset **)

let isasetifiscontrloops x0 x _ =
  Obj.magic (fun _ x0' -> Obj.magic isapropifcontr (x0 x) Coq_paths_refl x0')

(** val iscontrloopsifisaset : 'a1 isaset -> 'a1 -> 'a1 paths iscontr **)

let iscontrloopsifisaset x0 x =
  iscontraprop1 (x0 x x) Coq_paths_refl

(** val isasetsubset :
    ('a1 -> 'a2) -> 'a2 isaset -> ('a1, 'a2) isincl -> 'a1 isaset **)

let isasetsubset f is1 is2 =
  Obj.magic isofhlevelsninclb (S O) f is2 is1

(** val isinclfromhfiber :
    ('a1 -> 'a2) -> 'a2 isaset -> 'a2 -> (('a1, 'a2) hfiber, 'a1) isincl **)

let isinclfromhfiber f is y =
  isofhlevelfhfiberpr1 (S O) f y (Obj.magic is)

(** val isinclbetweensets :
    ('a1 -> 'a2) -> 'a1 isaset -> 'a2 isaset -> ('a1 -> 'a1 -> 'a2 paths ->
    'a1 paths) -> ('a1, 'a2) isincl **)

(* let isinclbetweensets f isx isy inj = *)
(*   isinclweqonpaths f (fun x x' -> *)
(*     isweqimplimpl (maponpaths f x x') (inj x x') (isx x x') (isy (f x) (f x'))) *)

(** val isinclfromunit :
    (coq_unit -> 'a1) -> 'a1 isaset -> (coq_unit, 'a1) isincl **)

(* let isinclfromunit f is = *)
(*   isinclbetweensets f (Obj.magic isofhlevelcontr (S (S O)) iscontrunit) is *)
(*     (fun _ _ _ -> Coq_paths_refl) *)

(** val set_bijection_to_weq :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> 'a2 isaset -> ('a1,
    'a2) isweq **)

(* let set_bijection_to_weq f bij i y = *)
(*   let sur = bij.pr1 in *)
(*   let inj = bij.pr2 in *)
(*   { pr1 = { pr1 = (sur y).pr1; pr2 = (sur y).pr2 }; pr2 = (fun w -> *)
(*   total2_paths_f w { pr1 = (sur y).pr1; pr2 = (sur y).pr2 } *)
(*     (inj w.pr1 (sur y).pr1 *)
(*       (pathscomp0 (f w.pr1) y (f (sur y).pr1) w.pr2 *)
(*         (pathsinv0 (f (sur y).pr1) y (sur y).pr2))) *)
(*     (let x = w.pr1 in *)
(*      let x0 = f (sur (f x)).pr1 in *)
(*      let x' = f x in *)
(*      let x1 = *)
(*        transportf x (sur (f x)).pr1 *)
(*          (inj x (sur (f x)).pr1 *)
(*            (pathscomp0 (f x) (f x) (f (sur (f x)).pr1) Coq_paths_refl *)
(*              (pathsinv0 (f (sur (f x)).pr1) (f x) (sur (f x)).pr2))) *)
(*          Coq_paths_refl *)
(*      in *)
(*      let x'0 = (sur (f x)).pr2 in (Obj.magic i x0 x' x1 x'0).pr1)) } *)

type ('p, 'q) complementary = ('p -> 'q -> empty, ('p, 'q) coprod) dirprod

(** val complementary_to_neg_iff :
    ('a1, 'a2) complementary -> ('a1 neg, 'a2) logeq **)

let complementary_to_neg_iff c =
  let n = c.pr1 in
  let c0 = c.pr2 in
  { pr1 = (fun _ ->
  match c0 with
  | Coq_ii1 _ -> assert false (* absurd case *)
  | Coq_ii2 b -> b); pr2 = (fun q _H ->
  match c0 with
  | Coq_ii1 a -> n a q
  | Coq_ii2 _ -> n _H q) }

type 'x decidable = ('x, 'x neg) coprod

(** val decidable_to_complementary :
    'a1 decidable -> ('a1, 'a1 neg) complementary **)

let decidable_to_complementary d =
  { pr1 = (fun x n -> n x); pr2 = d }

(** val decidable_dirprod :
    'a1 decidable -> 'a2 decidable -> ('a1, 'a2) dirprod decidable **)

let decidable_dirprod b c =
  match b with
  | Coq_ii1 a ->
    (match c with
     | Coq_ii1 a0 -> Coq_ii1 { pr1 = a; pr2 = a0 }
     | Coq_ii2 b0 -> Coq_ii2 (fun k -> b0 k.pr2))
  | Coq_ii2 b0 -> Coq_ii2 (fun k -> b0 k.pr1)

type 'p isdecprop = (('p, 'p neg) coprod, 'p isaprop) dirprod

(** val isdecproptoisaprop : 'a1 isdecprop -> 'a1 isaprop **)

let isdecproptoisaprop is =
  is.pr2

(** val isdecpropif :
    'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop **)

let isdecpropif i c =
  { pr1 = c; pr2 = i }

(** val isdecpropfromiscontr : 'a1 iscontr -> 'a1 isdecprop **)

let isdecpropfromiscontr i =
  { pr1 = (Coq_ii1 (iscontrpr1 i)); pr2 = (isapropifcontr i) }

(** val isdecpropempty : empty isdecprop **)

let isdecpropempty =
  { pr1 = (Coq_ii2 idfun); pr2 = isapropempty }

(** val isdecpropweqf : ('a1, 'a2) weq -> 'a1 isdecprop -> 'a2 isdecprop **)

(* let isdecpropweqf w i = *)
(*   let xnx = i.pr1 in *)
(*   let i0 = i.pr2 in *)
(*   { pr1 = *)
(*   (match xnx with *)
(*    | Coq_ii1 a -> Coq_ii1 (w.pr1 a) *)
(*    | Coq_ii2 b -> Coq_ii2 (fun x' -> b (invmap w x'))); pr2 = *)
(*   (isofhlevelweqf (S O) w i0) } *)

(** val isdecpropweqb : ('a1, 'a2) weq -> 'a2 isdecprop -> 'a1 isdecprop **)

(* let isdecpropweqb w i = *)
(*   let yny = i.pr1 in *)
(*   let i0 = i.pr2 in *)
(*   { pr1 = *)
(*   (match yny with *)
(*    | Coq_ii1 a -> Coq_ii1 (invmap w a) *)
(*    | Coq_ii2 b -> Coq_ii2 (fun x -> b (w.pr1 x))); pr2 = *)
(*   (isofhlevelweqb (S O) w i0) } *)

(** val isdecproplogeqf :
    'a1 isdecprop -> 'a2 isaprop -> ('a1, 'a2) logeq -> 'a2 isdecprop **)

(* let isdecproplogeqf isx isy lg = *)
(*   let w = weqimplimpl lg.pr1 lg.pr2 (isdecproptoisaprop isx) isy in *)
(*   isdecpropweqf w isx *)

(** val isdecproplogeqb :
    'a1 isaprop -> 'a2 isdecprop -> ('a1, 'a2) logeq -> 'a1 isdecprop **)

(* let isdecproplogeqb isx isy lg = *)
(*   let w = weqimplimpl lg.pr1 lg.pr2 isx (isdecproptoisaprop isy) in *)
(*   isdecpropweqb w isy *)

(** val isdecpropfromneg : 'a1 neg -> 'a1 isdecprop **)

let isdecpropfromneg n =
  { pr1 = (Coq_ii2 n); pr2 = (isapropifnegtrue n) }

type 'x isdeceq = 'x -> 'x -> 'x paths decidable

(** val isdeceqweqf : ('a1, 'a2) weq -> 'a1 isdeceq -> 'a2 isdeceq **)

(* let isdeceqweqf w is y y' = *)
(*   let w' = weqonpaths (invweq w) y y' in *)
(*   let int = is (pr1weq (invweq w) y) (pr1weq (invweq w) y') in *)
(*   (match int with *)
(*    | Coq_ii1 a -> Coq_ii1 (pr1weq (invweq w') a) *)
(*    | Coq_ii2 b -> Coq_ii2 (negf (pr1weq w') b)) *)

(** val isdeceqweqb : ('a1, 'a2) weq -> 'a2 isdeceq -> 'a1 isdeceq **)

(* let isdeceqweqb w is = *)
(*   isdeceqweqf (invweq w) is *)

(** val isdeceqinclb :
    ('a1 -> 'a2) -> 'a2 isdeceq -> ('a1, 'a2) isincl -> 'a1 isdeceq **)

(* let isdeceqinclb f is is' x x' = *)
(*   let w = weqonpathsincl f is' x x' in *)
(*   let int = is (f x) (f x') in *)
(*   (match int with *)
(*    | Coq_ii1 a -> Coq_ii1 (pr1weq (invweq w) a) *)
(*    | Coq_ii2 b -> Coq_ii2 (negf (pr1weq w) b)) *)

(** val isdeceqifisaprop : 'a1 isaprop -> 'a1 isdeceq **)

let isdeceqifisaprop is x x' =
  Coq_ii1 (proofirrelevance is x x')

(** val booleq : 'a1 isdeceq -> 'a1 -> 'a1 -> bool **)

let booleq is x x' =
  let d = is x x' in
  (match d with
   | Coq_ii1 _ -> Coq_true
   | Coq_ii2 _ -> Coq_false)

(** val eqfromdnegeq :
    'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths dneg -> 'a1 paths **)

let eqfromdnegeq is x x' _ =
  let d = is x x' in
  (match d with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val isdecequnit : coq_unit isdeceq **)

(* let isdecequnit = *)
(*   isdeceqifisaprop isapropunit *)

(** val isdeceqbool : bool isdeceq **)

let isdeceqbool x' = function
| Coq_true ->
  (match x' with
   | Coq_true -> Coq_ii1 Coq_paths_refl
   | Coq_false -> Coq_ii2 nopathsfalsetotrue)
| Coq_false ->
  (match x' with
   | Coq_true -> Coq_ii2 nopathstruetofalse
   | Coq_false -> Coq_ii1 Coq_paths_refl)

(** val isdeceqcoprod :
    'a1 isdeceq -> 'a2 isdeceq -> ('a1, 'a2) coprod isdeceq **)

let isdeceqcoprod h1 h2 ab ab' =
  match ab with
  | Coq_ii1 a ->
    (match ab' with
     | Coq_ii1 a0 ->
       let d = h1 a a0 in
       (match d with
        | Coq_ii1 a1 -> Coq_ii1 (maponpaths (fun x -> Coq_ii1 x) a a0 a1)
        | Coq_ii2 b -> Coq_ii2 (fun h -> b (ii1_injectivity a a0 h)))
     | Coq_ii2 b -> Coq_ii2 (negpathsii1ii2 a b))
  | Coq_ii2 b ->
    (match ab' with
     | Coq_ii1 a -> Coq_ii2 (negpathsii2ii1 a b)
     | Coq_ii2 b0 ->
       let d = h2 b b0 in
       (match d with
        | Coq_ii1 a -> Coq_ii1 (maponpaths (fun x -> Coq_ii2 x) b b0 a)
        | Coq_ii2 b1 -> Coq_ii2 (fun h -> b1 (ii2_injectivity b b0 h))))

type 'x isisolated = 'x -> ('x paths, 'x paths neg) coprod

type 't isolated = ('t, 't isisolated) total2

(** val make_isolated : 'a1 -> 'a1 isisolated -> 'a1 isolated **)

let make_isolated t i =
  { pr1 = t; pr2 = i }

(** val pr1isolated : 'a1 isolated -> 'a1 **)

let pr1isolated x =
  x.pr1

(** val isaproppathsfromisolated :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop **)

(* let isaproppathsfromisolated x is _ = *)
(*   iscontraprop1inv (fun _ -> *)
(*     let f = fun e -> coconusfromtpair x x e in *)
(*     let is' = onefiber x is in *)
(*     let is2 = iscontrcoconusfromt x in iscontrweqb (make_weq f is') is2) *)

(** val isaproppathstoisolated :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop **)

(* let isaproppathstoisolated x is x' = *)
(*   isofhlevelweqf (S O) (weqpathsinv0 x x') (isaproppathsfromisolated x is x') *)

(** val isisolatedweqf :
    ('a1, 'a2) weq -> 'a1 -> 'a1 isisolated -> 'a2 isisolated **)

(* let isisolatedweqf f x is y = *)
(*   let c = is (invmap f y) in *)
(*   (match c with *)
(*    | Coq_ii1 a -> Coq_ii1 (pathsweq1' f x y a) *)
(*    | Coq_ii2 b -> Coq_ii2 (fun eq -> b (pathsweq1 f x y eq))) *)

(** val isisolatedinclb :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a2 isisolated -> 'a1
    isisolated **)

let isisolatedinclb f is x is0 x' =
  let a = is0 (f x') in
  (match a with
   | Coq_ii1 a0 -> Coq_ii1 (invmaponpathsincl f is x x' a0)
   | Coq_ii2 b -> Coq_ii2 (negf (maponpaths f x x') b))

(** val disjointl1 : ('a1, coq_unit) coprod isisolated **)

let disjointl1 = function
| Coq_ii1 a -> Coq_ii2 (negpathsii2ii1 a Coq_tt)
| Coq_ii2 _ -> Coq_ii1 Coq_paths_refl

(** val isasetifdeceq : 'a1 isdeceq -> 'a1 isaset **)

 (* let isasetifdeceq is x x' = *)
 (*  isaproppathsfromisolated x (is x) x' *)

(** val isdeceq_total2 :
    'a1 isdeceq -> ('a1 -> 'a2 isdeceq) -> ('a1, 'a2) total2 isdeceq **)

(* let isdeceq_total2 hX hP xp yq = *)
(*   let d = hX xp.pr1 yq.pr1 in *)
(*   (match d with *)
(*    | Coq_ii1 a -> *)
(*      let d0 = hP yq.pr1 (transportf xp.pr1 yq.pr1 a xp.pr2) yq.pr2 in *)
(*      (match d0 with *)
(*       | Coq_ii1 a0 -> Coq_ii1 (total2_paths_f xp yq a a0) *)
(*       | Coq_ii2 b -> *)
(*         Coq_ii2 (fun e_xpyq -> *)
(*           b *)
(*             (let e_pq = fiber_paths xp yq e_xpyq in *)
(*              pathscomp0 (transportf xp.pr1 yq.pr1 a xp.pr2) *)
(*                (transportf xp.pr1 yq.pr1 (base_paths xp yq e_xpyq) xp.pr2) *)
(*                yq.pr2 *)
(*                (maponpaths (fun e -> transportf xp.pr1 yq.pr1 e xp.pr2) a *)
(*                  (base_paths xp yq e_xpyq) *)
(*                  (let x = xp.pr1 in *)
(*                   let x' = yq.pr1 in *)
(*                   let x'0 = base_paths xp yq e_xpyq in *)
(*                   (Obj.magic isasetifdeceq hX x x' a x'0).pr1)) e_pq))) *)
(*    | Coq_ii2 b -> Coq_ii2 (fun e_xypq -> b (base_paths xp yq e_xypq))) *)

(** val isolfun1 : 'a1 -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a1 -> 'a2 **)

let isolfun1 _ i1 y1 y' x =
  let c = i1 x in (match c with
                   | Coq_ii1 _ -> y1
                   | Coq_ii2 _ -> y')

(** val decfun1 : 'a1 isdeceq -> 'a1 -> 'a2 -> 'a2 -> 'a1 -> 'a2 **)

let decfun1 i x1 =
  isolfun1 x1 (i x1)

(** val isolfun2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a2 ->
    'a1 -> 'a2 **)

let isolfun2 _ _ i1 i2 y1 y2 y' x =
  let c = i1 x in
  (match c with
   | Coq_ii1 _ -> y1
   | Coq_ii2 _ ->
     let c0 = i2 x in (match c0 with
                       | Coq_ii1 _ -> y2
                       | Coq_ii2 _ -> y'))

(** val decfun2 :
    'a1 isdeceq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 **)

let decfun2 i x1 x2 y1 y2 y' =
  isolfun2 x1 x2 (i x1) (i x2) y1 y2 y'

(** val isolfun3 :
    'a1 -> 'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 isisolated
    -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 **)

let isolfun3 _ _ _ i1 i2 i3 y1 y2 y3 y' x =
  let c = i1 x in
  (match c with
   | Coq_ii1 _ -> y1
   | Coq_ii2 _ ->
     let c0 = i2 x in
     (match c0 with
      | Coq_ii1 _ -> y2
      | Coq_ii2 _ ->
        let c1 = i3 x in (match c1 with
                          | Coq_ii1 _ -> y3
                          | Coq_ii2 _ -> y')))

(** val decfun3 :
    'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2 **)

let decfun3 i x1 x2 x3 y1 y2 y3 y' =
  isolfun3 x1 x2 x3 (i x1) (i x2) (i x3) y1 y2 y3 y'

(** val isasetbool : bool isaset **)

(* let isasetbool = *)
(*   isasetifdeceq isdeceqbool *)

(** val subsetsplit :
    ('a1 -> bool) -> 'a1 -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod **)

let subsetsplit f x =
  let c = boolchoice (f x) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (make_hfiber f Coq_true x a)
   | Coq_ii2 b -> Coq_ii2 (make_hfiber f Coq_false x b))

(** val subsetsplitinv :
    ('a1 -> bool) -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod -> 'a1 **)

let subsetsplitinv _ = function
| Coq_ii1 xt -> xt.pr1
| Coq_ii2 xf -> xf.pr1

(** val weqsubsetsplit :
    ('a1 -> bool) -> ('a1, (('a1, bool) hfiber, ('a1, bool) hfiber) coprod)
    weq **)

(* let weqsubsetsplit f = *)
(*   let ff = subsetsplit f in *)
(*   let gg = subsetsplitinv f in *)
(*   { pr1 = ff; pr2 = *)
(*   (let egf = fun a -> *)
(*      let c = boolchoice (f a) in *)
(*      (match c with *)
(*       | Coq_ii1 _ -> Coq_paths_refl *)
(*       | Coq_ii2 _ -> Coq_paths_refl) *)
(*    in *)
(*    let efg = fun a -> *)
(*      match a with *)
(*      | Coq_ii1 a0 -> *)
(*        let x = a0.pr1 in *)
(*        let et' = a0.pr2 in *)
(*        let c = boolchoice (f x) in *)
(*        (match c with *)
(*         | Coq_ii1 a1 -> *)
(*           maponpaths (fun x0 -> Coq_ii1 x0) (make_hfiber f Coq_true x a1) *)
(*             { pr1 = x; pr2 = et' } *)
(*             (maponpaths (make_hfiber f Coq_true x) a1 et' *)
(*               (uip isasetbool (f x) Coq_true a1 et')) *)
(*         | Coq_ii2 _ -> assert false (\* absurd case *\)) *)
(*      | Coq_ii2 b -> *)
(*        let x = b.pr1 in *)
(*        let et' = b.pr2 in *)
(*        let c = boolchoice (f x) in *)
(*        (match c with *)
(*         | Coq_ii1 _ -> assert false (\* absurd case *\) *)
(*         | Coq_ii2 b0 -> *)
(*           maponpaths (fun x0 -> Coq_ii2 x0) (make_hfiber f Coq_false x b0) *)
(*             { pr1 = x; pr2 = et' } *)
(*             (maponpaths (make_hfiber f Coq_false x) b0 et' *)
(*               (uip isasetbool (f x) Coq_false b0 et'))) *)
(*    in *)
(*    isweq_iso ff gg egf efg) } *)
