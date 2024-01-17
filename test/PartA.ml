open Preamble

type __ = Obj.t

(** val fromempty : empty -> 'a1 **)

let fromempty _ =
  assert false (* absurd case *)

(** val tounit : 'a1 -> coq_unit **)

let tounit _ =
  Coq_tt

(** val termfun : 'a1 -> coq_unit -> 'a1 **)

let termfun x _ =
  x

(** val idfun : 'a1 -> 'a1 **)

let idfun t =
  t

(** val funcomp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3 **)

let funcomp f g x =
  g (f x)

(** val curry : (('a1, 'a2) total2 -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let curry f x y =
  f { pr1 = x; pr2 = y }

(** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3 **)

let uncurry g x =
  g x.pr1 x.pr2

type 'x binop = 'x -> 'x -> 'x

(** val iteration : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1 **)

let rec iteration f = function
| O -> idfun
| S n0 -> funcomp (iteration f n0) f

(** val adjev : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let adjev x f =
  f x

(** val adjev2 : ((('a1 -> 'a2) -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let adjev2 phi x =
  phi (fun f -> f x)

type ('x, 'y) dirprod = ('x, 'y) total2

(** val dirprod_pr1 : ('a1, 'a2) dirprod -> 'a1 **)

let dirprod_pr1 x =
  x.pr1

(** val dirprod_pr2 : ('a1, 'a2) dirprod -> 'a2 **)

let dirprod_pr2 x =
  x.pr2

(** val make_dirprod : 'a1 -> 'a2 -> ('a1, 'a2) dirprod **)

let make_dirprod x y =
  { pr1 = x; pr2 = y }

(** val dirprodadj : (('a1, 'a2) dirprod -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let dirprodadj f x y =
  f { pr1 = x; pr2 = y }

(** val dirprodf :
    ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) dirprod -> ('a2, 'a4) dirprod **)

let dirprodf f f' xx' =
  make_dirprod (f xx'.pr1) (f' xx'.pr2)

(** val ddualand :
    (('a1 -> 'a3) -> 'a3) -> (('a2 -> 'a3) -> 'a3) -> (('a1, 'a2) dirprod ->
    'a3) -> 'a3 **)

let ddualand xp yp x0 =
  xp (fun x -> yp (fun y -> x0 (make_dirprod x y)))

type 'x neg = 'x -> empty

(** val negf : ('a1 -> 'a2) -> 'a2 neg -> 'a1 neg **)

let negf f phi x =
  phi (f x)

type 'x dneg = 'x neg neg

(** val dnegf : ('a1 -> 'a2) -> 'a1 dneg -> 'a2 dneg **)

let dnegf f =
  negf (negf f)

(** val todneg : 'a1 -> 'a1 dneg **)

let todneg =
  adjev

(** val dnegnegtoneg : 'a1 neg dneg -> 'a1 neg **)

let dnegnegtoneg =
  adjev2

(** val dneganddnegl1 : 'a1 dneg -> 'a2 dneg -> ('a1 -> 'a2 neg) neg **)

let dneganddnegl1 dnx dny x2 =
  dnegf x2 dnx dny

(** val dneganddnegimpldneg :
    'a1 dneg -> 'a2 dneg -> ('a1, 'a2) dirprod dneg **)

let dneganddnegimpldneg =
  ddualand

type ('x, 'y) logeq = ('x -> 'y, 'y -> 'x) dirprod

(** val isrefl_logeq : ('a1, 'a1) logeq **)

let isrefl_logeq =
  { pr1 = idfun; pr2 = idfun }

(** val issymm_logeq : ('a1, 'a2) logeq -> ('a2, 'a1) logeq **)

let issymm_logeq e =
  { pr1 = e.pr2; pr2 = e.pr1 }

(** val logeqnegs : ('a1, 'a2) logeq -> ('a1 neg, 'a2 neg) logeq **)

let logeqnegs l =
  make_dirprod (negf l.pr2) (negf l.pr1)

(** val logeq_both_true : 'a1 -> 'a2 -> ('a1, 'a2) logeq **)

let logeq_both_true x y =
  { pr1 = (fun _ -> y); pr2 = (fun _ -> x) }

(** val logeq_both_false : 'a1 neg -> 'a2 neg -> ('a1, 'a2) logeq **)

let logeq_both_false _ _ =
  { pr1 = (fun _ -> assert false (* absurd case *)); pr2 = (fun _ ->
    assert false (* absurd case *)) }

(** val logeq_trans :
    ('a1, 'a2) logeq -> ('a2, 'a3) logeq -> ('a1, 'a3) logeq **)

let logeq_trans i j =
  { pr1 = (funcomp i.pr1 j.pr1); pr2 = (funcomp j.pr2 i.pr2) }

(** val funcomp_assoc :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1 -> 'a4) paths **)

let funcomp_assoc _ _ _ =
  Coq_paths_refl

(** val uncurry_curry :
    (('a1, 'a3) total2 -> 'a2) -> ('a1, 'a3) total2 -> 'a2 paths **)

let uncurry_curry _ _ =
  Coq_paths_refl

(** val curry_uncurry : ('a1 -> 'a3 -> 'a2) -> 'a1 -> 'a3 -> 'a2 paths **)

let curry_uncurry _ _ _ =
  Coq_paths_refl

(** val pathscomp0 :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths **)

let pathscomp0 _ _ _ _ e2 =
  e2

(** val pathscomp0rid : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathscomp0rid _ _ _ =
  Coq_paths_refl

(** val pathsinv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths **)

let pathsinv0 _ _ _ =
  Coq_paths_refl

(** val path_assoc :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
    paths paths **)

let path_assoc _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pathsinv0l : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathsinv0l _ _ _ =
  Coq_paths_refl

(** val pathsinv0r : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathsinv0r _ _ _ =
  Coq_paths_refl

(** val pathsinv0inv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathsinv0inv0 _ _ _ =
  Coq_paths_refl

(** val pathscomp_cancel_left :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths
    paths -> 'a1 paths paths **)

let pathscomp_cancel_left _ _ _ _ _ _ e =
  e

(** val pathscomp_cancel_right :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths
    paths -> 'a1 paths paths **)

let pathscomp_cancel_right x y _ p q _ e =
  pathscomp0 p (pathscomp0 x y y p Coq_paths_refl) q
    (pathsinv0 (pathscomp0 x y y p Coq_paths_refl) p (pathscomp0rid x y p))
    (pathscomp0 (pathscomp0 x y y p Coq_paths_refl)
      (pathscomp0 x y y q Coq_paths_refl) q e (pathscomp0rid x y q))

(** val pathscomp_inv :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths **)

let pathscomp_inv _ _ _ _ _ =
  Coq_paths_refl

(** val pathsdirprod :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) dirprod
    paths **)

let pathsdirprod _ _ _ _ _ _ =
  Coq_paths_refl

(** val dirprodeq :
    ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths ->
    ('a1, 'a2) dirprod paths **)

let dirprodeq _ _ _ _ =
  Coq_paths_refl

(** val maponpaths : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths **)

let maponpaths _ _ _ _ =
  Coq_paths_refl

(** val map_on_two_paths :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths
    -> 'a3 paths **)

let map_on_two_paths _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val maponpathscomp0 :
    'a1 -> 'a1 -> 'a1 -> ('a1 -> 'a2) -> 'a1 paths -> 'a1 paths -> 'a2 paths
    paths **)

let maponpathscomp0 _ _ _ _ _ _ =
  Coq_paths_refl

(** val maponpathsinv0 :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths **)

let maponpathsinv0 _ _ _ _ =
  Coq_paths_refl

(** val maponpathsidfun : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let maponpathsidfun _ _ _ =
  Coq_paths_refl

(** val maponpathscomp :
    'a1 -> 'a1 -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 paths -> 'a3 paths paths **)

let maponpathscomp _ _ _ _ _ =
  Coq_paths_refl

type ('x, 'p) homot = 'x -> 'p paths

(** val homotrefl : ('a1 -> 'a2) -> ('a1, 'a2) homot **)

let homotrefl _ _ =
  Coq_paths_refl

(** val homotcomp :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1,
    'a2) homot -> ('a1, 'a2) homot **)

let homotcomp f f' f'' h h' x =
  pathscomp0 (f x) (f' x) (f'' x) (h x) (h' x)

(** val invhomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) homot **)

let invhomot f f' h x =
  pathsinv0 (f x) (f' x) (h x)

(** val funhomot :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
    'a3) homot **)

let funhomot f _ _ h x =
  h (f x)

(** val funhomotsec :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
    'a3) homot **)

let funhomotsec f _ _ h x =
  h (f x)

(** val homotfun :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a3) -> ('a1,
    'a3) homot **)

let homotfun f f' h g x =
  maponpaths g (f x) (f' x) (h x)

(** val toforallpaths :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot **)

let toforallpaths _ _ _ _ =
  Coq_paths_refl

(** val eqtohomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot **)

let eqtohomot _ _ _ _ =
  Coq_paths_refl

(** val maponpathshomidinv :
    ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths **)

let maponpathshomidinv f h x x' e =
  pathscomp0 x (f x) x' (pathsinv0 (f x) x (h x))
    (pathscomp0 (f x) (f x') x' e (h x'))

(** val maponpathshomid1 :
    ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1
    paths paths **)

let maponpathshomid1 f h x _ _ =
  pathsinv0 (pathscomp0 (f x) x (f x) (h x) (pathsinv0 (f x) x (h x)))
    Coq_paths_refl (pathsinv0r (f x) x (h x))

(** val maponpathshomid2 :
    ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1
    paths paths **)

let maponpathshomid2 f h x x' e =
  pathscomp0
    (maponpaths f x x'
      (pathscomp0 x (f x) x' (pathsinv0 (f x) x (h x))
        (pathscomp0 (f x) (f x') x' e (h x'))))
    (pathscomp0 (f x) x (f x') (h x)
      (pathscomp0 x x' (f x')
        (pathscomp0 x (f x) x' (pathsinv0 (f x) x (h x))
          (pathscomp0 (f x) (f x') x' e (h x'))) (pathsinv0 (f x') x' (h x'))))
    e
    (maponpathshomid1 f h x x'
      (pathscomp0 x (f x) x' (pathsinv0 (f x) x (h x))
        (pathscomp0 (f x) (f x') x' e (h x')))) Coq_paths_refl

(** val pathssec1 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a2 -> 'a2
    paths -> 'a1 paths **)

let pathssec1 s p eps x y e =
  pathscomp0 x (p (s x)) (p y) (pathsinv0 (p (s x)) x (eps x))
    (maponpaths p (s x) y e)

(** val pathssec2 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a2
    paths -> 'a1 paths **)

let pathssec2 s p eps x x' e =
  let e' = pathssec1 s p eps x (s x') e in
  pathscomp0 x (p (s x')) x' e' (eps x')

(** val pathssec2id :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 paths
    paths **)

let pathssec2id _ _ _ _ =
  Coq_paths_refl

(** val pathssec3 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1
    paths -> 'a1 paths paths **)

let pathssec3 s p eps x _ _ =
  pathssec2id s p eps x

(** val constr1 :
    'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2, ('a2 -> ('a1, 'a2) total2 paths,
    'a2 -> 'a1 paths paths) total2) total2 **)

let constr1 _ _ _ =
  { pr1 = idfun; pr2 = { pr1 = (fun _ -> Coq_paths_refl); pr2 = (fun _ ->
    Coq_paths_refl) } }

(** val transportf : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 **)

let transportf x x' e =
  (constr1 x x' e).pr1

(** val transportf_eq :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) total2 paths **)

let transportf_eq x x' e p =
  (constr1 x x' e).pr2.pr1 p

(** val transportb : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 **)

let transportb x x' e =
  transportf x' x (pathsinv0 x x' e)

(** val idpath_transportf : 'a1 -> 'a2 -> 'a2 paths **)

let idpath_transportf _ _ =
  Coq_paths_refl

(** val functtransportf :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths **)

let functtransportf _ _ _ _ _ =
  Coq_paths_refl

(** val functtransportb :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths **)

let functtransportb _ _ _ _ _ =
  Coq_paths_refl

(** val transport_f_b :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transport_f_b _ _ _ _ _ _ =
  Coq_paths_refl

(** val transport_b_f :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transport_b_f _ _ _ _ _ _ =
  Coq_paths_refl

(** val transport_f_f :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transport_f_f _ _ _ _ _ _ =
  Coq_paths_refl

(** val transport_b_b :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transport_b_b _ _ _ _ _ _ =
  Coq_paths_refl

(** val transport_map :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths **)

let transport_map _ _ _ _ _ =
  Coq_paths_refl

(** val transport_section :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths **)

let transport_section f x y e =
  transport_map (fun x0 _ -> f x0) x y e Coq_tt

(** val transportf_fun :
    'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) -> ('a3 -> 'a2) paths **)

let transportf_fun _ _ _ _ =
  Coq_paths_refl

(** val transportb_fun' :
    'a1 -> 'a1 -> ('a2 -> 'a3) -> 'a1 paths -> 'a2 -> 'a3 paths **)

let transportb_fun' _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths **)

let transportf_const _ _ _ =
  Coq_paths_refl

(** val transportb_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths **)

let transportb_const _ _ _ =
  Coq_paths_refl

(** val transportf_paths :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2
    paths **)

let transportf_paths _ _ _ _ _ _ =
  Coq_paths_refl

(** val transportbfinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transportbfinv _ _ _ _ =
  Coq_paths_refl

(** val transportfbinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transportfbinv _ _ _ _ =
  Coq_paths_refl

(** val base_paths :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a1
    paths **)

let base_paths a b x =
  maponpaths (fun t -> t.pr1) a b x

(** val two_arg_paths :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
    -> 'a3 paths **)

let two_arg_paths _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val two_arg_paths_f :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
    -> 'a3 paths **)

let two_arg_paths_f _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val two_arg_paths_b :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
    -> 'a3 paths **)

let two_arg_paths_b _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val dirprod_paths :
    ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths ->
    ('a1, 'a2) dirprod paths **)

let dirprod_paths s s' p q =
  let a = s.pr1 in
  let b = s.pr2 in
  let a' = s'.pr1 in
  let b' = s'.pr2 in
  two_arg_paths (fun x x0 -> { pr1 = x; pr2 = x0 }) a b a' b' p q

(** val total2_paths_f :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
    'a2) total2 paths **)

let total2_paths_f s s' p q =
  let a = s.pr1 in
  let b = s.pr2 in
  let a' = s'.pr1 in
  let b' = s'.pr2 in
  two_arg_paths_f (fun x x0 -> { pr1 = x; pr2 = x0 }) a b a' b' p q

(** val total2_paths_b :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
    'a2) total2 paths **)

let total2_paths_b s s' p q =
  let a = s.pr1 in
  let b = s.pr2 in
  let a' = s'.pr1 in
  let b' = s'.pr2 in
  two_arg_paths_b (fun x x0 -> { pr1 = x; pr2 = x0 }) a b a' b' p q

(** val total2_paths2 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
    paths **)

let total2_paths2 a1 a2 b1 b2 p q =
  two_arg_paths (fun x x0 -> { pr1 = x; pr2 = x0 }) a1 b1 a2 b2 p q

(** val total2_paths2_f :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
    paths **)

let total2_paths2_f a1 b1 a2 b2 p q =
  two_arg_paths_f (fun x x0 -> { pr1 = x; pr2 = x0 }) a1 b1 a2 b2 p q

(** val total2_paths2_b :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
    paths **)

let total2_paths2_b a1 b1 a2 b2 p q =
  two_arg_paths_b (fun x x0 -> { pr1 = x; pr2 = x0 }) a1 b1 a2 b2 p q

(** val pair_path_in2 :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) total2 paths **)

let pair_path_in2 x p q e =
  maponpaths (fun x0 -> { pr1 = x; pr2 = x0 }) p q e

(** val fiber_paths :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a2
    paths **)

let fiber_paths _ _ _ =
  Coq_paths_refl

(** val total2_fiber_paths :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths ->
    ('a1, 'a2) total2 paths paths **)

let total2_fiber_paths _ _ _ =
  Coq_paths_refl

(** val base_total2_paths :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a1
    paths paths **)

let base_total2_paths _ _ _ _ =
  Coq_paths_refl

(** val transportf_fiber_total2_paths :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a2
    paths paths **)

let transportf_fiber_total2_paths _ _ _ _ =
  Coq_paths_refl

(** val total2_base_map :
    ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2 **)

let total2_base_map f x =
  { pr1 = (f x.pr1); pr2 = x.pr2 }

(** val total2_section_path :
    'a1 -> 'a2 -> ('a1 -> 'a2) -> ('a1, 'a2) total2 paths -> 'a2 paths **)

let total2_section_path a b e p =
  pathscomp0 (e a)
    (transportf a a
      (base_paths { pr1 = a; pr2 = (e a) } { pr1 = a; pr2 = b } p) (e a)) b
    (pathsinv0
      (transportf a a
        (maponpaths (fun t -> t.pr1) { pr1 = a; pr2 = (e a) } { pr1 = a;
          pr2 = b } p) (e a)) (e a)
      (transport_section e a a
        (maponpaths (fun t -> t.pr1) { pr1 = a; pr2 = (e a) } { pr1 = a;
          pr2 = b } p)))
    (fiber_paths { pr1 = a; pr2 = (e a) } { pr1 = a; pr2 = b } p)

(** val transportD : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 **)

let transportD _ _ _ _ z =
  z

(** val transportf_total2 :
    'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 paths **)

let transportf_total2 _ _ _ _ =
  Coq_paths_refl

(** val transportf_dirprod :
    ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 ->
    'a1 paths -> ('a2, 'a3) dirprod paths **)

let transportf_dirprod _ _ _ =
  Coq_paths_refl

(** val transportb_dirprod :
    ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 ->
    'a1 paths -> ('a2, 'a3) dirprod paths **)

let transportb_dirprod x x' p =
  transportf_dirprod x' x (pathsinv0 x.pr1 x'.pr1 p)

(** val transportf_id1 :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths **)

let transportf_id1 _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_id2 :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths **)

let transportf_id2 _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_id3 :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths **)

let transportf_id3 x1 _ _ q =
  pathsinv0 (pathscomp0 x1 x1 x1 q Coq_paths_refl)
    (transportf x1 x1 Coq_paths_refl q)
    (pathscomp0rid x1 x1 (transportf x1 x1 Coq_paths_refl q))

(** val famhomotfun :
    ('a1, coq_UU) homot -> ('a1, 'a2) total2 -> ('a1, 'a3) total2 **)

let famhomotfun _ xp =
  { pr1 = xp.pr1; pr2 = (Obj.magic xp).pr2 }

(** val famhomothomothomot :
    ('a1, coq_UU) homot -> ('a1, coq_UU) homot -> ('a1, coq_UU paths) homot
    -> (('a1, 'a2) total2, ('a1, 'a3) total2) homot **)

let famhomothomothomot _ _ _ xp =
  maponpaths (fun q -> { pr1 = xp.pr1; pr2 = (Obj.magic q) }) xp.pr2 xp.pr2
    Coq_paths_refl

type 't iscontr = ('t, 't -> 't paths) total2

(** val make_iscontr : 'a1 -> ('a1 -> 'a1 paths) -> 'a1 iscontr **)

let make_iscontr x x0 =
  { pr1 = x; pr2 = x0 }

(** val iscontrpr1 : 'a1 iscontr -> 'a1 **)

let iscontrpr1 x =
  x.pr1

(** val iscontr_uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths **)

let iscontr_uniqueness i t =
  i.pr2 t

(** val iscontrretract :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 iscontr -> 'a2
    iscontr **)

let iscontrretract p s eps is =
  let x = iscontrpr1 is in
  let fe = is.pr2 in
  { pr1 = (p x); pr2 = (fun t ->
  pathscomp0 t (p (s t)) (p is.pr1) (pathsinv0 (p (s t)) t (eps t))
    (maponpaths p (s t) is.pr1 (fe (s t)))) }

(** val proofirrelevancecontr : 'a1 iscontr -> 'a1 -> 'a1 -> 'a1 paths **)

let proofirrelevancecontr is x x' =
  pathscomp0 x is.pr1 x' (is.pr2 x) (pathsinv0 x' is.pr1 (is.pr2 x'))

(** val path_to_ctr : ('a1, 'a2) total2 iscontr -> 'a1 -> 'a2 -> 'a1 paths **)

let path_to_ctr isc a p =
  let hi = { pr1 = a; pr2 = p } in
  maponpaths (fun t -> t.pr1) hi isc.pr1 (isc.pr2 hi)

type ('x, 'y) hfiber = ('x, 'y paths) total2

(** val make_hfiber :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber **)

let make_hfiber _ _ x e =
  { pr1 = x; pr2 = e }

(** val hfiberpr1 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a1 **)

let hfiberpr1 _ _ t =
  t.pr1

(** val hfiberpr2 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a2 paths **)

let hfiberpr2 _ _ y' =
  y'.pr2

(** val hfibershomotftog :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let hfibershomotftog f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  { pr1 = x; pr2 =
  (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e) }

(** val hfibershomotgtof :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let hfibershomotgtof f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in { pr1 = x; pr2 = (pathscomp0 (f x) (g x) y (h x) e) }

(** val hfibertriangle1 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1,
    'a2) hfiber paths -> 'a2 paths paths **)

let hfibertriangle1 _ _ _ _ _ =
  Coq_paths_refl

(** val hfibertriangle1' :
    ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths ->
    'a2 paths paths **)

let hfibertriangle1' f x xe1 e =
  pathscomp0 xe1.pr2
    (pathscomp0 (f xe1.pr1) (f x) (f x)
      (maponpaths f xe1.pr1 x
        (maponpaths (fun t -> t.pr1) xe1 { pr1 = x; pr2 = Coq_paths_refl } e))
      Coq_paths_refl)
    (maponpaths f xe1.pr1 x
      (maponpaths (fun t -> t.pr1) xe1 { pr1 = x; pr2 = Coq_paths_refl } e))
    (hfibertriangle1 f (f x) xe1 { pr1 = x; pr2 = Coq_paths_refl } e)
    (pathscomp0rid (f xe1.pr1) (f x)
      (maponpaths f xe1.pr1 x
        (maponpaths (fun t -> t.pr1) xe1 { pr1 = x; pr2 = Coq_paths_refl } e)))

(** val hfibertriangle1inv0 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1,
    'a2) hfiber paths -> 'a2 paths paths **)

let hfibertriangle1inv0 _ _ _ _ _ =
  Coq_paths_refl

(** val hfibertriangle1inv0' :
    ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2 paths) total2 paths
    -> 'a2 paths paths **)

let hfibertriangle1inv0' f x xe2 e =
  pathscomp0
    (maponpaths f xe2.pr1 x
      (pathsinv0 x xe2.pr1
        (maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = Coq_paths_refl } xe2 e)))
    (pathscomp0 (f xe2.pr1) (f x) (f x)
      (maponpaths f xe2.pr1 x
        (pathsinv0 x xe2.pr1
          (maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = Coq_paths_refl } xe2
            e))) Coq_paths_refl) xe2.pr2
    (pathsinv0
      (pathscomp0 (f xe2.pr1) (f x) (f x)
        (maponpaths f xe2.pr1 x
          (pathsinv0 x xe2.pr1
            (maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = Coq_paths_refl }
              xe2 e))) Coq_paths_refl)
      (maponpaths f xe2.pr1 x
        (pathsinv0 x xe2.pr1
          (maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = Coq_paths_refl } xe2
            e)))
      (pathscomp0rid (f xe2.pr1) (f x)
        (maponpaths f xe2.pr1 x
          (pathsinv0 x xe2.pr1
            (maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = Coq_paths_refl }
              xe2 e)))))
    (hfibertriangle1inv0 f (f x) { pr1 = x; pr2 = Coq_paths_refl } xe2 e)

(** val hfibertriangle2 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> 'a1
    paths -> 'a2 paths paths -> ('a1, 'a2) hfiber paths **)

let hfibertriangle2 f y xe1 xe2 _ eee =
  let t = xe1.pr1 in
  let e1 = xe1.pr2 in
  let e2 = xe2.pr2 in maponpaths (fun e -> make_hfiber f y t e) e1 e2 eee

type 't coconusfromt = ('t, 't paths) total2

(** val coconusfromtpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconusfromt **)

let coconusfromtpair _ t' e =
  { pr1 = t'; pr2 = e }

(** val coconusfromtpr1 : 'a1 -> 'a1 coconusfromt -> 'a1 **)

let coconusfromtpr1 _ t =
  t.pr1

type 't coconustot = ('t, 't paths) total2

(** val coconustotpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconustot **)

let coconustotpair _ t' e =
  { pr1 = t'; pr2 = e }

(** val coconustotpr1 : 'a1 -> 'a1 coconustot -> 'a1 **)

let coconustotpr1 _ t =
  t.pr1

(** val coconustot_isProofIrrelevant :
    'a1 -> 'a1 coconustot -> 'a1 coconustot -> 'a1 coconustot paths **)

let coconustot_isProofIrrelevant _ _ _ =
  Coq_paths_refl

(** val iscontrcoconustot : 'a1 -> 'a1 coconustot iscontr **)

let iscontrcoconustot t =
  { pr1 = { pr1 = t; pr2 = Coq_paths_refl }; pr2 = (fun _ -> Coq_paths_refl) }

(** val coconusfromt_isProofIrrelevant :
    'a1 -> 'a1 coconusfromt -> 'a1 coconusfromt -> 'a1 coconusfromt paths **)

let coconusfromt_isProofIrrelevant _ _ _ =
  Coq_paths_refl

(** val iscontrcoconusfromt : 'a1 -> 'a1 coconusfromt iscontr **)

let iscontrcoconusfromt t =
  { pr1 = { pr1 = t; pr2 = Coq_paths_refl }; pr2 = (fun _ -> Coq_paths_refl) }

type 't pathsspace = ('t, 't coconusfromt) total2

(** val pathsspacetriple : 'a1 -> 'a1 -> 'a1 paths -> 'a1 pathsspace **)

let pathsspacetriple t1 t2 e =
  { pr1 = t1; pr2 = (coconusfromtpair t1 t2 e) }

(** val deltap : 'a1 -> 'a1 pathsspace **)

let deltap t =
  pathsspacetriple t t Coq_paths_refl

type 't pathsspace' = (('t, 't) dirprod, 't paths) total2

type ('x, 'y) coconusf = ('y, ('x, 'y) hfiber) total2

(** val fromcoconusf : ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> 'a1 **)

let fromcoconusf _ yxe =
  yxe.pr2.pr1

(** val tococonusf : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) coconusf **)

let tococonusf f x =
  { pr1 = (f x); pr2 = (make_hfiber f (f x) x Coq_paths_refl) }

(** val homottofromcoconusf :
    ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> ('a1, 'a2) coconusf paths **)

let homottofromcoconusf _ _ =
  Coq_paths_refl

(** val homotfromtococonusf : ('a1 -> 'a2) -> 'a1 -> 'a1 paths **)

let homotfromtococonusf _ _ =
  Coq_paths_refl

type ('x, 'y) isweq = 'y -> ('x, 'y) hfiber iscontr

(** val idisweq : ('a1, 'a1) isweq **)

let idisweq y =
  { pr1 = (make_hfiber idfun y y Coq_paths_refl); pr2 = (fun _ ->
    Coq_paths_refl) }

type ('x, 'y) weq = ('x -> 'y, ('x, 'y) isweq) total2

(** val pr1weq : ('a1, 'a2) weq -> 'a1 -> 'a2 **)

let pr1weq x =
  x.pr1

(** val weqproperty : ('a1, 'a2) weq -> ('a1, 'a2) isweq **)

let weqproperty f =
  f.pr2

(** val weqccontrhfiber : ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber **)

let weqccontrhfiber w y =
  iscontrpr1 (weqproperty w y)

(** val weqccontrhfiber2 :
    ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths **)

let weqccontrhfiber2 w y x =
  (w.pr2 y).pr2 x

(** val make_weq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) weq **)

let make_weq f is =
  { pr1 = f; pr2 = is }

(** val idweq : ('a1, 'a1) weq **)

let idweq =
  { pr1 = (fun x -> x); pr2 = idisweq }

(** val isweqtoempty : ('a1 -> empty) -> ('a1, empty) isweq **)

let isweqtoempty _ =
  fromempty

(** val weqtoempty : ('a1 -> empty) -> ('a1, empty) weq **)

let weqtoempty f =
  make_weq f (isweqtoempty f)

(** val isweqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) isweq **)

let isweqtoempty2 _ _ _ =
  assert false (* absurd case *)

(** val weqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) weq **)

let weqtoempty2 f is =
  make_weq f (isweqtoempty2 f is)

(** val weqempty : 'a1 neg -> 'a2 neg -> ('a1, 'a2) weq **)

let weqempty nx ny =
  make_weq (fun x -> fromempty (nx x)) (fun y -> fromempty (ny y))

(** val invmap : ('a1, 'a2) weq -> 'a2 -> 'a1 **)

let invmap w y =
  hfiberpr1 (pr1weq w) y (weqccontrhfiber w y)

(** val homotweqinvweq : ('a1, 'a2) weq -> 'a2 -> 'a2 paths **)

let homotweqinvweq w y =
  (weqccontrhfiber w y).pr2

(** val homotinvweqweq0 : ('a1, 'a2) weq -> 'a1 -> 'a1 paths **)

let homotinvweqweq0 w x =
  let xe2 = make_hfiber (pr1weq w) (pr1weq w x) x Coq_paths_refl in
  let p = weqccontrhfiber2 w (pr1weq w x) xe2 in
  maponpaths (fun t -> t.pr1) xe2 (weqccontrhfiber w (pr1weq w x)) p

(** val homotinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a1 paths **)

let homotinvweqweq w x =
  pathsinv0 x (invmap w (pr1weq w x)) (homotinvweqweq0 w x)

(** val invmaponpathsweq :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths **)

let invmaponpathsweq w x x' =
  pathssec2 (pr1weq w) (invmap w) (homotinvweqweq w) x x'

(** val invmaponpathsweqid : ('a1, 'a2) weq -> 'a1 -> 'a1 paths paths **)

let invmaponpathsweqid w x =
  pathssec2id (pr1weq w) (invmap w) (homotinvweqweq w) x

(** val pathsweq1 : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths **)

let pathsweq1 w x y e =
  maponpaths (fun t -> t.pr1) { pr1 = x; pr2 = e } (weqproperty w y).pr1
    ((weqproperty w y).pr2 { pr1 = x; pr2 = e })

(** val pathsweq1' :
    ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths **)

let pathsweq1' w x y e =
  pathscomp0 (pr1weq w x) (pr1weq w (invmap w y)) y
    (maponpaths (pr1weq w) x (invmap w y) e) (homotweqinvweq w y)

(** val pathsweq3 :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathsweq3 w x x' e =
  pathssec3 (pr1weq w) (invmap w) (homotinvweqweq w) x x' e

(** val pathsweq4 :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths paths **)

let pathsweq4 w x x' e =
  let f = w.pr1 in
  let is1 = w.pr2 in
  let w0 = make_weq f is1 in
  let g = invmap w0 in
  let ee =
    maponpaths g (pr1weq { pr1 = f; pr2 = is1 } x)
      (pr1weq { pr1 = f; pr2 = is1 } x') e
  in
  let eee = maponpathshomidinv (funcomp f g) (homotinvweqweq w0) x x' ee in
  let e1 =
    let e2 = maponpathshomid2 (funcomp f g) (homotinvweqweq w0) x x' ee in
    let e3 =
      pathscomp0 (maponpaths g (f x) (f x') (maponpaths f x x' eee))
        (maponpaths (funcomp f g) x x' eee) ee (maponpathscomp x x' f g eee)
        e2
    in
    let s = maponpaths g (f x) (f x') in
    let p = pathssec2 g f (homotweqinvweq w0) (f x) (f x') in
    let eps = pathssec3 g f (homotweqinvweq w0) (f x) (f x') in
    pathssec2 s p eps (maponpaths f x x' eee) e e3
  in
  let e4 =
    maponpaths (fun e0 -> maponpaths f x x' (invmaponpathsweq w0 x x' e0))
      (maponpaths f x x' eee) e e1
  in
  let x0 = pathsweq3 w0 x x' eee in
  let e5 =
    maponpaths (fun eee0 -> maponpaths f x x' eee0)
      (invmaponpathsweq w0 x x' (maponpaths f x x' eee)) eee x0
  in
  pathscomp0 (maponpaths f x x' (invmaponpathsweq w0 x x' e))
    (maponpaths f x x' (invmaponpathsweq w0 x x' (maponpaths f x x' eee))) e
    (pathsinv0
      (maponpaths f x x' (invmaponpathsweq w0 x x' (maponpaths f x x' eee)))
      (maponpaths f x x' (invmaponpathsweq w0 x x' e)) e4)
    (pathscomp0
      (maponpaths f x x' (invmaponpathsweq w0 x x' (maponpaths f x x' eee)))
      (maponpaths f x x' eee) e e5 e1)

(** val homotweqinv :
    ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) homot ->
    ('a2, 'a3) homot **)

let homotweqinv f w g p y =
  pathscomp0 (f (invmap w y)) (funcomp (pr1weq w) g (invmap w y)) (g y)
    (p (invmap w y))
    (maponpaths g (pr1weq w (invmap w y)) y (homotweqinvweq w y))

(** val homotweqinv' :
    ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) homot ->
    ('a1, 'a3) homot **)

let homotweqinv' f w g q x =
  pathscomp0 (f x) (funcomp (invmap w) f (pr1weq w x)) (g (pr1weq w x))
    (maponpaths f x (invmap w (pr1weq w x))
      (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x)))
    (q (pr1weq w x))

(** val internal_paths_rew : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2 **)

let internal_paths_rew _ f _ _ =
  f

(** val internal_paths_rew_r : 'a1 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 **)

let internal_paths_rew_r _ _ hC _ =
  hC

(** val isinjinvmap :
    ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a1) homot -> ('a1, 'a2) homot **)

let isinjinvmap v w h x =
  pathscomp0 (pr1weq v x) (pr1weq w (invmap w (pr1weq v x))) (pr1weq w x)
    (pathsinv0 (pr1weq w (invmap w (pr1weq v x))) (pr1weq v x)
      (homotweqinvweq w (pr1weq v x)))
    (internal_paths_rew (invmap v (pr1weq v x))
      (internal_paths_rew_r (invmap v (pr1weq v x)) x Coq_paths_refl
        (homotinvweqweq v x)) (invmap w (pr1weq v x)) (h (pr1weq v x)))

(** val isinjinvmap' :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2,
    'a2) homot -> ('a1, 'a1) homot -> ('a2, 'a1) homot -> ('a1, 'a2) homot **)

let isinjinvmap' v w v' w' p q h x =
  pathscomp0 (v x) (w (w' (v x))) (w x)
    (pathsinv0 (w (w' (v x))) (v x) (p (v x)))
    (maponpaths w (w' (v x)) x
      (internal_paths_rew (v' (v x)) (q x) (w' (v x)) (h (v x))))

(** val diaglemma2 :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths
    -> 'a2 paths paths **)

let diaglemma2 _ _ _ _ _ ee =
  ee

(** val homotweqinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a2 paths paths **)

let homotweqinvweqweq w x =
  let hfid = make_hfiber (pr1weq w) (pr1weq w x) x Coq_paths_refl in
  let hfcc = weqccontrhfiber w (pr1weq w x) in
  diaglemma2 (pr1weq w) x (invmap w (pr1weq w x))
    (maponpaths (fun t -> t.pr1) hfid hfcc
      (weqccontrhfiber2 w (pr1weq w x) hfid))
    (weqccontrhfiber w (pr1weq w x)).pr2
    (hfibertriangle1 (pr1weq w) (pr1weq w x) hfid hfcc
      (weqccontrhfiber2 w (pr1weq w x) hfid))

(** val weq_transportf_adjointness :
    ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths **)

let weq_transportf_adjointness w x p =
  pathscomp0
    (transportf x (invmap w (pr1weq w x))
      (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x)) p)
    (transportf (pr1weq w x) (pr1weq w (invmap w (pr1weq w x)))
      (maponpaths (pr1weq w) x (invmap w (pr1weq w x))
        (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x))) p)
    (transportf (pr1weq w x) (pr1weq w (invmap w (pr1weq w x)))
      (pathsinv0 (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x)
        (homotweqinvweq w (pr1weq w x))) p)
    (functtransportf (pr1weq w) x (invmap w (pr1weq w x))
      (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x)) p)
    (maponpaths (fun e ->
      transportf (pr1weq w x) (pr1weq w (invmap w (pr1weq w x))) e p)
      (maponpaths (pr1weq w) x (invmap w (pr1weq w x))
        (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x)))
      (pathsinv0 (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x)
        (homotweqinvweq w (pr1weq w x)))
      (internal_paths_rew_r
        (maponpaths (pr1weq w) x (invmap w (pr1weq w x))
          (pathsinv0 (invmap w (pr1weq w x)) x (homotinvweqweq w x)))
        (pathsinv0 (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x)
          (maponpaths (pr1weq w) (invmap w (pr1weq w x)) x
            (homotinvweqweq w x)))
        (maponpaths
          (pathsinv0 (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x))
          (maponpaths (pr1weq w) (invmap w (pr1weq w x)) x
            (homotinvweqweq w x)) (homotweqinvweq w (pr1weq w x))
          (homotweqinvweqweq w x))
        (maponpathsinv0 (pr1weq w) (invmap w (pr1weq w x)) x
          (homotinvweqweq w x))))

(** val weq_transportb_adjointness :
    ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths **)

let weq_transportb_adjointness w x p =
  pathscomp0 (transportb (invmap w (pr1weq w x)) x (homotinvweqweq w x) p)
    (transportb (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x)
      (maponpaths (pr1weq w) (invmap w (pr1weq w x)) x (homotinvweqweq w x))
      p)
    (transportb (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x)
      (homotweqinvweq w (pr1weq w x)) p)
    (functtransportb (pr1weq w) x (invmap w (pr1weq w x))
      (homotinvweqweq w x) p)
    (maponpaths (fun e ->
      transportb (pr1weq w (invmap w (pr1weq w x))) (pr1weq w x) e p)
      (maponpaths (pr1weq w) (invmap w (pr1weq w x)) x (homotinvweqweq w x))
      (homotweqinvweq w (pr1weq w x)) (homotweqinvweqweq w x))

(** val isweqtransportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq **)

let isweqtransportf _ _ _ =
  idisweq

(** val isweqtransportb : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq **)

let isweqtransportb x x' e =
  isweqtransportf x' x (pathsinv0 x x' e)

(** val iscontrweqb : ('a1, 'a2) weq -> 'a2 iscontr -> 'a1 iscontr **)

let iscontrweqb w is =
  iscontrretract (invmap w) (pr1weq w) (homotinvweqweq w) is

(** val isProofIrrelevantUnit : coq_unit -> coq_unit -> coq_unit paths **)

let isProofIrrelevantUnit _ _ =
  Coq_paths_refl

(** val unitl0 : coq_unit paths -> coq_unit coconustot **)

let unitl0 e =
  coconustotpair Coq_tt Coq_tt e

(** val unitl1 : coq_unit coconustot -> coq_unit paths **)

let unitl1 cp =
  cp.pr2

(** val unitl2 : coq_unit paths -> coq_unit paths paths **)

let unitl2 _ =
  Coq_paths_refl

(** val unitl3 : coq_unit paths -> coq_unit paths paths **)

let unitl3 e =
  let e0 =
    coconustot_isProofIrrelevant Coq_tt (unitl0 Coq_paths_refl) (unitl0 e)
  in
  let e1 = maponpaths unitl1 (unitl0 Coq_paths_refl) (unitl0 e) e0 in
  pathscomp0 e (unitl1 (unitl0 e)) Coq_paths_refl
    (pathsinv0 (unitl1 (unitl0 e)) e (unitl2 e))
    (pathscomp0 (unitl1 (unitl0 e)) (unitl1 (unitl0 Coq_paths_refl))
      Coq_paths_refl
      (pathsinv0 (unitl1 (unitl0 Coq_paths_refl)) (unitl1 (unitl0 e)) e1)
      (unitl2 Coq_paths_refl))

(** val iscontrunit : coq_unit iscontr **)

let iscontrunit =
  { pr1 = Coq_tt; pr2 = (fun t -> isProofIrrelevantUnit t Coq_tt) }

(** val iscontrpathsinunit :
    coq_unit -> coq_unit -> coq_unit paths iscontr **)

let iscontrpathsinunit x x' =
  { pr1 = (isProofIrrelevantUnit x x'); pr2 = unitl3 }

(** val ifcontrthenunitl0 :
    coq_unit paths -> coq_unit paths -> coq_unit paths paths **)

let ifcontrthenunitl0 e1 e2 =
  proofirrelevancecontr (iscontrpathsinunit Coq_tt Coq_tt) e1 e2

(** val isweqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) isweq **)

let isweqcontrtounit is _ =
  let c = is.pr1 in
  let h = is.pr2 in
  let hc = make_hfiber (fun _ -> Coq_tt) Coq_tt c Coq_paths_refl in
  { pr1 = hc; pr2 = (fun ha ->
  let x = ha.pr1 in
  let e = ha.pr2 in
  two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 }) x e c Coq_paths_refl
    (h x) (ifcontrthenunitl0 (transportf x c (h x) e) Coq_paths_refl)) }

(** val weqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) weq **)

let weqcontrtounit is =
  make_weq (fun _ -> Coq_tt) (isweqcontrtounit is)

(** val iscontrifweqtounit : ('a1, coq_unit) weq -> 'a1 iscontr **)

let iscontrifweqtounit w =
  iscontrweqb w iscontrunit

(** val hfibersgftog :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a3) hfiber -> ('a2, 'a3)
    hfiber **)

let hfibersgftog f g z xe =
  make_hfiber g z (f xe.pr1) xe.pr2

(** val constr2 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a2, 'a1)
    hfiber -> (('a1, 'a1) hfiber, ('a2, 'a1) hfiber paths) total2 **)

let constr2 f g efg x0 xe =
  let y0 = xe.pr1 in
  let e = xe.pr2 in
  let eint = pathssec1 g f efg y0 x0 e in
  let ee =
    pathscomp0 (g (f x0)) (g y0) x0
      (pathsinv0 (g y0) (g (f x0)) (maponpaths g y0 (f x0) eint)) e
  in
  { pr1 = (make_hfiber (funcomp f g) x0 x0 ee); pr2 =
  (two_arg_paths_f (fun x x1 -> { pr1 = x; pr2 = x1 }) y0 e (f x0) ee eint
    Coq_paths_refl) }

(** val iscontrhfiberl1 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a1, 'a1)
    hfiber iscontr -> ('a2, 'a1) hfiber iscontr **)

let iscontrhfiberl1 f g efg x0 is =
  let f1 = hfibersgftog f g x0 in
  let g1 = fun xe -> (constr2 f g efg x0 xe).pr1 in
  let efg1 = fun xe ->
    pathsinv0 xe (hfibersgftog f g x0 (constr2 f g efg x0 xe).pr1)
      (constr2 f g efg x0 xe).pr2
  in
  iscontrretract f1 g1 efg1 is

(** val homothfiber1 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let homothfiber1 f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  make_hfiber g y x (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e)

(** val homothfiber2 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let homothfiber2 f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in make_hfiber f y x (pathscomp0 (f x) (g x) y (h x) e)

(** val homothfiberretr :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber paths **)

let homothfiberretr f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  let xe1 =
    make_hfiber g y x
      (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x))
        (pathscomp0 (f x) (g x) y (h x) e))
  in
  let xe2 = make_hfiber g y x e in
  hfibertriangle2 g y xe1 xe2 Coq_paths_refl Coq_paths_refl

(** val iscontrhfiberl2 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber iscontr -> ('a1, 'a2) hfiber iscontr **)

let iscontrhfiberl2 f g h y is =
  let a = homothfiber1 f g h y in
  let b = homothfiber2 f g h y in
  let eab = homothfiberretr f g h y in iscontrretract a b eab is

(** val isweqhomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isweq ->
    ('a1, 'a2) isweq **)

let isweqhomot f1 f2 h x0 y =
  iscontrhfiberl2 f1 f2 h y (x0 y)

(** val remakeweq :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) weq **)

let remakeweq f g e =
  { pr1 = g; pr2 = (isweqhomot (pr1weq f) g e (weqproperty f)) }

(** val remakeweq_eq :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1 -> 'a2) paths **)

let remakeweq_eq _ _ _ =
  Coq_paths_refl

(** val remakeweq_eq' :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a1) paths **)

let remakeweq_eq' _ _ _ =
  Coq_paths_refl

(** val iscontr_move_point : 'a1 -> 'a1 iscontr -> 'a1 iscontr **)

let iscontr_move_point x i =
  { pr1 = x; pr2 = (fun y -> proofirrelevancecontr i y x) }

(** val iscontr_move_point_eq : 'a1 -> 'a1 iscontr -> 'a1 paths **)

let iscontr_move_point_eq _ _ =
  Coq_paths_refl

(** val remakeweqinv :
    ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1, 'a2) weq **)

let remakeweqinv f h e =
  { pr1 = (pr1weq f); pr2 = (fun y ->
    let p = { pr1 = (h y); pr2 =
      (pathsweq1' f (h y) y (pathsinv0 (invmap f y) (h y) (e y))) }
    in
    iscontr_move_point p (weqproperty f y)) }

(** val remakeweqinv_eq :
    ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1 -> 'a2) paths **)

let remakeweqinv_eq _ _ _ =
  Coq_paths_refl

(** val remakeweqinv_eq' :
    ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a2 -> 'a1) paths **)

let remakeweqinv_eq' _ _ _ =
  Coq_paths_refl

(** val remakeweqboth :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot ->
    ('a2, 'a1) homot -> ('a1, 'a2) weq **)

let remakeweqboth f g h r s =
  remakeweqinv (remakeweq f g r) h s

(** val remakeweqboth_eq :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot ->
    ('a2, 'a1) homot -> ('a1 -> 'a2) paths **)

let remakeweqboth_eq _ _ _ _ _ =
  Coq_paths_refl

(** val remakeweqboth_eq' :
    ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot ->
    ('a2, 'a1) homot -> ('a2 -> 'a1) paths **)

let remakeweqboth_eq' _ _ _ _ _ =
  Coq_paths_refl

(** val isweqhomot_iff :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> (('a1, 'a2) isweq,
    ('a1, 'a2) isweq) logeq **)

let isweqhomot_iff f1 f2 h =
  { pr1 = (isweqhomot f1 f2 h); pr2 = (isweqhomot f2 f1 (invhomot f1 f2 h)) }

(** val isweq_to_isweq_unit :
    ('a1 -> coq_unit) -> ('a1 -> coq_unit) -> ('a1, coq_unit) isweq -> ('a1,
    coq_unit) isweq **)

let isweq_to_isweq_unit f g i =
  let h = fun t -> isProofIrrelevantUnit (f t) (g t) in isweqhomot f g h i

(** val isweq_iso :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths)
    -> ('a1, 'a2) isweq **)

let isweq_iso f g egf efg y =
  let x0 =
    let efg' = fun y0 -> pathsinv0 (f (g y0)) y0 (efg y0) in
    iscontrhfiberl2 idfun (funcomp g f) efg' y (idisweq y)
  in
  iscontrhfiberl1 g f egf y x0

(** val weq_iso :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths)
    -> ('a1, 'a2) weq **)

let weq_iso f g egf efg =
  make_weq f (isweq_iso f g egf efg)

type ('x, 'y) coq_UniqueConstruction =
  ('y -> ('x, 'y paths) total2, 'x -> 'x -> 'y paths -> 'x paths) dirprod

(** val coq_UniqueConstruction_to_weq :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> ('a1, 'a2) isweq **)

let coq_UniqueConstruction_to_weq f bij =
  let sur = bij.pr1 in
  let inj = bij.pr2 in
  isweq_iso f (fun y -> (sur y).pr1) (fun x ->
    inj (sur (f x)).pr1 x (sur (f x)).pr2) (fun y -> (sur y).pr2)

(** val isweqinvmap : ('a1, 'a2) weq -> ('a2, 'a1) isweq **)

let isweqinvmap w =
  let efg = homotweqinvweq w in
  let egf = homotinvweqweq w in isweq_iso (invmap w) (pr1weq w) efg egf

(** val invweq : ('a1, 'a2) weq -> ('a2, 'a1) weq **)

let invweq w =
  make_weq (invmap w) (isweqinvmap w)

(** val invinv : ('a1, 'a2) weq -> 'a1 -> 'a2 paths **)

let invinv _ _ =
  Coq_paths_refl

(** val pr1_invweq : ('a1, 'a2) weq -> ('a2 -> 'a1) paths **)

let pr1_invweq _ =
  Coq_paths_refl

(** val iscontrweqf : ('a1, 'a2) weq -> 'a1 iscontr -> 'a2 iscontr **)

let iscontrweqf w is =
  iscontrweqb (invweq w) is

type ('a, 'b) coq_PathPair = ('a paths, 'b paths) total2

(** val total2_paths_equiv :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
    'a2) coq_PathPair) weq **)

let total2_paths_equiv x y =
  { pr1 = (fun r -> { pr1 = (base_paths x y r); pr2 = (fiber_paths x y r) });
    pr2 =
    (isweq_iso (fun r -> { pr1 = (base_paths x y r); pr2 =
      (fiber_paths x y r) }) (fun pq -> total2_paths_f x y pq.pr1 pq.pr2)
      (fun p -> total2_fiber_paths x y p) (fun y0 ->
      let p = y0.pr1 in
      let q = y0.pr2 in
      two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 })
        (base_paths x y (total2_paths_f x y p q))
        (fiber_paths x y (total2_paths_f x y p q)) p q
        (base_total2_paths x y p q) (transportf_fiber_total2_paths x y p q))) }

(** val wequnittocontr : 'a1 iscontr -> (coq_unit, 'a1) weq **)

let wequnittocontr is =
  let f = fun _ -> is.pr1 in
  let g = fun _ -> Coq_tt in
  { pr1 = f; pr2 =
  (let egf = fun _ -> Coq_paths_refl in
   let efg = fun x -> pathsinv0 x is.pr1 (is.pr2 x) in isweq_iso f g egf efg) }

(** val isweqmaponpaths :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) isweq **)

let isweqmaponpaths w x x' =
  isweq_iso (maponpaths (pr1weq w) x x') (invmaponpathsweq w x x')
    (pathsweq3 w x x') (pathsweq4 w x x')

(** val weqonpaths :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) weq **)

let weqonpaths w x x' =
  make_weq (maponpaths (pr1weq w) x x') (isweqmaponpaths w x x')

(** val isweqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) isweq **)

let isweqpathsinv0 x y p =
  { pr1 = { pr1 = (pathsinv0 y x p); pr2 = (pathsinv0inv0 y x p) }; pr2 =
    (fun _ -> Coq_paths_refl) }

(** val weqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) weq **)

let weqpathsinv0 x x' =
  make_weq (pathsinv0 x x') (isweqpathsinv0 x x')

(** val isweqpathscomp0r :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq **)

let isweqpathscomp0r x x' x'' e' =
  let f = fun e -> pathscomp0 x x' x'' e e' in
  let g = fun e'' -> pathscomp0 x x'' x' e'' (pathsinv0 x' x'' e') in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in isweq_iso f g egf efg

(** val isweqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) isweq **)

let isweqtococonusf f =
  isweq_iso (tococonusf f) (fromcoconusf f) (homotfromtococonusf f)
    (homottofromcoconusf f)

(** val weqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) weq **)

let weqtococonusf f =
  make_weq (tococonusf f) (isweqtococonusf f)

(** val isweqfromcoconusf :
    ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) isweq **)

let isweqfromcoconusf f =
  isweq_iso (fromcoconusf f) (tococonusf f) (homottofromcoconusf f)
    (homotfromtococonusf f)

(** val weqfromcoconusf : ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) weq **)

let weqfromcoconusf f =
  make_weq (fromcoconusf f) (isweqfromcoconusf f)

(** val isweqdeltap : ('a1, 'a1 pathsspace) isweq **)

let isweqdeltap y =
  let gg = fun z -> z.pr1 in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in isweq_iso deltap gg egf efg y

(** val isweqpr1pr1 : ('a1 pathsspace', 'a1) isweq **)

let isweqpr1pr1 y =
  let f = fun a -> a.pr1.pr1 in
  let g = fun t -> { pr1 = (make_dirprod t t); pr2 = Coq_paths_refl } in
  let efg = fun _ -> Coq_paths_refl in
  let egf = fun _ -> Coq_paths_refl in isweq_iso f g egf efg y

(** val weqhfibershomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> (('a1, 'a2)
    hfiber, ('a1, 'a2) hfiber) weq **)

let weqhfibershomot f g h y =
  let ff = hfibershomotftog f g h y in
  let gg = hfibershomotgtof f g h y in
  { pr1 = ff; pr2 =
  (let effgg = fun xe ->
     let x = xe.pr1 in
     let e = xe.pr2 in
     let eee = Coq_paths_refl in
     let xe1 =
       make_hfiber g y x
         (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x))
           (pathscomp0 (f x) (g x) y (h x) e))
     in
     let xe2 = make_hfiber g y x e in
     hfibertriangle2 g y xe1 xe2 Coq_paths_refl eee
   in
   let eggff = fun xe ->
     let x = xe.pr1 in
     let e = xe.pr2 in
     let eee = Coq_paths_refl in
     let xe1 =
       make_hfiber f y x
         (pathscomp0 (f x) (g x) y (h x)
           (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e))
     in
     let xe2 = make_hfiber f y x e in
     hfibertriangle2 f y xe1 xe2 Coq_paths_refl eee
   in
   isweq_iso ff gg eggff effgg) }

(** val twooutof3a :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isweq -> ('a2, 'a3) isweq ->
    ('a1, 'a2) isweq **)

let twooutof3a f g isgf isg =
  let gw = make_weq g isg in
  let gfw = make_weq (funcomp f g) isgf in
  let invgf = invmap gfw in
  let invf = funcomp g invgf in
  let efinvf = fun y ->
    let int1 = homotweqinvweq gfw (g y) in
    invmaponpathsweq gw (f (invf y)) y int1
  in
  let einvff = fun x -> homotinvweqweq gfw x in isweq_iso f invf einvff efinvf

(** val twooutof3b :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isweq ->
    ('a2, 'a3) isweq **)

let twooutof3b f g isf isgf =
  let wf = make_weq f isf in
  let wgf = make_weq (funcomp f g) isgf in
  let invf = invmap wf in
  let invgf = invmap wgf in
  let invg = funcomp invgf f in
  let eginvg = fun z -> homotweqinvweq wgf z in
  let einvgg = fun y ->
    let isinvf = isweqinvmap wf in
    let int5 = homotinvweqweq wf (invgf (g y)) in
    invmaponpathsweq (make_weq invf isinvf) (funcomp invgf f (g y)) y int5
  in
  isweq_iso g invg einvgg eginvg

(** val isweql3 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1, 'a2) isweq ->
    ('a2, 'a1) isweq **)

let isweql3 f g egf w =
  let int1 =
    isweqhomot idfun (funcomp f g) (fun x -> pathsinv0 (g (f x)) x (egf x))
      idisweq
  in
  twooutof3b f g w int1

(** val twooutof3c :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a2, 'a3) isweq ->
    ('a1, 'a3) isweq **)

let twooutof3c f g isf isg =
  let wf = make_weq f isf in
  let wg = make_weq g isg in
  let invf = invmap wf in
  let invg = invmap wg in
  let gf = funcomp f g in
  let invgf = funcomp invg invf in
  let egfinvgf = fun x -> homotinvweqweq wf x in
  let einvgfgf = fun z -> homotweqinvweq wg z in
  isweq_iso gf invgf egfinvgf einvgfgf

(** val twooutof3c_iff_2 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> (('a2, 'a3) isweq,
    ('a1, 'a3) isweq) logeq **)

let twooutof3c_iff_2 f g i =
  { pr1 = (fun j -> twooutof3c f g i j); pr2 = (fun j -> twooutof3b f g i j) }

(** val twooutof3c_iff_1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isweq -> (('a1, 'a2) isweq,
    ('a1, 'a3) isweq) logeq **)

let twooutof3c_iff_1 f g i =
  { pr1 = (fun j -> twooutof3c f g j i); pr2 = (fun j -> twooutof3a f g j i) }

(** val twooutof3c_iff_1_homot :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a2,
    'a3) isweq -> (('a1, 'a2) isweq, ('a1, 'a3) isweq) logeq **)

let twooutof3c_iff_1_homot f g h r i =
  logeq_trans (twooutof3c_iff_1 f g i) (isweqhomot_iff (funcomp f g) h r)

(** val twooutof3c_iff_2_homot :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a1,
    'a2) isweq -> (('a2, 'a3) isweq, ('a1, 'a3) isweq) logeq **)

let twooutof3c_iff_2_homot f g h r i =
  logeq_trans (twooutof3c_iff_2 f g i) (isweqhomot_iff (funcomp f g) h r)

(** val isweqcontrcontr :
    ('a1 -> 'a2) -> 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) isweq **)

let isweqcontrcontr f isx isy =
  let py = fun _ -> Coq_tt in
  twooutof3a f py (isweqcontrtounit isx) (isweqcontrtounit isy)

(** val weqcontrcontr : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq **)

let weqcontrcontr isx isy =
  make_weq (fun _ -> isy.pr1) (isweqcontrcontr (fun _ -> isy.pr1) isx isy)

(** val weqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq **)

let weqcomp w1 w2 =
  make_weq (fun x -> pr1weq w2 (pr1weq w1 x))
    (twooutof3c (pr1weq w1) (pr1weq w2) w1.pr2 w2.pr2)

(** val weqcomp_to_funcomp_app :
    'a1 -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a3 paths **)

let weqcomp_to_funcomp_app _ _ _ =
  Coq_paths_refl

(** val weqcomp_to_funcomp :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1 -> 'a3) paths **)

let weqcomp_to_funcomp _ _ =
  Coq_paths_refl

(** val invmap_weqcomp_expand :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths **)

let invmap_weqcomp_expand _ _ =
  Coq_paths_refl

(** val twooutofsixu :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
    'a4) isweq -> ('a1, 'a2) isweq **)

let twooutofsixu u v w isuv isvw =
  let invuv = invmap (make_weq (funcomp u v) isuv) in
  let pu = funcomp v invuv in
  let hupu = homotinvweqweq (make_weq (funcomp u v) isuv) in
  let invvw = invmap (make_weq (funcomp v w) isvw) in
  let pv = funcomp w invvw in
  let hvpv = homotinvweqweq (make_weq (funcomp v w) isvw) in
  let h0 =
    funhomot v (fun y ->
      pr1weq (make_weq (funcomp u v) isuv)
        (invmap (make_weq (funcomp u v) isuv) y)) (fun y -> y)
      (homotweqinvweq (make_weq (funcomp u v) isuv))
  in
  let h1 =
    funhomot (funcomp pu u) idfun (funcomp v pv)
      (invhomot (funcomp v pv) idfun hvpv)
  in
  let h2 =
    homotfun
      (funcomp v (fun y ->
        pr1weq (make_weq (funcomp u v) isuv)
          (invmap (make_weq (funcomp u v) isuv) y))) (funcomp v (fun y -> y))
      h0 pv
  in
  let hpuu =
    homotcomp (funcomp (funcomp pu u) idfun)
      (funcomp (funcomp v (fun y -> y)) pv) idfun
      (homotcomp (funcomp (funcomp pu u) idfun)
        (funcomp (funcomp pu u) (funcomp v pv))
        (funcomp (funcomp v (fun y -> y)) pv) h1 h2) hvpv
  in
  isweq_iso u pu hupu hpuu

(** val twooutofsixv :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
    'a4) isweq -> ('a2, 'a3) isweq **)

let twooutofsixv u v w isuv isvw =
  twooutof3b u v (twooutofsixu u v w isuv isvw) isuv

(** val twooutofsixw :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
    'a4) isweq -> ('a3, 'a4) isweq **)

let twooutofsixw u v w isuv isvw =
  twooutof3b v w (twooutofsixv u v w isuv isvw) isvw

(** val isweqdirprodf :
    ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
    dirprod) isweq **)

let isweqdirprodf w w' =
  let f = dirprodf (pr1weq w) (pr1weq w') in
  let g = dirprodf (pr1weq (invweq w)) (pr1weq (invweq w')) in
  let egf = fun a ->
    let x = a.pr1 in
    let x' = a.pr2 in
    pathsdirprod (pr1weq (invweq w) (f { pr1 = x; pr2 = x' }).pr1) x
      (pr1weq (invweq w') (f { pr1 = x; pr2 = x' }).pr2) x'
      (homotinvweqweq w x) (homotinvweqweq w' x')
  in
  let efg = fun a ->
    let x = a.pr1 in
    let x' = a.pr2 in
    pathsdirprod (pr1weq w (g { pr1 = x; pr2 = x' }).pr1) x
      (pr1weq w' (g { pr1 = x; pr2 = x' }).pr2) x' (homotweqinvweq w x)
      (homotweqinvweq w' x')
  in
  isweq_iso f g egf efg

(** val weqdirprodf :
    ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
    dirprod) weq **)

let weqdirprodf w w' =
  make_weq (dirprodf (pr1weq w) (pr1weq w')) (isweqdirprodf w w')

(** val weqtodirprodwithunit : ('a1, ('a1, coq_unit) dirprod) weq **)

let weqtodirprodwithunit =
  let f = fun x -> make_dirprod x Coq_tt in
  { pr1 = f; pr2 =
  (let g = fun xu -> xu.pr1 in
   let egf = fun _ -> Coq_paths_refl in
   let efg = fun _ -> Coq_paths_refl in isweq_iso f g egf efg) }

(** val total2asstor :
    (('a1, 'a2) total2, 'a3) total2 -> ('a1, ('a2, 'a3) total2) total2 **)

let total2asstor xpq =
  { pr1 = xpq.pr1.pr1; pr2 = { pr1 = xpq.pr1.pr2; pr2 = xpq.pr2 } }

(** val total2asstol :
    ('a1, ('a2, 'a3) total2) total2 -> (('a1, 'a2) total2, 'a3) total2 **)

let total2asstol xpq =
  { pr1 = { pr1 = xpq.pr1; pr2 = xpq.pr2.pr1 }; pr2 = xpq.pr2.pr2 }

(** val weqtotal2asstor :
    ((('a1, 'a2) total2, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq **)

let weqtotal2asstor =
  { pr1 = total2asstor; pr2 =
    (let egf = fun _ -> Coq_paths_refl in
     let efg = fun _ -> Coq_paths_refl in
     isweq_iso total2asstor total2asstol egf efg) }

(** val weqtotal2asstol :
    (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq **)

let weqtotal2asstol =
  invweq weqtotal2asstor

(** val weqdirprodasstor :
    ((('a1, 'a2) dirprod, 'a3) dirprod, ('a1, ('a2, 'a3) dirprod) dirprod) weq **)

let weqdirprodasstor =
  weqtotal2asstor

(** val weqdirprodasstol :
    (('a1, ('a2, 'a3) dirprod) dirprod, (('a1, 'a2) dirprod, 'a3) dirprod) weq **)

let weqdirprodasstol =
  invweq weqdirprodasstor

(** val weqdirprodcomm : (('a1, 'a2) dirprod, ('a2, 'a1) dirprod) weq **)

let weqdirprodcomm =
  let f = fun xy -> make_dirprod xy.pr2 xy.pr1 in
  let g = fun yx -> make_dirprod yx.pr2 yx.pr1 in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in
  { pr1 = f; pr2 = (isweq_iso f g egf efg) }

(** val weqtotal2dirprodcomm :
    ((('a1, 'a2) dirprod, 'a3) total2, (('a2, 'a1) dirprod, 'a3) total2) weq **)

let weqtotal2dirprodcomm =
  weq_iso (fun xyp -> { pr1 = { pr1 = xyp.pr1.pr2; pr2 = xyp.pr1.pr1 }; pr2 =
    xyp.pr2 }) (fun yxp -> { pr1 = { pr1 = yxp.pr1.pr2; pr2 = yxp.pr1.pr1 };
    pr2 = yxp.pr2 }) (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val weqtotal2dirprodassoc :
    ((('a1, 'a2) dirprod, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq **)

let weqtotal2dirprodassoc =
  weq_iso (fun xyp -> { pr1 = xyp.pr1.pr1; pr2 = { pr1 = xyp.pr1.pr2; pr2 =
    xyp.pr2 } }) (fun xyp -> { pr1 = { pr1 = xyp.pr1; pr2 = xyp.pr2.pr1 };
    pr2 = xyp.pr2.pr2 }) (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val weqtotal2dirprodassoc' :
    ((('a1, 'a2) dirprod, 'a3) total2, ('a2, ('a1, 'a3) total2) total2) weq **)

let weqtotal2dirprodassoc' =
  weq_iso (fun xyp -> { pr1 = xyp.pr1.pr2; pr2 = { pr1 = xyp.pr1.pr1; pr2 =
    xyp.pr2 } }) (fun yxp -> { pr1 = { pr1 = yxp.pr2.pr1; pr2 = yxp.pr1 };
    pr2 = yxp.pr2.pr2 }) (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val weqtotal2comm12 :
    ((('a1, 'a2) total2, 'a3) total2, (('a1, 'a3) total2, 'a2) total2) weq **)

let weqtotal2comm12 =
  weq_iso (fun xpq -> { pr1 = { pr1 = xpq.pr1.pr1; pr2 = xpq.pr2 }; pr2 =
    xpq.pr1.pr2 }) (fun xqp -> { pr1 = { pr1 = xqp.pr1.pr1; pr2 = xqp.pr2 };
    pr2 = xqp.pr1.pr2 }) (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val rdistrtocoprod :
    ('a1, ('a2, 'a3) coprod) dirprod -> (('a1, 'a2) dirprod, ('a1, 'a3)
    dirprod) coprod **)

let rdistrtocoprod x0 =
  let t = x0.pr1 in
  let x = x0.pr2 in
  (match x with
   | Coq_ii1 a -> Coq_ii1 (make_dirprod t a)
   | Coq_ii2 b -> Coq_ii2 (make_dirprod t b))

(** val rdistrtoprod :
    (('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod -> ('a1, ('a2, 'a3)
    coprod) dirprod **)

let rdistrtoprod = function
| Coq_ii1 a -> let t = a.pr1 in let x = a.pr2 in make_dirprod t (Coq_ii1 x)
| Coq_ii2 b -> let t = b.pr1 in let x = b.pr2 in make_dirprod t (Coq_ii2 x)

(** val isweqrdistrtoprod :
    ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3)
    coprod) dirprod) isweq **)

let isweqrdistrtoprod y =
  let egf = fun a ->
    match a with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun a ->
    let x = a.pr2 in
    (match x with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> Coq_paths_refl)
  in
  isweq_iso rdistrtoprod rdistrtocoprod egf efg y

(** val weqrdistrtoprod :
    ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3)
    coprod) dirprod) weq **)

let weqrdistrtoprod =
  make_weq rdistrtoprod isweqrdistrtoprod

(** val isweqrdistrtocoprod :
    (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3)
    dirprod) coprod) isweq **)

let isweqrdistrtocoprod y =
  isweqinvmap weqrdistrtoprod y

(** val weqrdistrtocoprod :
    (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3)
    dirprod) coprod) weq **)

let weqrdistrtocoprod =
  make_weq rdistrtocoprod isweqrdistrtocoprod

(** val fromtotal2overcoprod :
    (('a1, 'a2) coprod, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3) total2)
    coprod **)

let fromtotal2overcoprod xyp =
  let xy = xyp.pr1 in
  let p = xyp.pr2 in
  (match xy with
   | Coq_ii1 a -> Coq_ii1 { pr1 = a; pr2 = p }
   | Coq_ii2 b -> Coq_ii2 { pr1 = b; pr2 = p })

(** val tototal2overcoprod :
    (('a1, 'a3) total2, ('a2, 'a3) total2) coprod -> (('a1, 'a2) coprod, 'a3)
    total2 **)

let tototal2overcoprod = function
| Coq_ii1 a ->
  let x = a.pr1 in let p = a.pr2 in { pr1 = (Coq_ii1 x); pr2 = p }
| Coq_ii2 b ->
  let y = b.pr1 in let p = b.pr2 in { pr1 = (Coq_ii2 y); pr2 = p }

(** val weqtotal2overcoprod :
    ((('a1, 'a2) coprod, 'a3) total2, (('a1, 'a3) total2, ('a2, 'a3) total2)
    coprod) weq **)

let weqtotal2overcoprod =
  { pr1 = fromtotal2overcoprod; pr2 =
    (let egf = fun a ->
       let xy = a.pr1 in
       (match xy with
        | Coq_ii1 _ -> Coq_paths_refl
        | Coq_ii2 _ -> Coq_paths_refl)
     in
     let efg = fun a ->
       match a with
       | Coq_ii1 _ -> Coq_paths_refl
       | Coq_ii2 _ -> Coq_paths_refl
     in
     isweq_iso fromtotal2overcoprod tototal2overcoprod egf efg) }

(** val sumofmaps :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3 **)

let sumofmaps fx fy = function
| Coq_ii1 x -> fx x
| Coq_ii2 y -> fy y

(** val coprodasstor :
    (('a1, 'a2) coprod, 'a3) coprod -> ('a1, ('a2, 'a3) coprod) coprod **)

let coprodasstor = function
| Coq_ii1 a ->
  (match a with
   | Coq_ii1 a0 -> Coq_ii1 a0
   | Coq_ii2 b -> Coq_ii2 (Coq_ii1 b))
| Coq_ii2 b -> Coq_ii2 (Coq_ii2 b)

(** val coprodasstol :
    ('a1, ('a2, 'a3) coprod) coprod -> (('a1, 'a2) coprod, 'a3) coprod **)

let coprodasstol = function
| Coq_ii1 a -> Coq_ii1 (Coq_ii1 a)
| Coq_ii2 b ->
  (match b with
   | Coq_ii1 a -> Coq_ii1 (Coq_ii2 a)
   | Coq_ii2 b0 -> Coq_ii2 b0)

(** val sumofmaps_assoc_left :
    ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> (('a1, ('a2, 'a3) coprod)
    coprod, 'a4) homot **)

let sumofmaps_assoc_left _ _ _ _ =
  Coq_paths_refl

(** val sumofmaps_assoc_right :
    ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> ((('a1, 'a2) coprod, 'a3)
    coprod, 'a4) homot **)

let sumofmaps_assoc_right _ _ _ _ =
  Coq_paths_refl

(** val isweqcoprodasstor :
    ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) isweq **)

let isweqcoprodasstor y =
  let egf = fun xyz ->
    match xyz with
    | Coq_ii1 a ->
      (match a with
       | Coq_ii1 _ -> Coq_paths_refl
       | Coq_ii2 _ -> Coq_paths_refl)
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun xyz ->
    match xyz with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 b ->
      (match b with
       | Coq_ii1 _ -> Coq_paths_refl
       | Coq_ii2 _ -> Coq_paths_refl)
  in
  isweq_iso coprodasstor coprodasstol egf efg y

(** val weqcoprodasstor :
    ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) weq **)

let weqcoprodasstor =
  make_weq coprodasstor isweqcoprodasstor

(** val isweqcoprodasstol :
    (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) isweq **)

let isweqcoprodasstol y =
  isweqinvmap weqcoprodasstor y

(** val weqcoprodasstol :
    (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) weq **)

let weqcoprodasstol =
  make_weq coprodasstol isweqcoprodasstol

(** val coprodcomm : ('a1, 'a2) coprod -> ('a2, 'a1) coprod **)

let coprodcomm = function
| Coq_ii1 x -> Coq_ii2 x
| Coq_ii2 y -> Coq_ii1 y

(** val isweqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) isweq **)

let isweqcoprodcomm y =
  let egf = fun xy ->
    match xy with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun yx ->
    match yx with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 _ -> Coq_paths_refl
  in
  isweq_iso coprodcomm coprodcomm egf efg y

(** val weqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) weq **)

let weqcoprodcomm =
  make_weq coprodcomm isweqcoprodcomm

(** val isweqii1withneg : ('a2 -> empty) -> ('a1, ('a1, 'a2) coprod) isweq **)

let isweqii1withneg nf =
  let f = fun x -> Coq_ii1 x in
  let g = fun xy ->
    match xy with
    | Coq_ii1 x -> x
    | Coq_ii2 y -> fromempty (nf y)
  in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun xy ->
    match xy with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 b -> fromempty (nf b)
  in
  isweq_iso f g egf efg

(** val weqii1withneg : 'a2 neg -> ('a1, ('a1, 'a2) coprod) weq **)

let weqii1withneg nf =
  make_weq (fun x -> Coq_ii1 x) (isweqii1withneg nf)

(** val isweqii2withneg : ('a1 -> empty) -> ('a2, ('a1, 'a2) coprod) isweq **)

let isweqii2withneg nf =
  let f = fun x -> Coq_ii2 x in
  let g = fun xy ->
    match xy with
    | Coq_ii1 x -> fromempty (nf x)
    | Coq_ii2 y -> y
  in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun xy ->
    match xy with
    | Coq_ii1 a -> fromempty (nf a)
    | Coq_ii2 _ -> Coq_paths_refl
  in
  isweq_iso f g egf efg

(** val weqii2withneg : 'a1 neg -> ('a2, ('a1, 'a2) coprod) weq **)

let weqii2withneg nf =
  make_weq (fun x -> Coq_ii2 x) (isweqii2withneg nf)

(** val coprodf :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) coprod -> ('a3, 'a4) coprod **)

let coprodf f g = function
| Coq_ii1 x -> Coq_ii1 (f x)
| Coq_ii2 y -> Coq_ii2 (g y)

(** val coprodf1 : ('a1 -> 'a3) -> ('a1, 'a2) coprod -> ('a3, 'a2) coprod **)

let coprodf1 f =
  coprodf f idfun

(** val coprodf2 : ('a2 -> 'a3) -> ('a1, 'a2) coprod -> ('a1, 'a3) coprod **)

let coprodf2 g =
  coprodf idfun g

(** val homotcoprodfcomp :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3 -> 'a5) -> ('a4 -> 'a6) -> (('a1,
    'a2) coprod, ('a5, 'a6) coprod) homot **)

let homotcoprodfcomp _ _ _ _ _ =
  Coq_paths_refl

(** val homotcoprodfhomot :
    ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a2 -> 'a4) -> ('a1,
    'a3) homot -> ('a2, 'a4) homot -> (('a1, 'a2) coprod, ('a3, 'a4) coprod)
    homot **)

let homotcoprodfhomot f g f' g' h h' = function
| Coq_ii1 x -> maponpaths (fun x0 -> Coq_ii1 x0) (f x) (g x) (h x)
| Coq_ii2 x' -> maponpaths (fun x -> Coq_ii2 x) (f' x') (g' x') (h' x')

(** val isweqcoprodf :
    ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4)
    coprod) isweq **)

let isweqcoprodf w w' =
  let finv = invmap w in
  let ginv = invmap w' in
  let ff = coprodf (pr1weq w) (pr1weq w') in
  let gg = coprodf finv ginv in
  let egf = fun xy ->
    match xy with
    | Coq_ii1 a ->
      maponpaths (fun x -> Coq_ii1 x) (invmap w (pr1weq w a)) a
        (homotinvweqweq w a)
    | Coq_ii2 b ->
      maponpaths (fun x -> Coq_ii2 x) (invmap w' (pr1weq w' b)) b
        (homotinvweqweq w' b)
  in
  let efg = fun xy' ->
    match xy' with
    | Coq_ii1 a ->
      maponpaths (fun x -> Coq_ii1 x) (pr1weq w (invmap w a)) a
        (homotweqinvweq w a)
    | Coq_ii2 b ->
      maponpaths (fun x -> Coq_ii2 x) (pr1weq w' (invmap w' b)) b
        (homotweqinvweq w' b)
  in
  isweq_iso ff gg egf efg

(** val weqcoprodf :
    ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4)
    coprod) weq **)

let weqcoprodf w1 w2 =
  make_weq (coprodf (pr1weq w1) (pr1weq w2)) (isweqcoprodf w1 w2)

(** val weqcoprodf1 :
    ('a1, 'a3) weq -> (('a1, 'a2) coprod, ('a3, 'a2) coprod) weq **)

let weqcoprodf1 w =
  weqcoprodf w idweq

(** val weqcoprodf2 :
    ('a2, 'a3) weq -> (('a1, 'a2) coprod, ('a1, 'a3) coprod) weq **)

let weqcoprodf2 w =
  weqcoprodf idweq w

type ('p, 'q) equality_cases = __

(** val equality_by_case :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths ->
    ('a1, 'a2) equality_cases **)

let equality_by_case x x' e =
  match x with
  | Coq_ii1 a ->
    (match x' with
     | Coq_ii1 a0 ->
       Obj.magic maponpaths (fun c ->
         match c with
         | Coq_ii1 a1 -> a1
         | Coq_ii2 _ -> a) (Coq_ii1 a) (Coq_ii1 a0) e
     | Coq_ii2 b -> transportf (Coq_ii1 a) (Coq_ii2 b) e (Obj.magic Coq_tt))
  | Coq_ii2 b ->
    (match x' with
     | Coq_ii1 a -> transportb (Coq_ii2 b) (Coq_ii1 a) e (Obj.magic Coq_tt)
     | Coq_ii2 b0 ->
       Obj.magic maponpaths (fun c ->
         match c with
         | Coq_ii1 _ -> b
         | Coq_ii2 b1 -> b1) (Coq_ii2 b) (Coq_ii2 b0) e)

(** val inv_equality_by_case :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
    ('a1, 'a2) coprod paths **)

let inv_equality_by_case x x' e =
  match x with
  | Coq_ii1 a ->
    (match x' with
     | Coq_ii1 a0 -> maponpaths (fun x0 -> Coq_ii1 x0) a a0 (Obj.magic e)
     | Coq_ii2 _ -> assert false (* absurd case *))
  | Coq_ii2 b ->
    (match x' with
     | Coq_ii1 _ -> assert false (* absurd case *)
     | Coq_ii2 b0 -> maponpaths (fun x0 -> Coq_ii2 x0) b b0 (Obj.magic e))

(** val ii1_injectivity :
    'a1 -> 'a1 -> ('a1, 'a2) coprod paths -> 'a1 paths **)

let ii1_injectivity p p' =
  Obj.magic equality_by_case (Coq_ii1 p) (Coq_ii1 p')

(** val ii2_injectivity :
    'a2 -> 'a2 -> ('a1, 'a2) coprod paths -> 'a2 paths **)

let ii2_injectivity q q' =
  Obj.magic equality_by_case (Coq_ii2 q) (Coq_ii2 q')

(** val negpathsii1ii2 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg **)

let negpathsii1ii2 x y =
  Obj.magic equality_by_case (Coq_ii1 x) (Coq_ii2 y)

(** val negpathsii2ii1 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg **)

let negpathsii2ii1 x y =
  Obj.magic equality_by_case (Coq_ii2 y) (Coq_ii1 x)

(** val boolascoprod : ((coq_unit, coq_unit) coprod, bool) weq **)

let boolascoprod =
  let f = fun xx ->
    match xx with
    | Coq_ii1 _ -> Coq_true
    | Coq_ii2 _ -> Coq_false
  in
  { pr1 = f; pr2 =
  (let g = fun t ->
     match t with
     | Coq_true -> Coq_ii1 Coq_tt
     | Coq_false -> Coq_ii2 Coq_tt
   in
   let egf = fun xx ->
     match xx with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> Coq_paths_refl
   in
   let efg = fun t ->
     match t with
     | Coq_true -> Coq_paths_refl
     | Coq_false -> Coq_paths_refl
   in
   isweq_iso f g egf efg) }

(** val coprodtobool : ('a1, 'a2) coprod -> bool **)

let coprodtobool = function
| Coq_ii1 _ -> Coq_true
| Coq_ii2 _ -> Coq_false

type ('x, 'y) boolsumfun = __

(** val coprodtoboolsum :
    ('a1, 'a2) coprod -> (bool, ('a1, 'a2) boolsumfun) total2 **)

let coprodtoboolsum = function
| Coq_ii1 x -> { pr1 = Coq_true; pr2 = (Obj.magic x) }
| Coq_ii2 y -> { pr1 = Coq_false; pr2 = (Obj.magic y) }

(** val boolsumtocoprod :
    (bool, ('a1, 'a2) boolsumfun) total2 -> ('a1, 'a2) coprod **)

let boolsumtocoprod xy =
  let pr3 = xy.pr1 in
  let y = xy.pr2 in
  (match pr3 with
   | Coq_true -> Coq_ii1 (Obj.magic y)
   | Coq_false -> Coq_ii2 (Obj.magic y))

(** val isweqcoprodtoboolsum :
    (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) isweq **)

let isweqcoprodtoboolsum y =
  let egf = fun xy ->
    match xy with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun xy ->
    let t = xy.pr1 in
    (match t with
     | Coq_true -> Coq_paths_refl
     | Coq_false -> Coq_paths_refl)
  in
  isweq_iso coprodtoboolsum boolsumtocoprod egf efg y

(** val weqcoprodtoboolsum :
    (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) weq **)

let weqcoprodtoboolsum =
  make_weq coprodtoboolsum isweqcoprodtoboolsum

(** val isweqboolsumtocoprod :
    ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) isweq **)

let isweqboolsumtocoprod y =
  isweqinvmap weqcoprodtoboolsum y

(** val weqboolsumtocoprod :
    ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) weq **)

let weqboolsumtocoprod =
  make_weq boolsumtocoprod isweqboolsumtocoprod

(** val weqcoprodsplit :
    ('a1 -> ('a2, 'a3) coprod) -> ('a1, (('a2, ('a1, ('a2, 'a3) coprod)
    hfiber) total2, ('a3, ('a1, ('a2, 'a3) coprod) hfiber) total2) coprod) weq **)

let weqcoprodsplit f =
  let w1 = weqtococonusf f in weqcomp w1 weqtotal2overcoprod

(** val boolchoice : bool -> (bool paths, bool paths) coprod **)

let boolchoice = function
| Coq_true -> Coq_ii1 Coq_paths_refl
| Coq_false -> Coq_ii2 Coq_paths_refl

type bool_to_type = __

(** val nopathstruetofalse : bool paths -> empty **)

let nopathstruetofalse x =
  transportf Coq_true Coq_false x (Obj.magic Coq_tt)

(** val nopathsfalsetotrue : bool paths -> empty **)

let nopathsfalsetotrue x =
  transportb Coq_false Coq_true x (Obj.magic Coq_tt)

(** val truetonegfalse : bool -> bool paths -> bool paths neg **)

let truetonegfalse x e =
  internal_paths_rew_r x Coq_true nopathstruetofalse e

(** val falsetonegtrue : bool -> bool paths -> bool paths neg **)

let falsetonegtrue x e =
  internal_paths_rew_r x Coq_false nopathsfalsetotrue e

(** val negtruetofalse : bool -> bool paths neg -> bool paths **)

let negtruetofalse x _ =
  let c = boolchoice x in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 b -> b)

(** val negfalsetotrue : bool -> bool paths neg -> bool paths **)

let negfalsetotrue x _ =
  let c = boolchoice x in
  (match c with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val onefiber :
    'a1 -> ('a1 -> ('a1 paths, 'a2 neg) coprod) -> ('a2, ('a1, 'a2) total2)
    isweq **)

let onefiber x c =
  let f = fun p -> { pr1 = x; pr2 = p } in
  let cx = c x in
  let cnew = fun x' ->
    match cx with
    | Coq_ii1 a ->
      (match c x' with
       | Coq_ii1 a0 -> Coq_ii1 (pathscomp0 x x x' (pathsinv0 x x a) a0)
       | Coq_ii2 b -> Coq_ii2 b)
    | Coq_ii2 _ -> c x'
  in
  let efg = fun pp ->
    let t = pp.pr1 in
    let x0 = pp.pr2 in
    let cnewt = cnew t in
    (match cnewt with
     | Coq_ii1 a ->
       pathsinv0 { pr1 = t; pr2 = x0 } { pr1 = x; pr2 =
         ((constr1 t x (pathsinv0 x t a)).pr1 x0) }
         ((constr1 t x (pathsinv0 x t a)).pr2.pr1 x0)
     | Coq_ii2 _ -> assert false (* absurd case *))
  in
  let e1 = Coq_paths_refl in
  (match cx with
   | Coq_ii1 a ->
     let cnew0 = fun x' ->
       match c x' with
       | Coq_ii1 a0 -> Coq_ii1 (pathscomp0 x x x' (pathsinv0 x x a) a0)
       | Coq_ii2 b -> Coq_ii2 b
     in
     let g = fun pp ->
       match cnew0 pp.pr1 with
       | Coq_ii1 e -> transportb x pp.pr1 e pp.pr2
       | Coq_ii2 phi -> fromempty (phi pp.pr2)
     in
     let cnewx = Coq_ii1 (pathscomp0 x x x (pathsinv0 x x a) a) in
     let e =
       maponpaths (fun x0 -> Coq_ii1 x0)
         (pathscomp0 x x x (pathsinv0 x x a) a) Coq_paths_refl
         (pathsinv0l x x a)
     in
     let egf = fun p ->
       let ff = fun cc ->
         match cc with
         | Coq_ii1 e0 -> transportb x x e0 p
         | Coq_ii2 phi -> fromempty (phi p)
       in
       let ee = maponpaths ff cnewx (Coq_ii1 Coq_paths_refl) e in
       let eee = Coq_paths_refl in
       let e2 = maponpaths ff (cnew0 x) cnewx e1 in
       pathscomp0 (ff (cnew0 x)) (ff (Coq_ii1 Coq_paths_refl)) p
         (pathscomp0 (ff (cnew0 x)) (ff cnewx) (ff (Coq_ii1 Coq_paths_refl))
           e2 ee) eee
     in
     isweq_iso f g egf efg
   | Coq_ii2 _ -> (fun _ -> assert false (* absurd case *)))

type ('x, 'y, 'z) complxstr = 'x -> 'z paths

(** val ezmap :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a1
    -> ('a2, 'a3) hfiber **)

let ezmap f g z ez x =
  make_hfiber g z (f x) (ez x)

type ('x, 'y, 'z) isfibseq = ('x, ('y, 'z) hfiber) isweq

type ('x, 'y, 'z) fibseqstr =
  (('x, 'y, 'z) complxstr, ('x, 'y, 'z) isfibseq) total2

(** val make_fibseqstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> ('a1,
    'a2, 'a3) isfibseq -> (('a1, 'a2, 'a3) complxstr, ('a1, 'a2, 'a3)
    isfibseq) total2 **)

let make_fibseqstr _ _ _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val fibseqstrtocomplxstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
    'a2, 'a3) complxstr **)

let fibseqstrtocomplxstr _ _ _ t =
  t.pr1

(** val ezweq :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
    ('a2, 'a3) hfiber) weq **)

let ezweq f g z fs =
  make_weq (ezmap f g z fs.pr1) fs.pr2

(** val d1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a3 paths -> 'a1 **)

let d1 f g z fs y e =
  invmap (ezweq f g z fs) (make_hfiber g z y e)

(** val ezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a3 paths -> ('a1, 'a2) hfiber **)

let ezmap1 f g z fs y e =
  { pr1 = (d1 f g z fs y e); pr2 =
    (maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e))) }

(** val invezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a2
    -> ('a1, 'a2) hfiber -> 'a3 paths **)

let invezmap1 f g z ez y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  pathscomp0 (g y) (g (f x)) z (maponpaths g y (f x) (pathsinv0 (f x) y e))
    (ez x)

(** val isweqezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, ('a1, 'a2) hfiber) isweq **)

let isweqezmap1 f g z fs y =
  let ff = ezmap1 f g z fs y in
  let gg = invezmap1 f g z fs.pr1 y in
  let egf = fun e ->
    hfibertriangle1inv0 g z
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e))
  in
  let efg = fun xe ->
    let x = xe.pr1 in
    let gg0 = invezmap1 f g z fs.pr1 (f x) in
    hfibertriangle2 f (f x)
      (make_hfiber f (f x)
        (invmap (ezweq f g z fs)
          (ezmap f g z (fibseqstrtocomplxstr f g z fs) x))
        (maponpaths (hfiberpr1 g z)
          (pr1weq (ezweq f g z fs)
            (invmap (ezweq f g z fs)
              (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl }))))
          (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl }))
          (homotweqinvweq (ezweq f g z fs)
            (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl })))))
      (make_hfiber f (f x) x Coq_paths_refl)
      (homotinvweqweq (ezweq f g z fs) x)
      (let e1 =
         pathsinv0
           (pathscomp0
             (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
             (f x) (f x)
             (maponpaths f
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x)) Coq_paths_refl)
           (maponpaths f
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (homotinvweqweq (ezweq f g z fs) x))
           (pathscomp0rid
             (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
             (f x)
             (maponpaths f
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x)))
       in
       let e2 =
         let e3 =
           maponpaths (fun e ->
             maponpaths (hfiberpr1 g z)
               (pr1weq (ezweq f g z fs)
                 (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)))
               (pr1weq (ezweq f g z fs) x) e)
             (homotweqinvweq (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
             (maponpaths (pr1weq (ezweq f g z fs))
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x))
             (pathsinv0
               (maponpaths (pr1weq (ezweq f g z fs))
                 (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
                 (homotinvweqweq (ezweq f g z fs) x))
               (homotweqinvweq (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
               (homotweqinvweqweq (ezweq f g z fs) x))
         in
         let e4 =
           maponpathscomp
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (ezmap f g z fs.pr1) (hfiberpr1 g z)
             (homotinvweqweq (ezweq f g z fs) x)
         in
         pathscomp0
           (maponpaths (hfiberpr1 g z)
             (ezmap f g z fs.pr1
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
             (ezmap f g z fs.pr1 x)
             (homotweqinvweq (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
           (maponpaths (hfiberpr1 g z)
             (ezmap f g z fs.pr1
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
             (ezmap f g z fs.pr1 x)
             (maponpaths (ezmap f g z fs.pr1)
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)) x
               (homotinvweqweq (ezweq f g z fs) x)))
           (maponpaths (funcomp (ezmap f g z fs.pr1) (hfiberpr1 g z))
             (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)) x
             (homotinvweqweq (ezweq f g z fs) x)) e3 e4
       in
       pathscomp0
         (maponpaths (hfiberpr1 g z)
           (pr1weq (ezweq f g z fs)
             (invmap (ezweq f g z fs)
               (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)))
           (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)
           (homotweqinvweq (ezweq f g z fs)
             (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)))
         (maponpaths f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
           x (homotinvweqweq (ezweq f g z fs) x))
         (pathscomp0
           (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
           (f x) (f x)
           (maponpaths f
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (homotinvweqweq (ezweq f g z fs) x)) Coq_paths_refl) e2 e1)
  in
  isweq_iso ff gg egf efg

(** val ezweq1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, ('a1, 'a2) hfiber) weq **)

let ezweq1 f g z fs y =
  make_weq (ezmap1 f g z fs y) (isweqezmap1 f g z fs y)

(** val fibseq1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, 'a1, 'a2) fibseqstr **)

let fibseq1 f g z fs y =
  make_fibseqstr (d1 f g z fs y) f y (fun e ->
    maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e)))
    (isweqezmap1 f g z fs y)

(** val d2 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a1 -> 'a2 paths -> 'a3 paths **)

let d2 f g z fs y x e =
  pathscomp0 (g y) (g (f x)) z (maponpaths g y (f x) (pathsinv0 (f x) y e))
    (fs.pr1 x)

(** val ezweq2 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a1 -> ('a2 paths, ('a3 paths, 'a1) hfiber) weq **)

let ezweq2 f g z fs y x =
  ezweq1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x

(** val fibseq2 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a1 -> ('a2 paths, 'a3 paths, 'a1) fibseqstr **)

let fibseq2 f g z fs y x =
  make_fibseqstr (d1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x)
    (d1 f g z fs y) x (fun e ->
    maponpaths (hfiberpr1 f y)
      (pr1weq (ezweq (d1 f g z fs y) f y (fibseq1 f g z fs y))
        (invmap (ezweq (d1 f g z fs y) f y (fibseq1 f g z fs y))
          (make_hfiber f y x e))) (make_hfiber f y x e)
      (homotweqinvweq (ezweq (d1 f g z fs y) f y (fibseq1 f g z fs y))
        (make_hfiber f y x e)))
    (isweqezmap1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x)

(** val ezmappr1 : 'a1 -> 'a2 -> (('a1, 'a2) total2, 'a1) hfiber **)

let ezmappr1 z p =
  { pr1 = { pr1 = z; pr2 = p }; pr2 = Coq_paths_refl }

(** val invezmappr1 : 'a1 -> (('a1, 'a2) total2, 'a1) hfiber -> 'a2 **)

let invezmappr1 z te =
  transportf te.pr1.pr1 z te.pr2 te.pr1.pr2

(** val isweqezmappr1 :
    'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) isweq **)

let isweqezmappr1 z =
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in
  isweq_iso (ezmappr1 z) (invezmappr1 z) egf efg

(** val ezweqpr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) weq **)

let ezweqpr1 z =
  make_weq (ezmappr1 z) (isweqezmappr1 z)

(** val isfibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) isfibseq **)

let isfibseqpr1 =
  isweqezmappr1

(** val fibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) fibseqstr **)

let fibseqpr1 z =
  make_fibseqstr (fun p -> { pr1 = z; pr2 = p }) (fun t -> t.pr1) z (fun _ ->
    Coq_paths_refl) (isfibseqpr1 z)

(** val ezweq1pr1 :
    'a1 -> ('a1, 'a2) total2 -> ('a1 paths, ('a2, ('a1, 'a2) total2) hfiber)
    weq **)

let ezweq1pr1 z zp =
  ezweq1 (fun p -> { pr1 = z; pr2 = p }) (fun t -> t.pr1) z (fibseqpr1 z) zp

(** val isfibseqg :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) isfibseq **)

let isfibseqg g z =
  isweqhomot idfun (ezmap (hfiberpr1 g z) g z (fun ye -> ye.pr2)) (fun _ ->
    Coq_paths_refl) idisweq

(** val ezweqg :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, ('a1, 'a2) hfiber) weq **)

let ezweqg g z =
  make_weq (ezmap (hfiberpr1 g z) g z (fun ye -> ye.pr2)) (isfibseqg g z)

(** val fibseqg :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) fibseqstr **)

let fibseqg g z =
  make_fibseqstr (hfiberpr1 g z) g z (fun ye -> ye.pr2) (isfibseqg g z)

(** val d1g : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber **)

let d1g =
  make_hfiber

(** val ezweq1g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, (('a1, 'a2) hfiber, 'a1)
    hfiber) weq **)

let ezweq1g g z y =
  make_weq (ezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)
    (isweqezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)

(** val fibseq1g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, ('a1, 'a2) hfiber, 'a1)
    fibseqstr **)

let fibseq1g g z y =
  make_fibseqstr (d1 (hfiberpr1 g z) g z (fibseqg g z) y) (hfiberpr1 g z) y
    (fun e ->
    maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq (hfiberpr1 g z) g z (fibseqg g z))
        (invmap (ezweq (hfiberpr1 g z) g z (fibseqg g z))
          (make_hfiber g z y e))) (make_hfiber g z y e)
      (homotweqinvweq (ezweq (hfiberpr1 g z) g z (fibseqg g z))
        (make_hfiber g z y e)))
    (isweqezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)

(** val d2g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a1 paths -> 'a2 paths **)

let d2g g z y ye' e =
  pathscomp0 (g y) (g ye'.pr1) z
    (maponpaths g y ye'.pr1 (pathsinv0 ye'.pr1 y e)) ye'.pr2

(** val ezweq2g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, ('a2
    paths, ('a1, 'a2) hfiber) hfiber) weq **)

let ezweq2g g z y ye' =
  ezweq2 (hfiberpr1 g z) g z (fibseqg g z) y ye'

(** val fibseq2g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, 'a2 paths,
    ('a1, 'a2) hfiber) fibseqstr **)

let fibseq2g g z y ye' =
  fibseq2 (hfiberpr1 g z) g z (fibseqg g z) y ye'

(** val d3g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1,
    'a2) hfiber paths -> 'a1 paths **)

let d3g g z y ye' e =
  d2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e

(** val homotd3g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1,
    'a2) hfiber paths -> 'a1 paths paths **)

let homotd3g g z y ye' e ee =
  pathscomp0rid ye'.pr1 y
    (maponpaths (fun t -> t.pr1) ye' (make_hfiber g z y e)
      (pathsinv0 (make_hfiber g z y e) ye' ee))

(** val ezweq3g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1,
    'a2) hfiber paths, ('a1 paths, 'a2 paths) hfiber) weq **)

let ezweq3g g z y ye' e =
  ezweq2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e

(** val fibseq3g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1,
    'a2) hfiber paths, 'a1 paths, 'a2 paths) fibseqstr **)

let fibseq3g g z y ye' e =
  fibseq2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e

(** val hfibersftogf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
    hfiber -> ('a1, 'a3) hfiber **)

let hfibersftogf f g z ye xe =
  { pr1 = xe.pr1; pr2 =
    (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
      (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2) }

(** val ezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
    hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber **)

let ezmaphf f g z ye xe =
  { pr1 = (hfibersftogf f g z ye xe); pr2 =
    (hfibertriangle2 g z
      (make_hfiber g z (f xe.pr1)
        (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
          (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2)) ye xe.pr2
      Coq_paths_refl) }

(** val invezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> ('a1, 'a2) hfiber **)

let invezmaphf f g z ye xee' =
  { pr1 = xee'.pr1.pr1; pr2 =
    (maponpaths (hfiberpr1 g z) (hfibersgftog f g z xee'.pr1) ye xee'.pr2) }

(** val ffgg :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) hfiber **)

let ffgg f g _ ye xee' =
  let y = ye.pr1 in
  let xe = xee'.pr1 in
  let e' = xee'.pr2 in
  let x = xe.pr1 in
  let e = xe.pr2 in
  let e'' =
    maponpaths g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e))
      (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })
      (maponpaths (hfiberpr1 g (g y)) (make_hfiber g (g y) (f x) e) { pr1 =
        y; pr2 = Coq_paths_refl } e')
  in
  { pr1 =
  (make_hfiber (funcomp f g) (g y) x
    (pathscomp0 (g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e)))
      (g (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })) (g y) e''
      Coq_paths_refl)); pr2 =
  (hfibertriangle2 g (g y)
    (make_hfiber g (g y) (f x)
      (pathscomp0 (g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e)))
        (g (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })) (g y) e''
        Coq_paths_refl)) (make_hfiber g (g y) y Coq_paths_refl)
    (maponpaths (hfiberpr1 g (g y)) (make_hfiber g (g y) (f x) e) { pr1 = y;
      pr2 = Coq_paths_refl } e') Coq_paths_refl) }

(** val homotffggid :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) hfiber paths **)

let homotffggid _ _ _ _ _ =
  Coq_paths_refl

(** val isweqezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) isweq **)

let isweqezmaphf f g z ye =
  let ff = ezmaphf f g z ye in
  let gg = invezmaphf f g z ye in
  let egf =
    let y = ye.pr1 in
    let ff0 = ezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    let gg0 = invezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    (fun xe ->
    hfibertriangle2 f y (gg0 (ff0 xe)) xe Coq_paths_refl Coq_paths_refl)
  in
  let efg =
    let y = ye.pr1 in
    let ff0 = ezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    let gg0 = invezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    (fun xee' ->
    let hint = Coq_paths_refl in
    pathscomp0 (ff0 (gg0 xee'))
      (ffgg f g (g y) (make_hfiber g (g y) y Coq_paths_refl) xee') xee' hint
      (homotffggid f g (g y) { pr1 = y; pr2 = Coq_paths_refl } xee'))
  in
  isweq_iso ff gg egf efg

(** val ezweqhf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) weq **)

let ezweqhf f g z ye =
  make_weq (ezmaphf f g z ye) (isweqezmaphf f g z ye)

(** val fibseqhf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, ('a1, 'a3) hfiber, ('a2, 'a3) hfiber) fibseqstr **)

let fibseqhf f g z ye =
  make_fibseqstr (hfibersftogf f g z ye) (hfibersgftog f g z) ye (fun xe ->
    hfibertriangle2 g z
      (make_hfiber g z (f xe.pr1)
        (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
          (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2)) ye xe.pr2
      Coq_paths_refl) (isweqezmaphf f g z ye)

(** val isweqinvezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ((('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber, ('a1, 'a2) hfiber) isweq **)

let isweqinvezmaphf f g z ye =
  (invweq (ezweqhf f g z ye)).pr2

(** val weqhfibersgwtog :
    ('a1, 'a2) weq -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) weq **)

let weqhfibersgwtog w g z =
  { pr1 = (hfibersgftog (pr1weq w) g z); pr2 = (fun ye ->
    iscontrweqf (ezweqhf (pr1weq w) g z ye) (w.pr2 ye.pr1)) }

(** val totalfun :
    ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> ('a1, 'a3) total2 **)

let totalfun f z =
  { pr1 = z.pr1; pr2 = (f z.pr1 z.pr2) }

(** val isweqtotaltofib :
    ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq ->
    'a1 -> ('a2, 'a3) isweq **)

let isweqtotaltofib f x0 x =
  let totf = totalfun f in
  let piq = fun z -> z.pr1 in
  let hfx = hfibersgftog totf piq x in
  let h = fun y ->
    let x1 = isweqinvezmaphf totf piq x y in
    let t = y.pr1 in
    let e = y.pr2 in
    let int = invezmaphf totf piq x { pr1 = t; pr2 = e } in
    let is1 = x0 t in iscontrweqb (make_weq int x1) is1
  in
  let ip = ezmappr1 x in
  let iq = ezmappr1 x in
  let h0 = fun p -> hfx (ip p) in
  let is2 = twooutof3c ip hfx (isweqezmappr1 x) h in
  let h' = fun p -> iq (f x p) in
  let ee = fun _ -> Coq_paths_refl in
  let x2 = isweqhomot h0 h' ee is2 in twooutof3a (f x) iq x2 (isweqezmappr1 x)

(** val weqtotaltofib :
    ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq ->
    'a1 -> ('a2, 'a3) weq **)

let weqtotaltofib f is x =
  make_weq (f x) (isweqtotaltofib f is x)

(** val isweqfibtototal :
    ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq **)

let isweqfibtototal f =
  let fpq = totalfun (fun x -> pr1weq (f x)) in
  let pr1q = fun z -> z.pr1 in
  (fun xq ->
  let x = pr1q xq in
  let xqe = make_hfiber pr1q (pr1q xq) xq Coq_paths_refl in
  let hfpqx = hfibersgftog fpq pr1q x in
  let isint =
    let ipx = ezmappr1 x in
    let iqx = ezmappr1 x in
    let is2 = twooutof3c (pr1weq (f x)) iqx (f x).pr2 (isweqezmappr1 x) in
    twooutof3b ipx hfpqx (isweqezmappr1 x) is2 xqe
  in
  let intmap = invezmaphf fpq pr1q x xqe in
  iscontrweqf (make_weq intmap (isweqinvezmaphf fpq pr1q x xqe)) isint)

(** val isweqfibtototal' :
    ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq **)

let isweqfibtototal' f =
  isweq_iso (totalfun (fun x -> pr1weq (f x)))
    (totalfun (fun x -> invmap (f x))) (fun xp ->
    total2_paths_f
      (totalfun (fun x -> invmap (f x)) (totalfun (fun x -> pr1weq (f x)) xp))
      xp Coq_paths_refl (homotinvweqweq (f xp.pr1) xp.pr2)) (fun xp ->
    total2_paths_f
      (totalfun (fun x -> pr1weq (f x)) (totalfun (fun x -> invmap (f x)) xp))
      xp Coq_paths_refl (homotweqinvweq (f xp.pr1) xp.pr2))

(** val weqfibtototal :
    ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq **)

let weqfibtototal f =
  make_weq (totalfun (fun x -> pr1weq (f x))) (isweqfibtototal' f)

(** val fpmap : ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2 **)

let fpmap f z =
  { pr1 = (f z.pr1); pr2 = z.pr2 }

(** val hffpmap2 :
    ('a1 -> 'a2) -> ('a1, 'a3) total2 -> (('a2, 'a3) total2, ('a1, 'a2)
    hfiber) total2 **)

let hffpmap2 f x0 =
  let u = fpmap f x0 in
  { pr1 = u; pr2 = (let x = x0.pr1 in { pr1 = x; pr2 = Coq_paths_refl }) }

(** val centralfiber : 'a1 -> ('a2, ('a1 coconusfromt, 'a2) total2) isweq **)

let centralfiber x =
  let f = fun p -> { pr1 = (coconusfromtpair x x Coq_paths_refl); pr2 = p } in
  let g = fun z ->
    transportf z.pr1.pr1 x (pathsinv0 x z.pr1.pr1 z.pr1.pr2) z.pr2
  in
  let efg = fun _ -> Coq_paths_refl in
  let egf = fun _ -> Coq_paths_refl in isweq_iso f g egf efg

(** val isweqhff :
    ('a1 -> 'a2) -> (('a1, 'a3) total2, (('a2, 'a3) total2, ('a1, 'a2)
    hfiber) total2) isweq **)

let isweqhff f =
  let intpair = fun x x0 -> { pr1 = x; pr2 = x0 } in
  let toint = fun z ->
    intpair z.pr2.pr1 { pr1 =
      (coconusfromtpair (f z.pr2.pr1) z.pr1.pr1 z.pr2.pr2); pr2 = z.pr1.pr2 }
  in
  let fromint = fun z -> { pr1 = { pr1 = z.pr2.pr1.pr1; pr2 = z.pr2.pr2 };
    pr2 = (make_hfiber f z.pr2.pr1.pr1 z.pr1 z.pr2.pr1.pr2) }
  in
  let fromto = fun _ -> Coq_paths_refl in
  let tofrom = fun _ -> Coq_paths_refl in
  let is = isweq_iso toint fromint fromto tofrom in
  let l1 = fun x -> centralfiber (f x) in
  let x0 =
    isweqfibtototal (fun x ->
      make_weq (fun p -> { pr1 =
        (coconusfromtpair (f x) (f x) Coq_paths_refl); pr2 = p }) (l1 x))
  in
  twooutof3a (hffpmap2 f) toint x0 is

(** val hfiberfpmap :
    ('a1 -> 'a2) -> ('a2, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3)
    total2) hfiber -> ('a1, 'a2) hfiber **)

let hfiberfpmap f yp x0 =
  let int1 = hfibersgftog (hffpmap2 f) (fun u -> u.pr1) yp in
  invezmappr1 yp (int1 x0)

(** val isweqhfiberfp :
    ('a1 -> 'a2) -> ('a2, 'a3) total2 -> ((('a1, 'a3) total2, ('a2, 'a3)
    total2) hfiber, ('a1, 'a2) hfiber) isweq **)

let isweqhfiberfp f yp =
  let int1 = hfibersgftog (hffpmap2 f) (fun u -> u.pr1) yp in
  let is1 =
    (weqhfibersgwtog (make_weq (hffpmap2 f) (isweqhff f)) (fun u -> u.pr1) yp).pr2
  in
  let phi = invezmappr1 yp in
  let is2 = (invweq (ezweqpr1 yp)).pr2 in twooutof3c int1 phi is1 is2

(** val isweqfpmap :
    ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) isweq **)

let isweqfpmap w y =
  let h = hfiberfpmap (pr1weq w) y in
  let x1 = isweqhfiberfp (pr1weq w) y in
  let is = w.pr2 y.pr1 in iscontrweqb (make_weq h x1) is

(** val weqfp_map :
    ('a1, 'a2) weq -> ('a1, 'a3) total2 -> ('a2, 'a3) total2 **)

let weqfp_map w xp =
  { pr1 = (pr1weq w xp.pr1); pr2 = xp.pr2 }

(** val weqfp_invmap :
    ('a1, 'a2) weq -> ('a2, 'a3) total2 -> ('a1, 'a3) total2 **)

let weqfp_invmap w yp =
  { pr1 = (invmap w yp.pr1); pr2 =
    (transportf yp.pr1 (pr1weq w (invmap w yp.pr1))
      (pathsinv0 (pr1weq w (invmap w yp.pr1)) yp.pr1
        (homotweqinvweq w yp.pr1)) yp.pr2) }

(** val weqfp :
    ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) weq **)

let weqfp w =
  { pr1 = (weqfp_map w); pr2 =
    (isweq_iso (weqfp_map w) (weqfp_invmap w) (fun xp ->
      total2_paths_f (weqfp_invmap w (weqfp_map w xp)) xp
        (homotinvweqweq w xp.pr1)
        (internal_paths_rew
          (transportf xp.pr1 (invmap w (pr1weq w xp.pr1))
            (pathsinv0 (invmap w (pr1weq w xp.pr1)) xp.pr1
              (homotinvweqweq w xp.pr1)) xp.pr2)
          (internal_paths_rew_r
            (transportf (invmap w (pr1weq w xp.pr1)) xp.pr1
              (homotinvweqweq w xp.pr1)
              (transportf xp.pr1 (invmap w (pr1weq w xp.pr1))
                (pathsinv0 (invmap w (pr1weq w xp.pr1)) xp.pr1
                  (homotinvweqweq w xp.pr1)) xp.pr2))
            (transportf xp.pr1 xp.pr1
              (pathscomp0 xp.pr1 (invmap w (pr1weq w xp.pr1)) xp.pr1
                (pathsinv0 (invmap w (pr1weq w xp.pr1)) xp.pr1
                  (homotinvweqweq w xp.pr1)) (homotinvweqweq w xp.pr1))
              xp.pr2)
            (internal_paths_rew_r
              (pathscomp0 xp.pr1 (invmap w (pr1weq w xp.pr1)) xp.pr1
                (pathsinv0 (invmap w (pr1weq w xp.pr1)) xp.pr1
                  (homotinvweqweq w xp.pr1)) (homotinvweqweq w xp.pr1))
              Coq_paths_refl Coq_paths_refl
              (pathsinv0l (invmap w (pr1weq w xp.pr1)) xp.pr1
                (homotinvweqweq w xp.pr1)))
            (transport_f_f xp.pr1 (invmap w (pr1weq w xp.pr1)) xp.pr1
              (pathsinv0 (invmap w (pr1weq w xp.pr1)) xp.pr1
                (homotinvweqweq w xp.pr1)) (homotinvweqweq w xp.pr1) xp.pr2))
          (transportf (pr1weq w xp.pr1)
            (pr1weq w (invmap w (pr1weq w xp.pr1)))
            (pathsinv0 (pr1weq w (invmap w (pr1weq w xp.pr1)))
              (pr1weq w xp.pr1) (homotweqinvweq w (pr1weq w xp.pr1))) xp.pr2)
          (weq_transportf_adjointness w xp.pr1 xp.pr2))) (fun yp ->
      total2_paths_f (weqfp_map w (weqfp_invmap w yp)) yp
        (homotweqinvweq w yp.pr1)
        (internal_paths_rew_r
          (transportf (pr1weq w (invmap w yp.pr1)) yp.pr1
            (homotweqinvweq w yp.pr1)
            (transportf yp.pr1 (pr1weq w (invmap w yp.pr1))
              (pathsinv0 (pr1weq w (invmap w yp.pr1)) yp.pr1
                (homotweqinvweq w yp.pr1)) yp.pr2))
          (transportf yp.pr1 yp.pr1
            (pathscomp0 yp.pr1 (pr1weq w (invmap w yp.pr1)) yp.pr1
              (pathsinv0 (pr1weq w (invmap w yp.pr1)) yp.pr1
                (homotweqinvweq w yp.pr1)) (homotweqinvweq w yp.pr1)) yp.pr2)
          (internal_paths_rew_r
            (pathscomp0 yp.pr1 (pr1weq w (invmap w yp.pr1)) yp.pr1
              (pathsinv0 (pr1weq w (invmap w yp.pr1)) yp.pr1
                (homotweqinvweq w yp.pr1)) (homotweqinvweq w yp.pr1))
            Coq_paths_refl Coq_paths_refl
            (pathsinv0l (pr1weq w (invmap w yp.pr1)) yp.pr1
              (homotweqinvweq w yp.pr1)))
          (transport_f_f yp.pr1 (pr1weq w (invmap w yp.pr1)) yp.pr1
            (pathsinv0 (pr1weq w (invmap w yp.pr1)) yp.pr1
              (homotweqinvweq w yp.pr1)) (homotweqinvweq w yp.pr1) yp.pr2)))) }

(** val weqfp_compute_1 :
    ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) homot **)

let weqfp_compute_1 _ _ =
  Coq_paths_refl

(** val weqfp_compute_2 :
    ('a1, 'a2) weq -> (('a2, 'a3) total2, ('a1, 'a3) total2) homot **)

let weqfp_compute_2 _ _ =
  Coq_paths_refl

(** val weqtotal2overcoprod' :
    (('a2, 'a3) coprod, 'a1) weq -> (('a1, 'a4) total2, (('a2, 'a4) total2,
    ('a3, 'a4) total2) coprod) weq **)

let weqtotal2overcoprod' f =
  weqcomp (invweq (weqfp f)) weqtotal2overcoprod

(** val fromtotal2overunit : (coq_unit, 'a1) total2 -> 'a1 **)

let fromtotal2overunit tp =
  tp.pr2

(** val tototal2overunit : 'a1 -> (coq_unit, 'a1) total2 **)

let tototal2overunit p =
  { pr1 = Coq_tt; pr2 = p }

(** val weqtotal2overunit : ((coq_unit, 'a1) total2, 'a1) weq **)

let weqtotal2overunit =
  { pr1 = fromtotal2overunit; pr2 =
    (let egf = fun _ -> Coq_paths_refl in
     let efg = fun _ -> Coq_paths_refl in
     isweq_iso fromtotal2overunit tototal2overunit egf efg) }

(** val bandfmap :
    ('a1 -> 'a2) -> ('a1 -> 'a3 -> 'a4) -> ('a1, 'a3) total2 -> ('a2, 'a4)
    total2 **)

let bandfmap f fm xp =
  { pr1 = (f xp.pr1); pr2 = (fm xp.pr1 xp.pr2) }

(** val isweqbandfmap :
    ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2,
    'a4) total2) isweq **)

let isweqbandfmap w fw =
  let f1 = totalfun (fun x -> pr1weq (fw x)) in
  let is1 = isweqfibtototal fw in
  let f2 = fpmap (pr1weq w) in
  let is2 = isweqfpmap w in
  let h = fun _ -> Coq_paths_refl in
  isweqhomot (fun xp -> f2 (f1 xp))
    (bandfmap (pr1weq w) (fun x -> pr1weq (fw x))) h
    (twooutof3c f1 f2 is1 is2)

(** val weqbandf :
    ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2,
    'a4) total2) weq **)

let weqbandf w fw =
  make_weq (bandfmap (pr1weq w) (fun x -> pr1weq (fw x))) (isweqbandfmap w fw)

type ('x, 'x0, 'y, 'z) commsqstr = 'z -> 'y paths

(** val hfibersgtof' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> 'a1 -> ('a4, 'a1) hfiber -> ('a2, 'a3) hfiber **)

let hfibersgtof' f f' g g' h x ze =
  let z = ze.pr1 in
  let e = ze.pr2 in
  { pr1 = (g' z); pr2 =
  (pathscomp0 (f' (g' z)) (f (g z)) (f x) (h z) (maponpaths f (g z) x e)) }

(** val hfibersg'tof :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> 'a2 -> ('a4, 'a2) hfiber -> ('a1, 'a3) hfiber **)

let hfibersg'tof f f' g g' h x' ze =
  let z = ze.pr1 in
  let e = ze.pr2 in
  { pr1 = (g z); pr2 =
  (pathscomp0 (f (g z)) (f' (g' z)) (f' x')
    (pathsinv0 (f' (g' z)) (f (g z)) (h z)) (maponpaths f' (g' z) x' e)) }

(** val transposcommsqstr :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> ('a2, 'a1, 'a3, 'a4) commsqstr **)

let transposcommsqstr f f' g g' h z =
  pathsinv0 (f' (g' z)) (f (g z)) (h z)

(** val complxstrtocommsqstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr ->
    (coq_unit, 'a2, 'a3, 'a1) commsqstr **)

let complxstrtocommsqstr _ _ _ h =
  h

(** val commsqstrtocomplxstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1)
    commsqstr -> ('a1, 'a2, 'a3) complxstr **)

let commsqstrtocomplxstr _ _ _ h =
  h

type ('x, 'x0, 'y) hfp = (('x, 'x0) dirprod, 'y paths) total2

(** val hfpg : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a1 **)

let hfpg _ _ xx'e =
  xx'e.pr1.pr1

(** val hfpg' : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a2 **)

let hfpg' _ _ xx'e =
  xx'e.pr1.pr2

(** val commsqZtohfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> 'a4 -> ('a1, 'a2, 'a3) hfp **)

let commsqZtohfp _ _ g g' h z =
  { pr1 = (make_dirprod (g z) (g' z)); pr2 = (h z) }

(** val commsqZtohfphomot :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> 'a4 -> 'a1 paths **)

let commsqZtohfphomot _ _ _ _ _ _ =
  Coq_paths_refl

(** val commsqZtohfphomot' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> 'a4 -> 'a2 paths **)

let commsqZtohfphomot' _ _ _ _ _ _ =
  Coq_paths_refl

type ('x, 'x0, 'y) hfpoverX = ('x, ('x0, 'y) hfiber) total2

type ('x, 'x0, 'y) hfpoverX' = ('x0, ('x, 'y) hfiber) total2

(** val weqhfptohfpoverX :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
    hfpoverX) weq **)

let weqhfptohfpoverX _ _ =
  weqtotal2asstor

(** val weqhfptohfpoverX' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
    hfpoverX') weq **)

let weqhfptohfpoverX' f f' =
  let w1 = weqfp weqdirprodcomm in
  let w2 = weqfibtototal (fun x'x -> weqpathsinv0 (f' x'x.pr1) (f x'x.pr2)) in
  weqcomp (weqcomp w1 w2) weqtotal2asstor

(** val weqhfpcomm :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, 'a1, 'a3)
    hfp) weq **)

let weqhfpcomm f f' =
  let w1 = weqfp weqdirprodcomm in
  let w2 = weqfibtototal (fun x'x -> weqpathsinv0 (f' x'x.pr1) (f x'x.pr2)) in
  weqcomp w1 w2

(** val commhfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) hfp)
    commsqstr **)

let commhfp _ _ xx'e =
  xx'e.pr2

(** val hfibertohfp :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> (coq_unit, 'a1, 'a2) hfp **)

let hfibertohfp _ _ xe =
  { pr1 = (make_dirprod Coq_tt xe.pr1); pr2 = xe.pr2 }

(** val hfptohfiber :
    ('a1 -> 'a2) -> 'a2 -> (coq_unit, 'a1, 'a2) hfp -> ('a1, 'a2) hfiber **)

let hfptohfiber f y hf =
  make_hfiber f y hf.pr1.pr2 hf.pr2

(** val weqhfibertohfp :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, (coq_unit, 'a1, 'a2) hfp) weq **)

let weqhfibertohfp f y =
  let ff = hfibertohfp f y in
  let gg = hfptohfiber f y in
  { pr1 = ff; pr2 =
  (let egf = fun _ -> Coq_paths_refl in
   let efg = fun _ -> Coq_paths_refl in isweq_iso ff gg egf efg) }

(** val hfp_left :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, ('a2, 'a3)
    hfiber) total2) weq **)

let hfp_left _ _ =
  weqtotal2dirprodassoc

(** val hfp_right :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, ('a1, 'a3)
    hfiber) total2) weq **)

let hfp_right f g =
  weq_iso (fun x0 ->
    let pr3 = x0.pr1 in
    let x = pr3.pr1 in
    let y = pr3.pr2 in
    let e = x0.pr2 in
    { pr1 = y; pr2 = { pr1 = x; pr2 = (pathsinv0 (g y) (f x) e) } })
    (fun x0 ->
    let x = x0.pr1 in
    let pr3 = x0.pr2 in
    let y = pr3.pr1 in
    let e = pr3.pr2 in
    { pr1 = { pr1 = y; pr2 = x }; pr2 = (pathsinv0 (f y) (g x) e) })
    (fun x0 ->
    let pr3 = x0.pr1 in
    let x = pr3.pr1 in
    let y = pr3.pr2 in
    let e = x0.pr2 in
    maponpaths (fun x1 -> { pr1 = { pr1 = x; pr2 = y }; pr2 = x1 })
      (pathsinv0 (f x) (g y) (pathsinv0 (g y) (f x) e)) e
      (pathsinv0inv0 (g y) (f x) e)) (fun y0 ->
    let x = y0.pr1 in
    let pr3 = y0.pr2 in
    let y = pr3.pr1 in
    let e = pr3.pr2 in
    maponpaths (fun x0 -> { pr1 = x; pr2 = x0 }) { pr1 = y; pr2 =
      (pathsinv0 (g x) (f y) (pathsinv0 (f y) (g x) e)) } { pr1 = y; pr2 =
      e }
      (maponpaths (fun x0 -> { pr1 = y; pr2 = x0 })
        (pathsinv0 (g x) (f y) (pathsinv0 (f y) (g x) e)) e
        (pathsinv0inv0 (f y) (g x) e)))

(** val hfiber_comm :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, ('a2, 'a3) hfiber) total2, ('a2,
    ('a1, 'a3) hfiber) total2) weq **)

let hfiber_comm f g =
  weq_iso (fun x0 ->
    let x = x0.pr1 in
    let pr3 = x0.pr2 in
    let y = pr3.pr1 in
    let e = pr3.pr2 in
    { pr1 = y; pr2 = { pr1 = x; pr2 = (pathsinv0 (g y) (f x) e) } })
    (fun x0 ->
    let y = x0.pr1 in
    let pr3 = x0.pr2 in
    let x = pr3.pr1 in
    let e = pr3.pr2 in
    { pr1 = x; pr2 = { pr1 = y; pr2 = (pathsinv0 (f x) (g y) e) } })
    (fun x0 ->
    let x = x0.pr1 in
    let pr3 = x0.pr2 in
    let y = pr3.pr1 in
    let e = pr3.pr2 in
    maponpaths (fun x1 -> { pr1 = x; pr2 = x1 }) { pr1 = y; pr2 =
      (pathsinv0 (f x) (g y) (pathsinv0 (g y) (f x) e)) } { pr1 = y; pr2 =
      e }
      (maponpaths (fun x1 -> { pr1 = y; pr2 = x1 })
        (pathsinv0 (f x) (g y) (pathsinv0 (g y) (f x) e)) e
        (pathsinv0inv0 (g y) (f x) e))) (fun y0 ->
    let y = y0.pr1 in
    let pr3 = y0.pr2 in
    let x = pr3.pr1 in
    let e = pr3.pr2 in
    maponpaths (fun x0 -> { pr1 = y; pr2 = x0 }) { pr1 = x; pr2 =
      (pathsinv0 (g y) (f x) (pathsinv0 (f x) (g y) e)) } { pr1 = x; pr2 =
      e }
      (maponpaths (fun x0 -> { pr1 = x; pr2 = x0 })
        (pathsinv0 (g y) (f x) (pathsinv0 (f x) (g y) e)) e
        (pathsinv0inv0 (f x) (g y) e)))

type ('x, 'x0, 'y, 'z) ishfsq = ('z, ('x, 'x0, 'y) hfp) isweq

type ('x, 'x0, 'y, 'z) hfsqstr =
  (('x, 'x0, 'y, 'z) commsqstr, ('z, ('x, 'x0, 'y) hfp) isweq) total2

(** val make_hfsqstr :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) isweq -> (('a1,
    'a2, 'a3, 'a4) commsqstr, ('a4, ('a1, 'a2, 'a3) hfp) isweq) total2 **)

let make_hfsqstr _ _ _ _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val hfsqstrtocommsqstr :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> ('a1, 'a2, 'a3, 'a4) commsqstr **)

let hfsqstrtocommsqstr _ _ _ _ t =
  t.pr1

(** val weqZtohfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) weq **)

let weqZtohfp f f' g g' hf =
  make_weq (commsqZtohfp f f' g g' hf.pr1) hf.pr2

(** val isweqhfibersgtof' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber)
    isweq **)

let isweqhfibersgtof' f f' g g' hf x =
  let is = hf.pr2 in
  let h = hf.pr1 in
  let a = weqtococonusf g in
  let c = make_weq (commsqZtohfp f f' g g' hf.pr1) is in
  let d = weqhfptohfpoverX f f' in
  let b0 = totalfun (hfibersgtof' f f' g g' h) in
  let h1 = fun _ -> Coq_paths_refl in
  let is1 =
    isweqhomot (fun z -> pr1weq d (pr1weq c z)) (fun z -> b0 (pr1weq a z)) h1
      (twooutof3c c.pr1 d.pr1 c.pr2 d.pr2)
  in
  let is2 = twooutof3b a.pr1 b0 a.pr2 is1 in
  isweqtotaltofib (hfibersgtof' f f' g g' h) is2 x

(** val weqhfibersgtof' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber)
    weq **)

let weqhfibersgtof' f f' g g' hf x =
  make_weq (hfibersgtof' f f' g g' (hfsqstrtocommsqstr f f' g g' hf) x)
    (isweqhfibersgtof' f f' g g' hf x)

(** val ishfsqweqhfibersgtof' :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> ('a1 -> (('a4, 'a1) hfiber, ('a2, 'a3)
    hfiber) isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr **)

let ishfsqweqhfibersgtof' f f' g g' h is =
  { pr1 = h; pr2 =
    (let a = weqtococonusf g in
     let c0 = commsqZtohfp f f' g g' h in
     let d = weqhfptohfpoverX f f' in
     let b =
       weqfibtototal (fun x -> make_weq (hfibersgtof' f f' g g' h x) (is x))
     in
     let h1 = fun _ -> Coq_paths_refl in
     let is1 =
       isweqhomot (fun z -> pr1weq b (pr1weq a z)) (fun z -> pr1weq d (c0 z))
         (fun z ->
         pathsinv0 (pr1weq d (c0 z)) (pr1weq b (pr1weq a z)) (h1 z))
         (twooutof3c a.pr1 b.pr1 a.pr2 b.pr2)
     in
     twooutof3a c0 (pr1weq d) is1 d.pr2) }

(** val isweqhfibersg'tof :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber)
    isweq **)

let isweqhfibersg'tof f f' g g' hf x' =
  let is = hf.pr2 in
  let h = hf.pr1 in
  let a' = weqtococonusf g' in
  let c' = make_weq (commsqZtohfp f f' g g' hf.pr1) is in
  let d' = weqhfptohfpoverX' f f' in
  let b0' = totalfun (hfibersg'tof f f' g g' h) in
  let h1 = fun _ -> Coq_paths_refl in
  let is1 =
    isweqhomot (fun z -> pr1weq d' (pr1weq c' z)) (fun z ->
      b0' (pr1weq a' z)) h1 (twooutof3c c'.pr1 d'.pr1 c'.pr2 d'.pr2)
  in
  let is2 = twooutof3b a'.pr1 b0' a'.pr2 is1 in
  isweqtotaltofib (hfibersg'tof f f' g g' h) is2 x'

(** val weqhfibersg'tof :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber)
    weq **)

let weqhfibersg'tof f f' g g' hf x' =
  make_weq (hfibersg'tof f f' g g' (hfsqstrtocommsqstr f f' g g' hf) x')
    (isweqhfibersg'tof f f' g g' hf x')

(** val ishfsqweqhfibersg'tof :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) commsqstr -> ('a2 -> (('a4, 'a2) hfiber, ('a1, 'a3)
    hfiber) isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr **)

let ishfsqweqhfibersg'tof f f' g g' h is =
  { pr1 = h; pr2 =
    (let a' = weqtococonusf g' in
     let c0' = commsqZtohfp f f' g g' h in
     let d' = weqhfptohfpoverX' f f' in
     let b' =
       weqfibtototal (fun x' ->
         make_weq (hfibersg'tof f f' g g' h x') (is x'))
     in
     let h1 = fun _ -> Coq_paths_refl in
     let is1 =
       isweqhomot (fun z -> pr1weq b' (pr1weq a' z)) (fun z ->
         pr1weq d' (c0' z)) (fun z ->
         pathsinv0 (pr1weq d' (c0' z)) (pr1weq b' (pr1weq a' z)) (h1 z))
         (twooutof3c a'.pr1 b'.pr1 a'.pr2 b'.pr2)
     in
     twooutof3a c0' (pr1weq d') is1 d'.pr2) }

(** val transposhfpsqstr :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1,
    'a2, 'a3, 'a4) hfsqstr -> ('a2, 'a1, 'a3, 'a4) hfsqstr **)

let transposhfpsqstr f f' g g' hf =
  let is = hf.pr2 in
  let h = hf.pr1 in
  let th = transposcommsqstr f f' g g' h in
  { pr1 = th; pr2 =
  (let w1 = weqhfpcomm f f' in
   let h1 = fun _ -> Coq_paths_refl in
   isweqhomot (fun z -> pr1weq w1 (commsqZtohfp f f' g g' h z))
     (commsqZtohfp f' f g' g th) h1
     (twooutof3c (commsqZtohfp f f' g g' hf.pr1) w1.pr1 is w1.pr2)) }

(** val fibseqstrtohfsqstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
    (coq_unit, 'a2, 'a3, 'a1) hfsqstr **)

let fibseqstrtohfsqstr f g z hf =
  { pr1 = hf.pr1; pr2 =
    (let ff = ezweq f g z hf in
     let gg = weqhfibertohfp g z in (weqcomp ff gg).pr2) }

(** val hfsqstrtofibseqstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1) hfsqstr
    -> ('a1, 'a2, 'a3) fibseqstr **)

let hfsqstrtofibseqstr f g z hf =
  { pr1 = hf.pr1; pr2 =
    (let ff = ezmap f g z hf.pr1 in
     let ggff = weqZtohfp (fun _ -> z) g (fun _ -> Coq_tt) f hf in
     let gg = weqhfibertohfp g z in twooutof3a ff (pr1weq gg) ggff.pr2 gg.pr2) }


(** val transitive_paths_weq :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) weq **)

let transitive_paths_weq x y z xeqy =
  weq_iso (fun xeqz -> pathscomp0 y x z (pathsinv0 x y xeqy) xeqz)
    (fun yeqz -> pathscomp0 x y z xeqy yeqz) (fun xeqz ->
    pathscomp0
      (pathscomp0 x y z xeqy (pathscomp0 y x z (pathsinv0 x y xeqy) xeqz))
      (pathscomp0 x x z (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) xeqz)
      xeqz (path_assoc x y x z xeqy (pathsinv0 x y xeqy) xeqz)
      (pathscomp0
        (pathscomp0 x x z (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) xeqz)
        (pathscomp0 x x z Coq_paths_refl xeqz) xeqz
        (maponpaths (fun p -> pathscomp0 x x z p xeqz)
          (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) Coq_paths_refl
          (pathsinv0r x y xeqy)) Coq_paths_refl)) (fun yeqz ->
    pathscomp0
      (pathscomp0 y x z (pathsinv0 x y xeqy) (pathscomp0 x y z xeqy yeqz))
      (pathscomp0 y y z (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) yeqz)
      yeqz (path_assoc y x y z (pathsinv0 x y xeqy) xeqy yeqz)
      (pathscomp0
        (pathscomp0 y y z (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) yeqz)
        (pathscomp0 y y z Coq_paths_refl yeqz) yeqz
        (maponpaths (fun p -> pathscomp0 y y z p yeqz)
          (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) Coq_paths_refl
          (pathsinv0l x y xeqy)) Coq_paths_refl))

(** val weqtotal2comm :
    (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq **)

(* val weqtotal2comm : *)
(*   (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq *)

(* let weqtotal2comm = *)
(*   weq_iso (fun pair -> { pr1 = pair.pr2.pr1; pr2 = { pr1 = pair.pr1; pr2 = *)
(*     pair.pr2.pr2 } }) (fun pair -> { pr1 = pair.pr2.pr1; pr2 = { pr1 = *)
(*     pair.pr1; pr2 = pair.pr2.pr2 } }) (fun _ -> Coq_paths_refl) (fun _ -> *)
(*     Coq_paths_refl) *)

(** val pathsdirprodweq :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (('a1, 'a2) dirprod paths, ('a1 paths, 'a2
    paths) dirprod) weq **)

let pathsdirprodweq x1 x2 y1 y2 =
  weqcomp (total2_paths_equiv (make_dirprod x1 y1) (make_dirprod x2 y2))
    (weqfibtototal (fun p ->
      transitive_paths_weq (transportf x1 x2 p y1) y1 y2
        (toforallpaths (transportf x1 x2 p) idfun (transportf_const x1 x2 p)
          y1)))

(** val dirprod_with_contr_r :
    'a1 iscontr -> ('a2, ('a2, 'a1) dirprod) weq **)

let isweqcontrtounit is _ =
  let c = is.pr1 in
  let h = is.pr2 in
  let hc = make_hfiber (fun _ -> Coq_tt) Coq_tt c Coq_paths_refl in
  { pr1 = hc; pr2 = (fun ha ->
  let x = ha.pr1 in
  let e = ha.pr2 in
  two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 }) x e c Coq_paths_refl
    (h x) (ifcontrthenunitl0 (transportf x c (h x) e) Coq_paths_refl)) }
let make_dirprod x y =
  { pr1 = x; pr2 = y }

let weqtodirprodwithunit =
  let f = fun x -> make_dirprod x Coq_tt in
  { pr1 = f; pr2 =
  (let g = fun xu -> xu.pr1 in
   let egf = fun _ -> Coq_paths_refl in
   let efg = fun _ -> Coq_paths_refl in isweq_iso f g egf efg) }

let dirprod_with_contr_r iscontrX =
  weqcomp weqtodirprodwithunit
    (weqdirprodf idweq (invweq (weqcontrtounit iscontrX)))

(** val dirprod_with_contr_l :
    'a1 iscontr -> ('a2, ('a1, 'a2) dirprod) weq **)

let dirprod_with_contr_l iscontrX =
  weqcomp (dirprod_with_contr_r iscontrX) weqdirprodcomm

(** val total2_assoc_fun_left :
    (('a1 -> ('a2, 'a3) total2, 'a4) total2, ('a1 -> 'a2, ('a1 -> 'a3, 'a4)
    total2) total2) weq **)

(* let total2_assoc_fun_left = *)
(*   weq_iso (fun p -> { pr1 = (fun a -> (p.pr1 a).pr1); pr2 = { pr1 = (fun a -> *)
(*     (p.pr1 a).pr2); pr2 = p.pr2 } }) (fun p -> { pr1 = (fun a -> { pr1 = *)
(*     (p.pr1 a); pr2 = (p.pr2.pr1 a) }); pr2 = p.pr2.pr2 }) (fun _ -> *)
(*     Coq_paths_refl) (fun _ -> Coq_paths_refl) *)

(** val sec_total2_distributivity :
    ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq **)

let sec_total2_distributivity =
  weq_iso (fun f -> { pr1 = (fun a -> (f a).pr1); pr2 = (fun a ->
    (f a).pr2) }) (fun f a -> { pr1 = (f.pr1 a); pr2 = (f.pr2 a) })
    (Obj.magic (fun _ -> Coq_paths_refl))
    (Obj.magic (fun _ -> Coq_paths_refl))



let isweqrecompl_ne' x is neq_x y =
  iscontrweqb weqtotal2overcoprod
    (let c = is y in
     match c with
     | Coq_ii1 _ ->
       iscontrweqf (weqii2withneg (fun _ -> assert false (* absurd case *)))
         { pr1 = { pr1 = Coq_tt; pr2 = Coq_paths_refl }; pr2 = (fun w ->
         let e = w.pr2 in
         maponpaths (fun x0 -> { pr1 = Coq_tt; pr2 = x0 }) e Coq_paths_refl
           (let x' = Coq_paths_refl in
            (Obj.magic isaproppathsfromisolated x is x e x').pr1)) }
     | Coq_ii2 b ->
       iscontrweqf (weqii1withneg (fun _ -> assert false (* absurd case *)))
         { pr1 = { pr1 = { pr1 = y; pr2 = (neg_to_negProp (neq_x y) b) };
         pr2 = Coq_paths_refl }; pr2 = (fun _ -> Coq_paths_refl) })
let ischoicebasecoprod isx isy =
  Obj.magic (fun _ fs ->
    hinhfun (pr1weq (invweq weqsecovercoprodtoprod))
      (hinhand (Obj.magic isx __ (fun x -> fs (Coq_ii1 x)))
        (Obj.magic isy __ (fun y -> fs (Coq_ii2 y)))))

(* from nat *)
let nat_dist_between_ge m n a b i j =
  let j0 =
    internal_paths_rew (nat_dist m n) j (nat_dist n m) (nat_dist_symm m n)
  in
  let j1 = internal_paths_rew (add a b) j0 (add b a) (natpluscomm a b) in
  { pr1 = (nat_dist_between_le n m b a i j1).pr1; pr2 =
  (weqdirprodcomm.pr1 (nat_dist_between_le n m b a i j1).pr2) }
let nat_dist_between m n a b j =
  let c = natgthorleh m n in
  (match c with
   | Coq_ii1 a0 -> nat_dist_between_ge m n a b (natlthtoleh n m a0) j
   | Coq_ii2 b0 -> nat_dist_between_le m n a b b0 j)


