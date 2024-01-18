open PartA
open PartB
open PartD
open Preamble
open Propositions0
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type pregraph = (coq_UU, __) total2

(** val make_pregraph : pregraph **)

let make_pregraph =
  { pr1 = __; pr2 = __ }

type vertex = __

type edge = __

type has_vertexset = vertex isaset

(** val isaprop_has_vertexset : pregraph -> has_vertexset isaprop **)

let isaprop_has_vertexset _ =
  isapropisaset

type has_edgesets = vertex -> vertex -> edge isaset

type graph = (pregraph, (has_vertexset, has_edgesets) dirprod) total2

(** val make_graph : pregraph -> has_vertexset -> has_edgesets -> graph **)

let make_graph g h k =
  { pr1 = g; pr2 = (make_dirprod h k) }

(** val pregraph_of_graph : graph -> pregraph **)

let pregraph_of_graph t =
  t.pr1

(** val isaset_vertex : graph -> vertex isaset **)

let isaset_vertex g =
  g.pr2.pr1

(** val isaset_edge : graph -> vertex -> vertex -> edge isaset **)

let isaset_edge g =
  g.pr2.pr2

type graph_mor = (vertex -> vertex, vertex -> vertex -> edge -> edge) total2

(** val make_graph_mor :
    pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge
    -> edge) -> graph_mor **)

let make_graph_mor _ _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val onvertex : pregraph -> pregraph -> graph_mor -> vertex -> vertex **)

let onvertex _ _ t =
  t.pr1

(** val onedge :
    pregraph -> pregraph -> graph_mor -> vertex -> vertex -> edge -> edge **)

let onedge _ _ p x y =
  p.pr2 x y

(** val graph_mor_id : pregraph -> graph_mor **)

let graph_mor_id g =
  make_graph_mor g g idfun (fun _ _ -> idfun)

(** val graph_mor_comp :
    pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor -> graph_mor **)

let graph_mor_comp g h k p q =
  make_graph_mor g k (funcomp (onvertex g h p) (onvertex h k q))
    (fun x y f -> onedge h k q (p.pr1 x) (p.pr1 y) (p.pr2 x y f))

(** val make_graph_mor_eq :
    pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge
    -> edge) -> (vertex -> vertex -> edge -> edge) -> (vertex -> vertex ->
    edge -> edge paths) -> graph_mor paths **)

let make_graph_mor_eq _ _ p_UU2080_ p_UU2081_ p_UU2081_' e =
  pair_path_in2 p_UU2080_ p_UU2081_ p_UU2081_'
    (Obj.magic funextsec p_UU2081_ p_UU2081_' (fun x ->
      Obj.magic funextsec (Obj.magic p_UU2081_ x) (Obj.magic p_UU2081_' x)
        (fun y ->
        Obj.magic funextfun (p_UU2081_ x y) (p_UU2081_' x y) (fun f ->
          e x y f))))

(** val graph_mor_id_left :
    pregraph -> pregraph -> graph_mor -> graph_mor paths **)

let graph_mor_id_left g h p =
  let p_UU2080_ = p.pr1 in
  let p_UU2081_ = p.pr2 in
  make_graph_mor_eq g h p_UU2080_ (fun x y f ->
    onedge g h { pr1 = p_UU2080_; pr2 = p_UU2081_ } ((graph_mor_id g).pr1 x)
      ((graph_mor_id g).pr1 y) ((graph_mor_id g).pr2 x y f)) p_UU2081_
    (fun _ _ _ -> Coq_paths_refl)

(** val graph_mor_id_right :
    pregraph -> pregraph -> graph_mor -> graph_mor paths **)

let graph_mor_id_right g h p =
  let p_UU2080_ = p.pr1 in
  let p_UU2081_ = p.pr2 in
  make_graph_mor_eq g h p_UU2080_ (fun x y f ->
    onedge h h (graph_mor_id h) (p_UU2080_ x) (p_UU2080_ y) (p_UU2081_ x y f))
    p_UU2081_ (fun _ _ _ -> Coq_paths_refl)

(** val graph_mor_comp_assoc :
    pregraph -> pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor ->
    graph_mor -> graph_mor paths **)

let graph_mor_comp_assoc g1 g2 g3 g4 p q r =
  let p_UU2080_ = p.pr1 in
  let p_UU2081_ = p.pr2 in
  let q_UU2080_ = q.pr1 in
  let q_UU2081_ = q.pr2 in
  let r_UU2080_ = r.pr1 in
  let r_UU2081_ = r.pr2 in
  make_graph_mor_eq g1 g4
    (funcomp
      (onvertex g1 g3
        (graph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = p_UU2081_ } { pr1 =
          q_UU2080_; pr2 = q_UU2081_ }))
      (onvertex g3 g4 { pr1 = r_UU2080_; pr2 = r_UU2081_ })) (fun x y f ->
    onedge g2 g4
      (graph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = q_UU2081_ } { pr1 =
        r_UU2080_; pr2 = r_UU2081_ }) (p_UU2080_ x) (p_UU2080_ y)
      (p_UU2081_ x y f)) (fun x y f ->
    onedge g3 g4 { pr1 = r_UU2080_; pr2 = r_UU2081_ }
      ((graph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = p_UU2081_ } { pr1 =
         q_UU2080_; pr2 = q_UU2081_ }).pr1 x)
      ((graph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = p_UU2081_ } { pr1 =
         q_UU2080_; pr2 = q_UU2081_ }).pr1 y)
      ((graph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = p_UU2081_ } { pr1 =
         q_UU2080_; pr2 = q_UU2081_ }).pr2 x y f)) (fun _ _ _ ->
    Coq_paths_refl)

(** val isaset_graph_mor :
    pregraph -> pregraph -> has_vertexset -> has_edgesets -> graph_mor isaset **)

let funspace_isaset x = x
let isaset_graph_mor _ _ h k =
  isaset_total2 (funspace_isaset h) (fun p_UU2080_ ->
    impred_isaset (fun x ->
      impred_isaset (fun y -> funspace_isaset (k (p_UU2080_ x) (p_UU2080_ y)))))
