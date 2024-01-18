type __ = Obj.t
type coq_UU = __
type 'x isofhlevel = __
type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }
type ('x, 'y) dirprod = ('x, 'y) total2
type 'x isaprop = 'x isofhlevel
type 'a paths = | Coq_paths_refl
type 'x isaset = 'x -> 'x -> 'x paths isaprop
type hSet = (coq_UU, __ isaset) total2

type node = __
type arc = __

type has_nodeset = node isaset
type has_arcset = arc isaset

type precgraph =  (coq_UU,
                   
                   (coq_UU,(
                       __ -> __,
                       __ -> __)
                       dirprod)
                   
                     total2)
    total2
type cgraph = (precgraph,
               (node isaset, arc isaset)
                 dirprod)
    total2
type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod
type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2


    
(*
val source : precgraph -> arc -> node
   val target : precgraph -> arc -> node
val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph
   val isaset_arc : cgraph -> arc isaset
   val arc_set : cgraph -> hSet
   val make_cgraph_mor :
  precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> is_cgraph_mor
  -> cgraph_mor
val onnode : precgraph -> precgraph -> cgraph_mor -> node -> node

val onarc : precgraph -> precgraph -> cgraph_mor -> arc -> arc
val preserves_source :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths

val preserves_target :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths
val isaprop_is_cgraph_mor :
  precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> has_nodeset ->
  is_cgraph_mor isaprop

val isaset_cgraph_mor :
  precgraph -> precgraph -> has_nodeset -> has_arcset -> cgraph_mor isaset

val cgraph_mor_eq_aux :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor -> (node -> node) paths
  -> (arc -> arc) paths -> has_nodeset -> cgraph_mor paths

val cgraph_mor_eq :
  cgraph -> cgraph -> cgraph_mor -> cgraph_mor -> (node -> node paths) ->
  (arc -> arc paths) -> cgraph_mor paths

val precgraph_weq_pregraph : (precgraph, pregraph) weq
*)
