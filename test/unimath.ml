
val total2_paths_equiv' :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
  'a2) coq_PathPair) weq

val total2_paths_equiv'_compute :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths -> ('a1,
  'a2) coq_PathPair) paths


val pr1_issurjective :
  ('a1 -> hProptoType) -> (('a1, 'a2) total2, 'a1) issurjective

val eqrel_on_bool : hProp -> pr1hSet eqrel

val eqrel_on_bool_iff : hProp -> (pr1hSet setquot paths, hProptoType) logeq

val coq_AxiomOfChoice : hProp

val coq_AxiomOfChoice_surj : hProp

val coq_AC_impl2 : (hProptoType, hProptoType) logeq

val coq_SetCovering : hProptoType -> hProptoType

val coq_AC_to_LEM : hProptoType -> hProptoType

val coq_AxiomOfDecidableChoice : hProp

val coq_AC_iff_ADC_and_LEM : hProptoType

val andb : bool -> bool -> bool

val orb : bool -> bool -> bool

val implb : bool -> bool -> bool

val andb_is_associative : bool -> bool -> bool -> bool paths

val orb_is_associative : bool -> bool -> bool -> bool paths

val andb_is_commutative : bool -> bool -> bool paths

val orb_is_commutative : bool -> bool -> bool paths

type minimal = nat -> hProptoType -> hProptoType

val isapropminimal : (nat -> hProp) -> nat -> minimal isaprop

type min_n_UUU = (nat, (hProptoType, minimal) dirprod) total2

val isapropmin_n : (nat -> hProp) -> min_n_UUU isaprop

val min_n : (nat -> hProp) -> hProp

type smaller =
  (nat, (hProptoType, (minimal, hProptoType) dirprod) dirprod) total2

val smaller_S : (nat -> hProp) -> nat -> smaller -> smaller

val bounded_search :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat ->
  (smaller, nat -> hProptoType -> hProptoType neg) coprod

val n_to_min_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat ->
  hProptoType -> hProptoType

val prop_n_to_min_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
  hProptoType -> hProptoType

val minimal_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
  hProptoType -> (nat, hProptoType) total2

type __ = Obj.t

type precgraph =
  (coq_UU, (coq_UU, (__ -> __, __ -> __) dirprod) total2) total2

val make_precgraph : ('a2 -> 'a1) -> ('a2 -> 'a1) -> precgraph

type node = __

type arc = __

val source : precgraph -> arc -> node

val target : precgraph -> arc -> node

type has_nodeset = node isaset

type has_arcset = arc isaset

type cgraph = (precgraph, (node isaset, arc isaset) dirprod) total2

val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph

val precgraph_of_cgraph : cgraph -> precgraph

val isaset_node : cgraph -> node isaset

val node_set : cgraph -> hSet

val isaset_arc : cgraph -> arc isaset

val arc_set : cgraph -> hSet

type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod

type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2

val make_cgraph_mor :
  precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> is_cgraph_mor
  -> cgraph_mor

val onnode : precgraph -> precgraph -> cgraph_mor -> node -> node

val onarc : precgraph -> precgraph -> cgraph_mor -> arc -> arc

val preserves_source :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths

val preserves_target :
  precgraph -> precgraph -> cgraph_mor -> arc -> node paths

val is_cgraph_mor_id : precgraph -> is_cgraph_mor

val cgraph_mor_id : precgraph -> cgraph_mor

val is_cgraph_mor_comp :
  precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
  is_cgraph_mor

val cgraph_mor_comp :
  precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
  cgraph_mor

val cgraph_mor_id_left :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths

val cgraph_mor_id_right :
  precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths

val cgraph_mor_comp_assoc :
  precgraph -> precgraph -> precgraph -> precgraph -> cgraph_mor ->
  cgraph_mor -> cgraph_mor -> cgraph_mor paths

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

type __ = Obj.t

val retract_dec :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2, 'a2) homot -> 'a1 isdeceq -> 'a2
  isdeceq

val logeq_dec : ('a1, 'a2) logeq -> 'a1 decidable -> 'a2 decidable

val decidable_prop : hProp -> hProp

val coq_LEM : hProp

type coq_ComplementaryPair =
  (coq_UU, (coq_UU, (__, __) complementary) total2) total2

type coq_Part1 = __

type coq_Part2 = __

val pair_contradiction :
  coq_ComplementaryPair -> coq_Part1 -> coq_Part2 -> empty

val chooser : coq_ComplementaryPair -> (coq_Part1, coq_Part2) coprod

type isTrue = (coq_Part1, (coq_Part1, coq_Part2) coprod) hfiber

type isFalse = (coq_Part2, (coq_Part1, coq_Part2) coprod) hfiber

val trueWitness : coq_ComplementaryPair -> isTrue -> coq_Part1

val falseWitness : coq_ComplementaryPair -> isFalse -> coq_Part2

val complementaryDecisions :
  coq_ComplementaryPair -> (isTrue, isFalse) coprod iscontr

val isaprop_isTrue : coq_ComplementaryPair -> isTrue isaprop

val isaprop_isFalse : coq_ComplementaryPair -> isFalse isaprop

val pair_truth : coq_ComplementaryPair -> coq_Part1 -> isTrue

val pair_falsehood : coq_ComplementaryPair -> coq_Part2 -> isFalse

val to_ComplementaryPair : ('a1, 'a1 neg) coprod -> coq_ComplementaryPair

type 'x isolation = isFalse

val isaprop_isolation : 'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation isaprop

val isolation_to_inequality :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation -> 'a1 paths neg

val inequality_to_isolation :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths neg -> 'a1 isolation

val pairNegation : coq_ComplementaryPair -> coq_ComplementaryPair

val pairConjunction :
  coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair

val pairDisjunction :
  coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair

val dnegelim : ('a1, 'a2) complementary -> 'a1 dneg -> 'a1

val coq_LEM_for_sets : hProptoType -> 'a1 isaset -> 'a1 isdeceq

val isaprop_LEM : hProptoType isaprop

val dneg_LEM : hProp -> hProptoType -> hProptoType dneg -> hProptoType

val reversal_LEM :
  hProp -> hProp -> hProptoType -> (hProptoType neg -> hProptoType) ->
  hProptoType neg -> hProptoType

type coq_DecidableProposition = (coq_UU, __ isdecprop) total2

val isdecprop_to_DecidableProposition :
  'a1 isdecprop -> coq_DecidableProposition

val decidable_to_isdecprop :
  hProp -> hProptoType decidable -> hProptoType isdecprop

val decidable_to_isdecprop_2 :
  'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop

val decidable_to_DecidableProposition :
  hProp -> hProptoType decidable -> coq_DecidableProposition

val coq_DecidableProposition_to_isdecprop :
  coq_DecidableProposition -> __ isdecprop

val coq_DecidableProposition_to_hProp : coq_DecidableProposition -> hProp

val decidabilityProperty : coq_DecidableProposition -> hProptoType isdecprop

type 'x coq_DecidableSubtype = 'x -> coq_DecidableProposition

type 'x coq_DecidableRelation = 'x -> 'x -> coq_DecidableProposition

val decrel_to_DecidableRelation : 'a1 decrel -> 'a1 coq_DecidableRelation

val decidableAnd :
  coq_DecidableProposition -> coq_DecidableProposition ->
  coq_DecidableProposition

val decidableOr :
  coq_DecidableProposition -> coq_DecidableProposition ->
  coq_DecidableProposition

val neg_isdecprop : 'a1 isdecprop -> 'a1 neg isdecprop

val decidableNot : coq_DecidableProposition -> coq_DecidableProposition

val choice : coq_DecidableProposition -> 'a1 -> 'a1 -> 'a1

val dependent_choice :
  coq_DecidableProposition -> (hProptoType -> 'a1) -> (hProptoType neg ->
  'a1) -> 'a1

val choice_compute_yes :
  coq_DecidableProposition -> hProptoType -> 'a1 -> 'a1 -> 'a1 paths

val choice_compute_no :
  coq_DecidableProposition -> hProptoType neg -> 'a1 -> 'a1 -> 'a1 paths

type 'x decidableSubtypeCarrier = ('x, hProptoType) total2

type 'x decidableSubtypeCarrier' = ('x, bool) hfiber

val decidableSubtypeCarrier_weq :
  'a1 coq_DecidableSubtype -> ('a1 decidableSubtypeCarrier', 'a1
  decidableSubtypeCarrier) weq

val coq_DecidableSubtype_to_hsubtype :
  'a1 coq_DecidableSubtype -> 'a1 hsubtype

val coq_DecidableRelation_to_hrel : 'a1 coq_DecidableRelation -> 'a1 hrel

val natlth_DecidableProposition : nat coq_DecidableRelation

val natleh_DecidableProposition : nat coq_DecidableRelation

val natgth_DecidableProposition : nat coq_DecidableRelation

val natgeh_DecidableProposition : nat coq_DecidableRelation

val nateq_DecidableProposition : nat coq_DecidableRelation

val natneq_DecidableProposition : nat coq_DecidableRelation

type __ = Obj.t

type decSet = (coq_UU, __ isdeceq) total2

val make_decSet : 'a1 isdeceq -> decSet

type pr1decSet = __

val decproperty : decSet -> __ isdeceq

val wma_dneg : 'a2 dneg -> ('a2 -> 'a1 neg) -> 'a1 neg

val dneg_decidable : 'a1 decidable dneg

val wma_decidable : ('a2 decidable -> 'a1 neg) -> 'a1 neg

val negforall_to_existsneg' : hProptoType -> hProptoType dneg


val eqrel_closure_hrel : 'a1 hrel -> 'a1 hrel

val iseqrel_closure : 'a1 hrel -> 'a1 iseqrel

val eqrel_closure : 'a1 hrel -> 'a1 eqrel

val eqrel_closure_minimal :
  'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1
  -> 'a1 -> hProptoType -> hProptoType

type __ = Obj.t

type 'x coq_Vector = stn -> 'x

val vector_hlevel : nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Vector isofhlevel

val const_vec : nat -> 'a1 -> 'a1 coq_Vector

val iscontr_vector_0 : 'a1 coq_Vector iscontr

val empty_vec : 'a1 coq_Vector

val weq_vector_1 : ('a1, 'a1 coq_Vector) weq

val append_vec : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 coq_Vector

val append_vec_compute_1 : nat -> 'a1 coq_Vector -> 'a1 -> stn -> 'a1 paths

val append_vec_compute_2 : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 paths

val drop_and_append_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Vector paths

val coq_Vector_rect :
  'a2 -> (nat -> 'a1 coq_Vector -> 'a1 -> 'a2 -> 'a2) -> nat -> 'a1
  coq_Vector -> 'a2

val vectorEquality :
  nat -> nat -> 'a1 coq_Vector -> 'a1 coq_Vector -> nat paths -> (stn -> 'a1
  paths) -> 'a1 coq_Vector paths

val tail : nat -> 'a1 coq_Vector -> 'a1 coq_Vector

val vector_stn_proofirrelevance :
  nat -> 'a1 coq_Vector -> stn -> stn -> nat paths -> 'a1 paths

type 'x coq_Matrix = 'x coq_Vector coq_Vector

val transpose : nat -> nat -> 'a1 coq_Matrix -> 'a1 coq_Matrix

val row : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector

val col : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector

val row_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix

val col_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix

val matrix_hlevel :
  nat -> nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Matrix isofhlevel

val const_matrix : nat -> nat -> 'a1 -> 'a1 coq_Matrix

val weq_matrix_1_1 : ('a1, 'a1 coq_Matrix) weq

type 'x coq_Sequence = (nat, 'x coq_Vector) total2

type 'x coq_NonemptySequence = (nat, stn -> 'x) total2

type 'x coq_UnorderedSequence = (coq_FiniteSet, pr1hSet -> 'x) total2

val length : 'a1 coq_Sequence -> nat

val sequenceToFunction : 'a1 coq_Sequence -> stn -> 'a1

val unorderedSequenceToFunction : 'a1 coq_UnorderedSequence -> __ -> 'a1

val sequenceToUnorderedSequence :
  'a1 coq_Sequence -> 'a1 coq_UnorderedSequence

val length' : 'a1 coq_NonemptySequence -> nat

val functionToSequence : nat -> (stn -> 'a1) -> 'a1 coq_Sequence

val functionToUnorderedSequence :
  coq_FiniteSet -> (pr1hSet -> 'a1) -> 'a1 coq_UnorderedSequence

val coq_NonemptySequenceToFunction : 'a1 coq_NonemptySequence -> stn -> 'a1

val coq_NonemptySequenceToSequence :
  'a1 coq_NonemptySequence -> 'a1 coq_Sequence

val composeSequence : ('a1 -> 'a2) -> 'a1 coq_Sequence -> 'a2 coq_Sequence

val composeSequence' :
  nat -> nat -> (stn -> 'a1) -> (stn -> stn) -> 'a1 coq_Sequence

val composeUnorderedSequence :
  ('a1 -> 'a2) -> 'a1 coq_UnorderedSequence -> 'a2 coq_UnorderedSequence

val weqListSequence : ('a1 list, 'a1 coq_Sequence) weq

val transport_stn : nat -> nat -> nat -> hProptoType -> nat paths -> stn paths

val sequenceEquality2 :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (stn -> 'a1 paths) ->
  'a1 coq_Sequence paths

val seq_key_eq_lemma :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat -> hProptoType ->
  hProptoType -> 'a1 paths) -> 'a1 coq_Sequence paths

val seq_key_eq_lemma' :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat -> (hProptoType,
  (hProptoType, 'a1 paths) total2) total2) -> 'a1 coq_Sequence paths

val nil : 'a1 coq_Sequence

val append : 'a1 coq_Sequence -> 'a1 -> 'a1 coq_Sequence

val drop_and_append : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val nil_unique : (stn -> 'a1) -> 'a1 coq_Sequence paths

val iscontr_rect' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths

val iscontr_rect'' : 'a1 iscontr -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute'' : 'a1 iscontr -> 'a2 -> 'a2 paths

val iscontr_adjointness : 'a1 iscontr -> 'a1 -> 'a1 paths paths

val iscontr_rect : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2

val iscontr_rect_compute : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths

val weqsecovercontr' : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq

val nil_length : 'a1 coq_Sequence -> (nat paths, 'a1 coq_Sequence paths) logeq

val drop : 'a1 coq_Sequence -> nat paths neg -> 'a1 coq_Sequence

val drop' : 'a1 coq_Sequence -> 'a1 coq_Sequence paths neg -> 'a1 coq_Sequence

val append_and_drop_fun : nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a1) paths

val drop_and_append' : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val disassembleSequence :
  'a1 coq_Sequence -> (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod

val assembleSequence :
  (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod -> 'a1 coq_Sequence

val assembleSequence_ii2 :
  ('a1, 'a1 coq_Sequence) dirprod -> 'a1 coq_Sequence paths

val coq_SequenceAssembly :
  ('a1 coq_Sequence, (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod) weq

val coq_Sequence_rect :
  'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a1 coq_Sequence -> 'a2

val coq_Sequence_rect_compute_nil :
  'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a2 paths

val append_length : 'a1 coq_Sequence -> 'a1 -> nat paths

val concatenate : 'a1 coq_Sequence binop

val concatenate_length : 'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths

val concatenate_0 :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> 'a1 coq_Sequence paths

val concatenateStep :
  'a1 coq_Sequence -> nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths

val flatten : 'a1 coq_Sequence coq_Sequence -> 'a1 coq_Sequence

val flattenUnorderedSequence :
  'a1 coq_UnorderedSequence coq_UnorderedSequence -> 'a1 coq_UnorderedSequence

val flattenStep' :
  nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> (stn -> 'a1) paths

val flattenStep :
  'a1 coq_Sequence coq_NonemptySequence -> 'a1 coq_Sequence paths

val partition' :
  nat -> (stn -> nat) -> (stn -> 'a1) -> stn -> 'a1 coq_Sequence

val partition :
  nat -> (stn -> nat) -> (stn -> 'a1) -> 'a1 coq_Sequence coq_Sequence

val flatten_partition :
  nat -> (stn -> nat) -> (stn -> 'a1) -> (stn, 'a1) homot

val isassoc_concatenate :
  'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1
  coq_Sequence paths

val reverse : 'a1 coq_Sequence -> 'a1 coq_Sequence

val reversereverse : 'a1 coq_Sequence -> 'a1 coq_Sequence paths

val reverse_index : 'a1 coq_Sequence -> stn -> 'a1 paths

val reverse_index' : 'a1 coq_Sequence -> stn -> 'a1 paths

type 'x nelstruct = (stn, 'x) weq

val nelstructToFunction : nat -> 'a1 nelstruct -> stn -> 'a1

val nelstructonstn : nat -> stn nelstruct

val nelstructweqf : nat -> ('a1, 'a2) weq -> 'a1 nelstruct -> 'a2 nelstruct

val nelstructweqb : nat -> ('a1, 'a2) weq -> 'a2 nelstruct -> 'a1 nelstruct

val nelstructonempty : empty nelstruct

val nelstructonempty2 : 'a1 neg -> 'a1 nelstruct

val nelstructonunit : coq_unit nelstruct

val nelstructoncontr : 'a1 iscontr -> 'a1 nelstruct

val nelstructonbool : bool nelstruct

val nelstructoncoprodwithunit :
  nat -> 'a1 nelstruct -> ('a1, coq_unit) coprod nelstruct

val nelstructoncompl : nat -> 'a1 -> 'a1 nelstruct -> 'a1 compl nelstruct

val nelstructoncoprod :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) coprod nelstruct

val nelstructontotal2 :
  nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1,
  'a2) total2 nelstruct

val nelstructondirprod :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) dirprod nelstruct

val nelstructonfun :
  nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1 -> 'a2) nelstruct

val nelstructonforall :
  nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1 ->
  'a2) nelstruct

val nelstructonweq : nat -> 'a1 nelstruct -> ('a1, 'a1) weq nelstruct

val isofnel : nat -> hProp

val isofneluniv :
  nat -> hProp -> ('a1 nelstruct -> hProptoType) -> hProptoType -> hProptoType

val isofnelstn : nat -> hProptoType

val isofnelweqf : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType

val isofnelweqb : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType

val isofnelempty : hProptoType

val isofnelempty2 : 'a1 neg -> hProptoType

val isofnelunit : hProptoType

val isofnelcontr : 'a1 iscontr -> hProptoType

val isofnelbool : hProptoType

val isofnelcoprodwithunit : nat -> hProptoType -> hProptoType

val isofnelcompl : nat -> 'a1 -> hProptoType -> hProptoType

val isofnelcoprod : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelondirprod : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelonfun : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isofnelonweq : nat -> hProptoType -> hProptoType

type 'x finstruct = (nat, 'x nelstruct) total2

val finstruct_cardinality : 'a1 finstruct -> nat

val finstructToFunction : 'a1 finstruct -> 'a1 nelstruct

val make_finstruct : nat -> (stn, 'a1) weq -> 'a1 finstruct

val finstructonstn : nat -> stn finstruct

val finstructweqf : ('a1, 'a2) weq -> 'a1 finstruct -> 'a2 finstruct

val finstructweqb : ('a1, 'a2) weq -> 'a2 finstruct -> 'a1 finstruct

val finstructonempty : empty finstruct

val finstructonempty2 : 'a1 neg -> 'a1 finstruct

val finstructonunit : coq_unit finstruct

val finstructoncontr : 'a1 iscontr -> 'a1 finstruct

val finstructonbool : bool finstruct

val finstructoncoprodwithunit :
  'a1 finstruct -> ('a1, coq_unit) coprod finstruct

val finstructoncompl : 'a1 -> 'a1 finstruct -> 'a1 compl finstruct

val finstructoncoprod :
  'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) coprod finstruct

val finstructontotal2 :
  'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1, 'a2) total2 finstruct

val finstructondirprod :
  'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) dirprod finstruct

val finstructondecsubset :
  ('a1 -> bool) -> 'a1 finstruct -> ('a1, bool) hfiber finstruct

val finstructonfun : 'a1 finstruct -> 'a2 finstruct -> ('a1 -> 'a2) finstruct

val finstructonforall :
  'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1 -> 'a2) finstruct

val finstructonweq : 'a1 finstruct -> ('a1, 'a1) weq finstruct

val isfinite : hProp

val isfinite_isdeceq : hProptoType -> 'a1 isdeceq

val isfinite_isaset : hProptoType -> 'a1 isaset

val fincard : hProptoType -> nat

val ischoicebasefiniteset : hProptoType -> hProptoType

val isfinitestn : nat -> hProptoType

val isfiniteweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType

val isfiniteweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType

val isfiniteempty : hProptoType

val isfiniteempty2 : 'a1 neg -> hProptoType

val isfiniteunit : hProptoType

val isfinitecontr : 'a1 iscontr -> hProptoType

val isfinitebool : hProptoType

val isfinitecoprodwithunit : hProptoType -> hProptoType

val isfinitecompl : 'a1 -> hProptoType -> hProptoType

val isfinitecoprod : hProptoType -> hProptoType -> hProptoType

val isfinitetotal2 : hProptoType -> ('a1 -> hProptoType) -> hProptoType

val isfinitedirprod : hProptoType -> hProptoType -> hProptoType

val isfinitedecsubset : ('a1 -> bool) -> hProptoType -> hProptoType

val isfinitefun : hProptoType -> hProptoType -> hProptoType

val isfiniteforall : hProptoType -> ('a1 -> hProptoType) -> hProptoType

val isfiniteweq : hProptoType -> hProptoType

val isfinite_to_DecidableEquality : hProptoType -> 'a1 coq_DecidableRelation

val subsetFiniteness : hProptoType -> 'a1 coq_DecidableSubtype -> hProptoType

val fincard_subset : hProptoType -> 'a1 coq_DecidableSubtype -> nat

val fincard_standardSubset : nat -> stn coq_DecidableSubtype -> nat

val bound01 : coq_DecidableProposition -> hProptoType

val tallyStandardSubset : nat -> stn coq_DecidableSubtype -> stn

val tallyStandardSubsetSegment : nat -> stn coq_DecidableSubtype -> stn -> stn

type finite_subset = (pr1hSet hsubtype, hProptoType) total2

val make_finite_subset :
  hSet -> pr1hSet hsubtype -> hProptoType -> finite_subset

val subtype_from_finite_subset : hSet -> finite_subset -> pr1hSet hsubtype

val isfinite_singleton : hSet -> pr1hSet -> hProptoType

val finite_singleton : hSet -> pr1hSet -> finite_subset

val finite_singleton_is_in :
  hSet -> pr1hSet hsubtype -> pr1hSet carrier -> hProptoType

type coq_FiniteSet = (coq_UU, hProptoType) total2

val isfinite_to_FiniteSet : hProptoType -> coq_FiniteSet

val coq_FiniteSet_to_hSet : coq_FiniteSet -> hSet

val coq_FiniteSetSum :
  coq_FiniteSet -> (pr1hSet -> coq_FiniteSet) -> coq_FiniteSet

val cardinalityFiniteSet : coq_FiniteSet -> nat

val standardFiniteSet : nat -> coq_FiniteSet

val subsetFiniteSet :
  coq_FiniteSet -> pr1hSet coq_DecidableSubtype -> coq_FiniteSet

type __ = Obj.t

type pregraph = (coq_UU, __) total2

val make_pregraph : pregraph

type vertex = __

type edge = __

type has_vertexset = vertex isaset

val isaprop_has_vertexset : pregraph -> has_vertexset isaprop

type has_edgesets = vertex -> vertex -> edge isaset

type graph = (pregraph, (has_vertexset, has_edgesets) dirprod) total2

val make_graph : pregraph -> has_vertexset -> has_edgesets -> graph

val pregraph_of_graph : graph -> pregraph

val isaset_vertex : graph -> vertex isaset

val isaset_edge : graph -> vertex -> vertex -> edge isaset

type graph_mor = (vertex -> vertex, vertex -> vertex -> edge -> edge) total2

val make_graph_mor :
  pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge ->
  edge) -> graph_mor

val onvertex : pregraph -> pregraph -> graph_mor -> vertex -> vertex

val onedge :
  pregraph -> pregraph -> graph_mor -> vertex -> vertex -> edge -> edge

val graph_mor_id : pregraph -> graph_mor

val graph_mor_comp :
  pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor -> graph_mor

val make_graph_mor_eq :
  pregraph -> pregraph -> (vertex -> vertex) -> (vertex -> vertex -> edge ->
  edge) -> (vertex -> vertex -> edge -> edge) -> (vertex -> vertex -> edge ->
  edge paths) -> graph_mor paths

val graph_mor_id_left : pregraph -> pregraph -> graph_mor -> graph_mor paths

val graph_mor_id_right : pregraph -> pregraph -> graph_mor -> graph_mor paths

val graph_mor_comp_assoc :
  pregraph -> pregraph -> pregraph -> pregraph -> graph_mor -> graph_mor ->
  graph_mor -> graph_mor paths

val isaset_graph_mor :
  pregraph -> pregraph -> has_vertexset -> has_edgesets -> graph_mor isaset

type __ = Obj.t

type ('v, 'e) issymmetric = 'v -> 'v -> ('e, 'e) weq

type ('v, 'e) gpaths_of_length = __

type ('v, 'e) gpaths = (nat, ('v, 'e) gpaths_of_length) total2

val nil : 'a1 -> ('a1, 'a2) gpaths

val cons : 'a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths

val gpaths_ind :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) gpaths -> 'a3 -> 'a3) -> 'a1
  -> ('a1, 'a2) gpaths -> 'a3

val foldr :
  'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) gpaths
  -> 'a3

val concat :
  'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2) gpaths -> ('a1, 'a2)
  gpaths

val append :
  'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> 'a2 -> ('a1, 'a2) gpaths

val reverse :
  ('a1, 'a2) issymmetric -> 'a1 -> 'a1 -> ('a1, 'a2) gpaths -> ('a1, 'a2)
  gpaths

type ('v, 'e) symmetric_closure = ('e, 'e) coprod

val issymmetric_symmetric_closure :
  ('a1, ('a1, 'a2) symmetric_closure) issymmetric

val reverse_in_closure :
  'a1 -> 'a1 -> ('a1, ('a1, 'a2) symmetric_closure) gpaths -> ('a1, ('a1,
  'a2) symmetric_closure) gpaths

type __ = Obj.t

val weq1 :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, (coq_UU paths, hProptoType paths) total2) weq

val ident_is_prop :
  (__ -> hProp) -> hProptoType -> hProptoType -> coq_UU paths -> hProptoType
  paths isaprop

val weq2 :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU paths, hProptoType
  paths) total2, coq_UU paths) weq

val coq_Id_p_weq_Id :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, coq_UU paths) weq

val iscontr_weq : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq iscontr

val isofhlevel0pathspace : 'a1 iscontr -> 'a2 iscontr -> coq_UU paths iscontr

val isofhlevelSnpathspace : nat -> 'a2 isofhlevel -> coq_UU paths isofhlevel

val isofhlevelpathspace :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> coq_UU paths isofhlevel

type coq_HLevel = (coq_UU, __ isofhlevel) total2

val isofhlevel_HLevel : nat -> coq_HLevel isofhlevel

val coq_UA_for_Predicates :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, ('a1, 'a2) weq) weq

val coq_UA_for_HLevels :
  nat -> coq_HLevel -> coq_HLevel -> (coq_HLevel paths, (__, __) weq) weq

val iskfinite_singleton : 'a1 -> 'a1 carrier iskfinite

val indexed_carrier_to_carrier_union :
  ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 carrier) total2 -> 'a1 carrier

val issurjective_indexed_carrier_to_union :
  ('a2 -> 'a1 hsubtype) -> (('a2, 'a1 carrier) total2, 'a1 carrier)
  issurjective

val reindex_carrier_union :
  ('a2 -> 'a1 hsubtype) -> ('a3 -> 'a2) -> 'a1 carrier -> 'a1 carrier

val issurjective_reindex_carrier_union :
  ('a2 -> 'a1 hsubtype) -> ('a3 -> 'a2) -> ('a3, 'a2) issurjective -> ('a1
  carrier, 'a1 carrier) issurjective

val kfinstruct_union :
  ('a1 -> 'a2 hsubtype) -> 'a1 kfinstruct -> ('a1 -> 'a2 carrier kfinstruct)
  -> 'a2 carrier kfinstruct

val iskfinite_union :
  ('a1 -> 'a2 hsubtype) -> hProptoType -> ('a1 -> 'a2 carrier iskfinite) ->
  'a2 carrier iskfinite

val iskfinite_binary_union :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 carrier iskfinite -> 'a1 carrier
  iskfinite -> 'a1 carrier iskfinite

type 'x kfinite_subtype = ('x hsubtype, 'x carrier iskfinite) total2

val subtype_from_kfinite_subtype : 'a1 kfinite_subtype -> 'a1 hsubtype

val kfinite_subtype_property : 'a1 kfinite_subtype -> 'a1 carrier iskfinite

val make_kfinite_subtype :
  'a1 hsubtype -> 'a1 carrier iskfinite -> 'a1 kfinite_subtype

val kfinite_subtype_union_subproof :
  ('a2 -> 'a1 kfinite_subtype) -> hProptoType -> 'a1 carrier iskfinite

val kfinite_subtype_union :
  ('a2 -> 'a1 kfinite_subtype) -> hProptoType -> 'a1 kfinite_subtype

val kfinite_subtype_singleton : 'a1 -> 'a1 kfinite_subtype
open FiniteSets
open PartA
open PartA0
open Preamble
open Propositions
open StandardFiniteSets

type 'x kfinstruct = (nat, (stn -> 'x, (stn, 'x) issurjective) total2) total2

val make_kfinstruct :
  nat -> (stn -> 'a1) -> (stn, 'a1) issurjective -> 'a1 kfinstruct

val kfinstruct_cardinality : 'a1 kfinstruct -> nat

val kfinstruct_map : 'a1 kfinstruct -> stn -> 'a1

val issurjective_kfinstruct : 'a1 kfinstruct -> (stn, 'a1) issurjective

val kfinstruct_from_surjection :
  ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 kfinstruct -> 'a2 kfinstruct

val kfinstruct_weqf : ('a1, 'a2) weq -> 'a1 kfinstruct -> 'a2 kfinstruct

val kfinstruct_weqb : ('a1, 'a2) weq -> 'a2 kfinstruct -> 'a1 kfinstruct

val kfinstruct_contr : 'a1 iscontr -> 'a1 kfinstruct

val kfinstruct_coprod :
  'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) coprod kfinstruct

val kfinstruct_dirprod :
  'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) dirprod kfinstruct

val kfinstruct_finstruct : 'a1 finstruct -> 'a1 kfinstruct

val kfinstruct_unit : coq_unit kfinstruct

val kfinstruct_bool : bool kfinstruct

val kfinstruct_stn : nat -> stn kfinstruct

val kfinstruct_stn_indexed :
  nat -> (stn -> 'a1 kfinstruct) -> (stn, 'a1) total2 kfinstruct

type 'x iskfinite = hProptoType

val kfinstruct_iskfinite : 'a1 kfinstruct -> 'a1 iskfinite

val iskfinite_weqf : ('a1, 'a2) weq -> 'a1 iskfinite -> 'a2 iskfinite

val iskfinite_weqb : ('a1, 'a2) weq -> 'a2 iskfinite -> 'a1 iskfinite

val iskfinite_from_surjection :
  ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 iskfinite -> 'a2 iskfinite

val iskfinite_unit : coq_unit iskfinite

val iskfinite_bool : bool iskfinite

val iskfinite_contr : 'a1 iscontr -> 'a1 iskfinite

val iskfinite_coprod :
  'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) coprod iskfinite

val iskfinite_dirprod :
  'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) dirprod iskfinite

val iskfinite_isfinite : hProptoType -> 'a1 iskfinite
open NaturalNumbers
open PartA
open PartB
open Preamble
open StandardFiniteSets
open Vectors

type 'a list = (nat, 'a vec) total2

val nil : 'a1 list

val cons : 'a1 -> 'a1 list -> 'a1 list

val list_ind : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val list_ind_compute_2 :
  'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 paths

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val length : 'a1 list -> nat

val foldr1 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 list -> 'a1

val foldr1_map : ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2

val nth : 'a1 list -> stn -> 'a1

val functionToList' : nat -> (stn -> 'a1) -> 'a1 vec

val functionToList : nat -> (stn -> 'a1) -> 'a1 list

val coq_Unnamed_thm : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm0 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 list paths

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val mapStep : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val foldr_nil : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2 paths

val foldr_cons : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 -> 'a1 list -> 'a2 paths

val map_nil : ('a1 -> 'a2) -> 'a2 list paths

val map_cons : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val map_compose : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 list -> 'a3 list paths

val map_idfun : 'a1 list -> 'a1 list paths

val map_homot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 list -> 'a2 list
  paths

val foldr1_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 paths

val foldr1_cons_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths

val foldr1_cons :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 list -> 'a1 paths

val foldr1_map_nil : ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a2 paths

val foldr1_map_cons_nil :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths

val foldr1_map_cons :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 list -> 'a2
  paths

val foldr1_foldr1_map :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2 paths

val concatenate : 'a1 list -> 'a1 list -> 'a1 list

val concatenateStep : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths

val nil_concatenate : 'a1 list -> 'a1 list paths

val concatenate_nil : 'a1 list -> 'a1 list paths

val assoc_concatenate : 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list paths

val map_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a1 list -> 'a2 list paths

val foldr_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val foldr1_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val append : 'a1 -> 'a1 list -> 'a1 list

val appendStep : 'a1 -> 'a1 -> 'a1 list -> 'a1 list paths

val append_concatenate : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths

val map_append : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val reverse : 'a1 list -> 'a1 list

val reverse_nil : 'a1 list paths

val reverseStep : 'a1 -> 'a1 list -> 'a1 list paths

val map_reverse : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val reverse_concatenate : 'a1 list -> 'a1 list -> 'a1 list paths

val reverse_append : 'a1 -> 'a1 list -> 'a1 list paths

val reverse_reverse : 'a1 list -> 'a1 list paths

val flatten : 'a1 list list -> 'a1 list

val flattenStep : 'a1 list -> 'a1 list list -> 'a1 list paths

val isofhlevellist : nat -> 'a1 isofhlevel -> 'a1 list isofhlevel
open PartA
open PartB
open PartC
open Preamble

type 'a maybe = ('a, coq_unit) coprod

val just : 'a1 -> 'a1 maybe

val nothing : 'a1 maybe

val just_injectivity : 'a1 -> 'a1 -> 'a1 maybe paths -> 'a1 paths

val isasetmaybe : 'a1 isaset -> 'a1 maybe isaset

val flatmap : ('a1 -> 'a2 maybe) -> 'a1 maybe -> 'a2 maybe

val flatmap_just : ('a1 -> 'a2 maybe) -> 'a1 -> 'a2 maybe paths

val flatmap_nothing : ('a1 -> 'a2 maybe) -> 'a2 maybe paths

val flatmap_ind : 'a3 -> ('a1 -> 'a3) -> 'a1 maybe -> 'a3
open Nat
open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions

type __ = Obj.t

type coq_Tree =
  (__, (__ -> __ -> nat, (__ -> nat paths, (__ -> __ -> nat paths -> __
  paths, (__ -> __ -> nat paths, (__ -> __ -> __ -> hProptoType, __ -> __ ->
  __ paths neg -> (__, (nat paths, nat paths) dirprod) total2) total2)
  total2) total2) total2) total2) total2

type mt_set = __

val mt_dist : coq_Tree -> __ -> __ -> nat

val mt_refl : coq_Tree -> __ -> nat paths

val mt_anti : coq_Tree -> __ -> __ -> nat paths -> __ paths

val mt_symm : coq_Tree -> __ -> __ -> nat paths

val mt_trans : coq_Tree -> __ -> __ -> __ -> hProptoType

val mt_step :
  coq_Tree -> __ -> __ -> __ paths neg -> (__, (nat paths, nat paths)
  dirprod) total2

val make :
  ('a1 -> 'a1 -> nat) -> ('a1 -> nat paths) -> ('a1 -> 'a1 -> nat paths ->
  'a1 paths) -> ('a1 -> 'a1 -> nat paths) -> ('a1 -> 'a1 -> 'a1 ->
  hProptoType) -> ('a1 -> 'a1 -> 'a1 paths neg -> ('a1, (nat paths, nat
  paths) dirprod) total2) -> coq_Tree

val mt_path_refl : coq_Tree -> mt_set -> mt_set -> mt_set paths -> nat paths

val tree_deceq : coq_Tree -> mt_set isdeceq

val tree_isaset : coq_Tree -> mt_set isaset

val step : coq_Tree -> mt_set -> mt_set -> mt_set paths neg -> mt_set

val tree_induction :
  coq_Tree -> mt_set -> 'a1 -> (mt_set -> mt_set paths neg -> 'a1 -> 'a1) ->
  mt_set -> 'a1

val nat_tree : coq_Tree
open DecSet
open Lists
open Maybe
open NaturalNumbers
open PartA
open Preamble
open Propositions
open Sets
open Vectors

val head : 'a1 list -> 'a1 maybe

val tail : 'a1 list -> 'a1 list maybe

val list_head_cons : 'a1 -> 'a1 list -> 'a1 maybe paths

val list_tail_cons : 'a1 -> 'a1 list -> 'a1 list maybe paths

val cons_inj1 :
  'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 paths

val cons_inj2 :
  'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 list paths

val negpathsconsnil : 'a1 -> 'a1 list -> 'a1 list paths neg

val negpathsnilcons : 'a1 -> 'a1 list -> 'a1 list paths neg

val length_cons : 'a1 -> 'a1 list -> nat paths

val length_zero_back : 'a1 list -> nat paths -> 'a1 list paths

val length_one_back : 'a1 list -> nat paths -> ('a1, 'a1 list paths) total2

val length_concatenate : 'a1 list -> 'a1 list -> nat paths

val length_sublist1 : 'a1 list -> 'a1 list -> hProptoType

val length_sublist2 : 'a1 list -> 'a1 list -> hProptoType

val length_map : 'a1 list -> ('a1 -> 'a2) -> nat paths

val listset : hSet -> hSet

val fill : 'a1 -> nat -> 'a1 list

val map_const : 'a2 -> 'a1 list -> 'a2 list paths

val length_fill : 'a1 -> nat -> nat paths

val drop : 'a1 list -> nat -> 'a1 list

val drop_nil : nat -> 'a1 list paths

val drop_zero : 'a1 list -> 'a1 list paths

val drop_step : 'a1 -> 'a1 list -> nat -> 'a1 list paths

val drop_full : 'a1 list -> 'a1 list paths

val drop_concatenate :
  'a1 list -> 'a1 list -> nat -> hProptoType -> 'a1 list paths

val length_drop : 'a1 list -> nat -> nat paths

val prefix_remove :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe

val prefix_remove_stepeq :
  decSet -> pr1decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list
  maybe paths

val prefix_remove_stepneq :
  decSet -> pr1decSet -> pr1decSet -> pr1decSet paths neg -> pr1decSet list
  -> pr1decSet list -> pr1decSet list maybe paths

val prefix_remove_stepback :
  decSet -> pr1decSet -> pr1decSet -> pr1decSet list -> pr1decSet list ->
  pr1decSet list maybe paths neg -> pr1decSet paths

val prefix_remove_back :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
  list maybe paths -> pr1decSet list paths

val prefix_remove_self :
  decSet -> pr1decSet list -> pr1decSet list maybe paths

type isprefix = pr1decSet list maybe paths neg

val isprefix_self : decSet -> pr1decSet list -> isprefix

val prefix_remove_concatenate :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
  list -> pr1decSet list maybe paths -> pr1decSet list maybe paths

val prefix_remove_concatenate2 :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> hProptoType
  -> pr1decSet list maybe paths -> pr1decSet list maybe paths

val prefix_remove_prefix :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths

val prefix_remove_drop :
  decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths
  neg -> pr1decSet list maybe paths
