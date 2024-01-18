
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


type cgraph = (precgraph, (node isaset, arc isaset) dirprod) total2

val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph

val precgraph_of_cgraph : cgraph -> precgraph

val isaset_node : cgraph -> node isaset

val node_set : cgraph -> hSet

val isaset_arc : cgraph -> arc isaset

val arc_set : cgraph -> hSet

type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod

type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2




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
open NaturalNumbers
open PartA
open PartA0
open PartB
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t

type _UU2115_ = nat

module Uniqueness :
 sig
  val helper_A :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1 paths, ('a1
    paths, nat -> 'a1 paths) dirprod) weq

  val helper_B :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> ((nat -> 'a1) paths, ('a1
    paths, nat -> 'a1 paths) dirprod) weq

  val helper_C :
    'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, (nat -> 'a1) paths) total2,
    (nat -> 'a1, ('a1 paths, nat -> 'a1 paths) dirprod) total2) weq

  val hNatRecursionUniq :
    'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1, ('a1 paths, nat -> 'a1 paths)
    dirprod) total2 iscontr

  val helper_D :
    'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, ('a1 paths, nat -> 'a1 paths)
    dirprod) total2, ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1) hfiber) weq

  val hNatRecursion_weq :
    (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1) weq
 end




val nat_dist_symm : nat -> nat -> nat paths

val nat_dist_ge : nat -> nat -> hProptoType -> nat paths

val nat_dist_0m : nat -> nat paths

val nat_dist_m0 : nat -> nat paths

val nat_dist_plus : nat -> nat -> nat paths

val nat_dist_le : nat -> nat -> hProptoType -> nat paths

val nat_dist_minus : nat -> nat -> hProptoType -> nat paths

val nat_dist_gt : nat -> nat -> hProptoType -> nat paths

val nat_dist_S : nat -> nat -> nat paths

val natminuseqlr : nat -> nat -> nat -> hProptoType -> nat paths -> nat paths

val nat_dist_between_le :
  nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
  nat paths) dirprod) total2

val nat_dist_between_ge :
  nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
  nat paths) dirprod) total2

val nat_dist_between :
  nat -> nat -> nat -> nat -> nat paths -> (nat, (nat paths, nat paths)
  dirprod) total2

val natleorle : nat -> nat -> (hProptoType, hProptoType) coprod

val nat_dist_trans : nat -> nat -> nat -> hProptoType

val plusmn0n0 : nat -> nat -> nat paths -> nat paths

val plusmn0m0 : nat -> nat -> nat paths -> nat paths

val natminus0le : nat -> nat -> nat paths -> hProptoType

val minusxx : nat -> nat paths

val minusSxx : nat -> nat paths

val natminusminus : nat -> nat -> hProptoType -> nat paths

val natplusminus : nat -> nat -> nat -> nat paths -> nat paths

val natleplusminus : nat -> nat -> nat -> hProptoType -> hProptoType

val natltminus1 : nat -> nat -> hProptoType -> hProptoType

val natminusminusassoc : nat -> nat -> nat -> nat paths

val natminusplusltcomm :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val nat_le_diff :
  _UU2115_ -> _UU2115_ -> hProptoType -> (_UU2115_, nat paths) total2
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

val natnegpaths : nat -> nat -> hProp

val natneq_hProp : nat -> nat -> hProp

val negpaths0sx : nat -> nat paths neg

val negpathssx0 : nat -> nat paths neg

val invmaponpathsS : nat -> nat -> nat paths -> nat paths

val noeqinjS : nat -> nat -> nat paths neg -> nat paths neg

val natneq_iff_neq : nat -> nat -> (nat paths neg, hProptoType) logeq

val nat_neq_to_nopath : nat -> nat -> hProptoType -> nat paths neg

val nat_nopath_to_neq : nat -> nat -> nat paths neg -> hProptoType

val natneq0sx : nat -> hProptoType

val natneqsx0 : nat -> hProptoType

val natneqinjS : nat -> nat -> hProptoType -> hProptoType

val isirrefl_natneq : nat -> hProptoType neg

val issymm_natneq : nat -> nat -> hProptoType -> hProptoType

val isdeceqnat : nat isdeceq

val isisolatedn : nat -> nat isisolated

val isasetnat : nat isaset

val natset : hSet

val nat_eq_or_neq : nat -> nat -> (nat paths, hProptoType) coprod

val isdecrel_natneq : nat isdecrel

val nateq : nat -> nat -> hProp

val isdecrelnateq : nat isdecrel

val natdeceq : nat decrel

val natdecneq : nat decrel

val natboolneq : nat brel

val isinclS : (nat, nat) isincl

val isdecinclS : (nat, nat) isdecincl

val natgtb : nat -> nat -> bool

val natgth : nat -> nat -> hProp

val negnatgth0n : nat -> hProptoType neg

val natgthsnn : nat -> hProptoType

val natgthsn0 : nat -> hProptoType

val negnatgth0tois0 : nat -> hProptoType neg -> nat paths

val natneq0togth0 : nat -> hProptoType -> hProptoType

val nat1gthtois0 : nat -> hProptoType -> nat paths

val istransnatgth :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isirreflnatgth : nat -> hProptoType neg

val natgthtoneq : nat -> nat -> hProptoType -> hProptoType

val isasymmnatgth : nat -> nat -> hProptoType -> hProptoType -> empty

val isantisymmnegnatgth :
  nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths

val isdecrelnatgth : nat isdecrel

val natgthdec : nat decrel

val isnegrelnatgth : nat isnegrel

val iscoantisymmnatgth :
  nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod

val iscotransnatgth :
  nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natlth : nat -> nat -> hProp

val negnatlthn0 : nat -> hProptoType neg

val natlthnsn : nat -> hProptoType

val negnat0lthtois0 : nat -> hProptoType neg -> nat paths

val natneq0to0lth : nat -> hProptoType -> hProptoType

val natlth1tois0 : nat -> hProptoType -> nat paths

val istransnatlth :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isirreflnatlth : nat -> hProptoType neg

val natlthtoneq : nat -> nat -> hProptoType -> hProptoType

val isasymmnatlth : nat -> nat -> hProptoType -> hProptoType -> empty

val isantisymmnegnattth :
  nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths

val isdecrelnatlth : nat isdecrel

val natlthdec : nat decrel

val isnegrelnatlth : nat isnegrel

val iscoantisymmnatlth :
  nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod

val iscotransnatlth :
  nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natleh : nat -> nat -> hProp

val isdecrelnatleh : nat isdecrel

val negnatlehsn0 : nat -> hProptoType neg

val natlehneggth : nat -> nat -> hProptoType -> hProptoType neg

val natgthnegleh : nat -> nat -> hProptoType -> hProptoType neg

val negnatSleh : nat -> hProptoType neg

val negnatgthtoleh : nat -> nat -> hProptoType neg -> hProptoType

val negnatlehtogth : nat -> nat -> hProptoType neg -> hProptoType

val neggth_logeq_leh : nat -> nat -> (hProptoType neg, hProptoType) logeq

val natleh0tois0 : nat -> hProptoType -> nat paths

val natleh0n : nat -> hProptoType

val negnatlehsnn : nat -> hProptoType neg

val istransnatleh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isreflnatleh : nat -> hProptoType

val isantisymmnatleh : nat isantisymm

val natlehdec : nat decrel

val isnegrelnatleh : nat isnegrel

val natlthtoleh : nat -> nat -> hProptoType -> hProptoType

val iscoasymmnatleh : nat -> nat -> hProptoType neg -> hProptoType

val istotalnatleh : nat istotal

val natgeh : nat -> nat -> hProp

val nat0gehtois0 : nat -> hProptoType -> nat paths

val natgehn0 : nat -> hProptoType

val negnatgeh0sn : nat -> hProptoType neg

val negnatgehnsn : nat -> hProptoType neg

val istransnatgeh :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val isreflnatgeh : nat -> hProptoType

val isantisymmnatgeh : nat -> nat -> hProptoType -> hProptoType -> nat paths

val isdecrelnatgeh : nat isdecrel

val natgehdec : nat decrel

val isnegrelnatgeh : nat isnegrel

val iscoasymmnatgeh : nat -> nat -> hProptoType neg -> hProptoType

val istotalnatgeh : nat istotal

val natgthtogeh : nat -> nat -> hProptoType -> hProptoType

val natlehtonegnatgth : nat -> nat -> hProptoType -> hProptoType neg

val natgthtonegnatleh : nat -> nat -> hProptoType -> hProptoType neg

val natgehtonegnatlth : nat -> nat -> hProptoType -> hProptoType neg

val natlthtonegnatgeh : nat -> nat -> hProptoType -> hProptoType neg

val negnatgehtolth : nat -> nat -> hProptoType neg -> hProptoType

val negnatlthtogeh : nat -> nat -> hProptoType neg -> hProptoType

val natlehnsn : nat -> hProptoType

val natgehsnn : nat -> hProptoType

val natgthorleh : nat -> nat -> (hProptoType, hProptoType) coprod

val natlthorgeh : nat -> nat -> (hProptoType, hProptoType) coprod

val natchoice0 : nat -> (nat paths, hProptoType) coprod

val natneqchoice :
  nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod

val natlehchoice :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthgehtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehgthtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthlehtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehlthtrans :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natltltSlt :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthtogehsn : nat -> nat -> hProptoType -> hProptoType

val natgthsntogeh : nat -> nat -> hProptoType -> hProptoType

val natgehtogthsn : nat -> nat -> hProptoType -> hProptoType

val natgehsntogth : nat -> nat -> hProptoType -> hProptoType

val natlthtolehsn : nat -> nat -> hProptoType -> hProptoType

val natlehsntolth : nat -> nat -> hProptoType -> hProptoType

val natlehtolthsn : nat -> nat -> hProptoType -> hProptoType

val natlthsntoleh : nat -> nat -> hProptoType -> hProptoType

val natlehchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlthchoice2 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natplusl0 : nat -> nat paths

val natplusr0 : nat -> nat paths

val natplusnsm : nat -> nat -> nat paths

val natpluscomm : nat -> nat -> nat paths

val natplusassoc : nat -> nat -> nat -> nat paths

val natgthtogths : nat -> nat -> hProptoType -> hProptoType

val negnatgthmplusnm : nat -> nat -> hProptoType neg

val negnatgthnplusnm : nat -> nat -> hProptoType neg

val natgthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandplusm : nat -> nat -> hProptoType -> hProptoType

val natlthtolths : nat -> nat -> hProptoType -> hProptoType

val negnatlthplusnmm : nat -> nat -> hProptoType neg

val negnatlthplusnmn : nat -> nat -> hProptoType neg

val natlthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandplusm : nat -> nat -> hProptoType -> hProptoType

val natlehtolehs : nat -> nat -> hProptoType -> hProptoType

val natlehmplusnm : nat -> nat -> hProptoType

val plus_n_Sm : nat -> nat -> nat paths

val natlehnplusnm : nat -> nat -> hProptoType

val natlehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplus :
  nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehtogehs : nat -> nat -> hProptoType -> hProptoType

val natgehplusnmm : nat -> nat -> hProptoType

val natgehplusnmn : nat -> nat -> hProptoType

val natgehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandpluslinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandplusrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthtogthp1 : nat -> nat -> hProptoType -> hProptoType

val natlthtolthp1 : nat -> nat -> hProptoType -> hProptoType

val natlehtolehp1 : nat -> nat -> hProptoType -> hProptoType

val natgehtogehp1 : nat -> nat -> hProptoType -> hProptoType

val natgthtogehp1 : nat -> nat -> hProptoType -> hProptoType

val natgthp1togeh : nat -> nat -> hProptoType -> hProptoType

val natlehp1tolth : nat -> nat -> hProptoType -> hProptoType

val natlthtolehp1 : nat -> nat -> hProptoType -> hProptoType

val natlthp1toleh : nat -> nat -> hProptoType -> hProptoType

val natgehp1togth : nat -> nat -> hProptoType -> hProptoType

val natlehchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgehchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natgthchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlthchoice3 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val natlehchoice4 :
  nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod

val pathsitertoplus : nat -> nat -> nat paths

val isinclnatplusr : nat -> (nat, nat) isincl

val isinclnatplusl : nat -> (nat, nat) isincl

val natplusrcan : nat -> nat -> nat -> nat paths -> nat paths

val natpluslcan : nat -> nat -> nat -> nat paths -> nat paths

val iscontrhfibernatplusr :
  nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val iscontrhfibernatplusl :
  nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val neghfibernatplusr : nat -> nat -> hProptoType -> (nat, nat) hfiber neg

val isdecinclnatplusr : nat -> (nat, nat) isdecincl

val minuseq0 : nat -> nat -> hProptoType -> nat paths

val minuseq0' : nat -> nat paths

val minusgth0 : nat -> nat -> hProptoType -> hProptoType

val minusgth0inv : nat -> nat -> hProptoType -> hProptoType

val natminuseqn : nat -> nat paths

val natminuslehn : nat -> nat -> hProptoType

val natminusgehn : nat -> nat -> hProptoType

val natminuslthn : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natminuslthninv : nat -> nat -> hProptoType -> hProptoType

val minusplusnmm : nat -> nat -> hProptoType -> nat paths

val minusplusnmmineq : nat -> nat -> hProptoType

val plusminusnmm : nat -> nat -> nat paths

val minusminusmmn : nat -> nat -> hProptoType -> nat paths

val natgthtogthm1 : nat -> nat -> hProptoType -> hProptoType

val natlthtolthm1 : nat -> nat -> hProptoType -> hProptoType

val natlehtolehm1 : nat -> nat -> hProptoType -> hProptoType

val natgehtogehm1 : nat -> nat -> hProptoType -> hProptoType

val natgthtogehm1 : nat -> nat -> hProptoType -> hProptoType

val natgehandminusr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandminusl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandminusrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandminusl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natmult0n : nat -> nat paths

val natmultn0 : nat -> nat paths

val multsnm : nat -> nat -> nat paths

val multnsm : nat -> nat -> nat paths

val natmultcomm : nat -> nat -> nat paths

val natrdistr : nat -> nat -> nat -> nat paths

val natldistr : nat -> nat -> nat -> nat paths

val natmultassoc : nat -> nat -> nat -> nat paths

val natmultl1 : nat -> nat paths

val natmultr1 : nat -> nat paths

val natplusnonzero : nat -> nat -> hProptoType -> hProptoType

val natneq0andmult : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natneq0andmultlinv : nat -> nat -> hProptoType -> hProptoType

val natneq0andmultrinv : nat -> nat -> hProptoType -> hProptoType

val natgthandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgthandmultlinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natgthandmultrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlthandmultlinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlthandmultrinv : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType

val natlehandmultlinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natlehandmultrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType

val natgehandmultlinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natgehandmultrinv :
  nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natdivrem : nat -> nat -> (nat, nat) dirprod

val natdiv : nat -> nat -> nat

val natrem : nat -> nat -> nat

val lthnatrem : nat -> nat -> hProptoType -> hProptoType

val natdivremrule : nat -> nat -> hProptoType -> nat paths

val natlehmultnatdiv : nat -> nat -> hProptoType -> hProptoType

val natdivremunique :
  nat -> nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths
  -> (nat paths, nat paths) dirprod

val natdivremandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
  dirprod

val natdivandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natremandmultl :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natdivremandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
  dirprod

val natdivandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natremandmultr :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths

val natpower : nat -> nat -> nat

val factorial : nat -> nat

val di : nat -> nat -> nat

val di_eq1 : nat -> nat -> hProptoType -> nat paths

val di_eq2 : nat -> nat -> hProptoType -> nat paths

val di_neq_i : nat -> nat -> hProptoType

val natlehdinsn : nat -> nat -> hProptoType

val natgehdinn : nat -> nat -> hProptoType

val isincldi : nat -> (nat, nat) isincl

val neghfiberdi : nat -> (nat, nat) hfiber neg

val iscontrhfiberdi : nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr

val isdecincldi : nat -> (nat, nat) isdecincl

val si : nat -> nat -> nat

val natleh_neq : nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natminusminus : nat -> nat -> nat -> nat paths

val natltplusS : nat -> nat -> hProptoType

val nat_split : nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType

val natplusminusle : nat -> nat -> nat -> hProptoType -> nat paths

val natdiffplusdiff :
  nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths
open NaturalNumbers
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

type __ = Obj.t

type 'p negProp = (coq_UU, (__ isaprop, ('p neg, __) logeq) dirprod) total2

val negProp_to_isaprop : 'a1 negProp -> __ isaprop

val negProp_to_hProp : 'a1 negProp -> hProp

val negProp_to_iff : 'a1 negProp -> ('a1 neg, hProptoType) logeq

val negProp_to_neg : 'a1 negProp -> hProptoType -> 'a1 neg

val neg_to_negProp : 'a1 negProp -> 'a1 neg -> hProptoType

type ('x, 'p) negPred = 'x -> 'p negProp

type ('x, 'p) negReln = 'x -> 'x -> 'p negProp

type 'x neqProp = 'x paths negProp

type 'x neqPred = 'x -> 'x paths negProp

type 'x neqReln = 'x -> 'x -> 'x paths negProp

val negProp_to_complementary :
  'a1 negProp -> (('a1, hProptoType) coprod, ('a1, hProptoType)
  complementary) logeq

val negProp_to_uniqueChoice :
  'a1 negProp -> (('a1 isaprop, ('a1, hProptoType) coprod) dirprod, ('a1,
  hProptoType) coprod iscontr) logeq

type 'x isisolated_ne = 'x -> ('x paths, hProptoType) coprod

val isisolated_to_isisolated_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 isisolated_ne

val isisolated_ne_to_isisolated :
  'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 isisolated

type 't isolated_ne = ('t, 't isisolated_ne) total2

val make_isolated_ne :
  'a1 -> 'a1 neqReln -> 'a1 isisolated_ne -> 'a1 isolated_ne

val pr1isolated_ne : 'a1 neqReln -> 'a1 isolated_ne -> 'a1

val isaproppathsfromisolated_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 -> 'a1 paths isaprop

type 'x compl_ne = ('x, hProptoType) total2

val make_compl_ne : 'a1 -> 'a1 neqPred -> 'a1 -> hProptoType -> 'a1 compl_ne

val pr1compl_ne : 'a1 -> 'a1 neqPred -> 'a1 compl_ne -> 'a1

val make_negProp : 'a1 negProp

val make_neqProp : 'a1 -> 'a1 -> 'a1 neqProp

val isinclpr1compl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1) isincl

val compl_ne_weq_compl : 'a1 -> 'a1 neqPred -> ('a1 compl, 'a1 compl_ne) weq

val compl_weq_compl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1 compl) weq

val recompl_ne : 'a1 -> 'a1 neqPred -> ('a1 compl_ne, coq_unit) coprod -> 'a1

val maponcomplincl_ne :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 neqPred -> 'a2 neqPred ->
  'a1 compl_ne -> 'a2 compl_ne

val weqoncompl_ne :
  ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> ('a1 compl_ne, 'a2
  compl_ne) weq

val weqoncompl_ne_compute :
  ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> 'a1 compl_ne -> 'a2
  paths

val invrecompl_ne :
  'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 -> ('a1 compl_ne, coq_unit)
  coprod

val isweqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) isweq

val isweqrecompl_ne' :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) isweq

val weqrecompl_ne :
  'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
  'a1) weq

val isweqrecompl' :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq

val iscotrans_to_istrans_negReln :
  'a1 hrel -> ('a1, hProptoType) negReln -> 'a1 isdeccotrans -> 'a1 istrans

val natneq : nat -> nat -> nat paths negProp

type nat_compl = nat compl_ne

val weqdicompl : nat -> (nat, nat_compl) weq
open PartA
open PartB
open Preamble
open Propositions

val hequiv : hProp -> hProp -> hProp

val total2_hProp : hProp -> (hProptoType -> hProp) -> hProp

type 'x paths_from = 'x coconusfromt

val point_to : 'a1 -> 'a1 paths_from -> 'a1

val paths_from_path : 'a1 -> 'a1 paths_from -> 'a1 paths

type 'x paths' = 'x paths

val idpath' : 'a1 -> 'a1 paths'

type 'x paths_to = 'x coconustot

val point_from : 'a1 -> 'a1 paths_to -> 'a1

val paths_to_path : 'a1 -> 'a1 paths_to -> 'a1 paths

val iscontr_paths_to : 'a1 -> 'a1 paths_to iscontr

val iscontr_paths_from : 'a1 -> 'a1 paths_from iscontr

val paths_to_prop : 'a1 -> hProp

val paths_from_prop : 'a1 -> hProp

val squash_path : 'a1 -> 'a1 -> hProptoType paths
open Notations
open PartA
open PartB
open PartD
open Preamble
open Propositions

type ('x, 'y) nullHomotopyTo = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyTo = ('y, ('x, 'y) nullHomotopyTo) total2

val coq_NullHomotopyTo_center :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> 'a2

val coq_NullHomotopyTo_path :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> ('a1, 'a2) nullHomotopyTo

type ('x, 'y) nullHomotopyFrom = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyFrom = ('y, ('x, 'y) nullHomotopyFrom) total2

val coq_NullHomotopyFrom_center :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> 'a2

val coq_NullHomotopyFrom_path :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> ('a1, 'a2)
  nullHomotopyFrom

val nullHomotopyTo_transport :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> 'a2 -> 'a2 paths -> 'a1
  -> 'a2 paths paths

val isaset_NullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo isaset

val isaprop_nullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo isaprop

val isaprop_NullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> hProptoType -> ('a1, 'a2) coq_NullHomotopyTo
  isaprop

val cone_squash_map :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> hProptoType -> 'a2

val coq_Unnamed_thm :
  'a2 -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1 -> 'a2) paths
open DecidablePropositions
open FiniteSets
open NaturalNumbers
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open UnivalenceAxiom

val isTotalOrder : hSet -> pr1hSet hrel -> hProp

val tot_nge_to_le :
  hSet -> pr1hSet hrel -> pr1hSet istotal -> pr1hSet -> pr1hSet ->
  hProptoType -> hProptoType

val tot_nle_iff_gt :
  hSet -> pr1hSet hrel -> hProptoType -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq

type isSmallest = pr1hSet -> hProptoType

type isBiggest = pr1hSet -> hProptoType

type isMinimal = pr1hSet -> hProptoType -> pr1hSet paths

type isMaximal = pr1hSet -> hProptoType -> pr1hSet paths

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> hProptoType) dirprod

val isaprop_isSmallest : coq_Poset -> pr1hSet -> isSmallest isaprop

val isaprop_isBiggest : coq_Poset -> pr1hSet -> isBiggest isaprop

val coq_Poset_univalence_map :
  coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence

val posetStructureIdentity :
  hSet -> coq_PartialOrder -> coq_PartialOrder -> (isPosetEquivalence,
  coq_PartialOrder paths) logeq

val posetTransport_weq :
  coq_Poset -> coq_Poset -> ((hSet, coq_PartialOrder) coq_PathPair,
  coq_PosetEquivalence) weq

val coq_Poset_univalence_0 :
  coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq

val coq_Poset_univalence :
  coq_Poset -> coq_Poset -> (coq_Poset paths, coq_PosetEquivalence) weq

val coq_Poset_univalence_compute :
  coq_Poset -> coq_Poset -> coq_Poset paths -> coq_PosetEquivalence paths

val coq_PosetEquivalence_rect :
  coq_Poset -> coq_Poset -> (coq_Poset paths -> 'a1) -> coq_PosetEquivalence
  -> 'a1

val isMinimal_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> isMinimal -> coq_PosetEquivalence ->
  isMinimal

val isMaximal_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> isMaximal -> coq_PosetEquivalence ->
  isMaximal

val consecutive_preserved :
  coq_Poset -> coq_Poset -> pr1hSet -> pr1hSet -> consecutive ->
  coq_PosetEquivalence -> consecutive

type coq_OrderedSet = (coq_Poset, pr1hSet istotal) total2

val underlyingPoset : coq_OrderedSet -> coq_Poset

val coq_Poset_lessthan : coq_Poset -> pr1hSet -> pr1hSet -> hProp

val coq_OrderedSet_isrefl : coq_OrderedSet -> pr1hSet -> hProptoType

val coq_OrderedSet_isantisymm :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType ->
  pr1hSet paths

val coq_OrderedSet_istotal :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> hProptoType

val isdeceq_isdec_ordering :
  coq_OrderedSet -> pr1hSet isdeceq -> isdec_ordering

val isfinite_isdec_ordering : coq_OrderedSet -> hProptoType -> isdec_ordering

val isdeceq_isdec_lessthan :
  coq_OrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType
  decidable

val isfinite_isdec_lessthan :
  coq_OrderedSet -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType decidable

val isincl_underlyingPoset : (coq_OrderedSet, coq_Poset) isincl

val underlyingPoset_weq :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths, coq_Poset paths)
  weq

val smallestUniqueness :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> isSmallest -> isSmallest -> pr1hSet
  paths

val biggestUniqueness :
  coq_OrderedSet -> pr1hSet -> pr1hSet -> isBiggest -> isBiggest -> pr1hSet
  paths

val coq_OrderedSet_univalence :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths,
  coq_PosetEquivalence) weq

val coq_OrderedSetEquivalence_rect :
  coq_OrderedSet -> coq_OrderedSet -> (coq_OrderedSet paths -> 'a1) ->
  coq_PosetEquivalence -> 'a1

type coq_FiniteOrderedSet = (coq_OrderedSet, hProptoType) total2

val underlyingOrderedSet : coq_FiniteOrderedSet -> coq_OrderedSet

val finitenessProperty : coq_FiniteOrderedSet -> hProptoType

val underlyingFiniteSet : coq_FiniteOrderedSet -> coq_FiniteSet

val istotal_FiniteOrderedSet : coq_FiniteOrderedSet -> pr1hSet istotal

val coq_FiniteOrderedSet_isdeceq : coq_FiniteOrderedSet -> pr1hSet isdeceq

val coq_FiniteOrderedSet_isdec_ordering :
  coq_FiniteOrderedSet -> isdec_ordering

val coq_FiniteOrderedSetDecidableOrdering :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableEquality :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableInequality :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSetDecidableLessThan :
  coq_FiniteOrderedSet -> pr1hSet coq_DecidableRelation

val coq_FiniteOrderedSet_segment :
  coq_FiniteOrderedSet -> pr1hSet -> coq_FiniteSet

val height : coq_FiniteOrderedSet -> pr1hSet -> nat

val standardFiniteOrderedSet : nat -> coq_FiniteOrderedSet

val inducedPartialOrder :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a2 hrel -> 'a2 isPartialOrder ->
  'a1 isPartialOrder

val inducedPartialOrder_weq :
  ('a1, 'a2) weq -> 'a2 hrel -> 'a2 isPartialOrder -> 'a1 isPartialOrder

val transportFiniteOrdering :
  nat -> ('a1, pr1hSet) weq -> coq_FiniteOrderedSet

val lexicographicOrder :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet hrel

val lex_isrefl :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  (pr1hSet -> pr1hSet isrefl) -> pr1hSet isrefl

val lex_istrans :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isantisymm -> pr1hSet istrans -> (pr1hSet -> pr1hSet istrans) ->
  pr1hSet istrans

val lex_isantisymm :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isantisymm -> (pr1hSet -> pr1hSet isantisymm) -> pr1hSet isantisymm

val lex_istotal :
  hSet -> (pr1hSet -> hSet) -> pr1hSet hrel -> (pr1hSet -> pr1hSet hrel) ->
  pr1hSet isdeceq -> pr1hSet istotal -> (pr1hSet -> pr1hSet istotal) ->
  pr1hSet istotal

val concatenateFiniteOrderedSets :
  coq_FiniteOrderedSet -> (pr1hSet -> coq_FiniteOrderedSet) ->
  coq_FiniteOrderedSet

type coq_FiniteStructure = (nat, coq_PosetEquivalence) total2

type isLattice =
  (pr1hSet isPartialOrder, (pr1hSet -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq, (pr1hSet -> pr1hSet -> pr1hSet -> (hProptoType,
  hProptoType) logeq, coq_unit) total2) total2) total2

type istrans2 =
  (pr1hSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType ->
  hProptoType, (pr1hSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType
  -> hProptoType, coq_unit) total2) total2

type 'x iswklin = 'x -> 'x -> 'x -> hProptoType -> hProptoType

type isComputablyOrdered =
  (isLattice, (istrans2, (pr1hSet istrans, (pr1hSet isirrefl, (pr1hSet
  iscotrans, coq_unit) total2) total2) total2) total2) total2

val apart_isirrefl :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet isirrefl

val lt_implies_le :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType

val apart_implies_ne :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths
  neg

val tightness :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> (hProptoType, hProptoType)
  logeq

val ne_implies_dnegapart :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> pr1hSet -> pr1hSet -> pr1hSet paths neg ->
  hProptoType dneg

val ne_implies_apart :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> pr1hSet paths
  neg -> hProptoType

val trichotomy :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet -> pr1hSet -> hProptoType

val le_istotal :
  hSet -> pr1hSet hrel -> pr1hSet binop -> pr1hSet binop ->
  isComputablyOrdered -> hProptoType -> pr1hSet istotal
open HLevels
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type __ = Obj.t

val maponpaths_1 : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val maponpaths_2 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths

val maponpaths_12 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths
  -> 'a3 paths

val maponpaths_3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a4
  paths

val maponpaths_123 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2
  paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 paths

val maponpaths_13 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3
  -> 'a3 paths -> 'a4 paths

val maponpaths_4 :
  ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3
  -> 'a4 -> 'a5 paths

val maponpaths_1234 :
  ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2
  -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 -> 'a4 -> 'a4 paths -> 'a5
  paths

val maponpaths_for_constant_function :
  'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths

val base_paths_pair_path_in2 :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths

val transportf_transpose_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportb_transpose_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_transpose_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportb_transpose_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_pathsinv0 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transportf_comp_lemma :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
  'a2 paths

val transportf_comp_lemma_hset :
  'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a1 isaset -> 'a2 paths -> 'a2 paths

val transportf_bind :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
  'a2 paths

val pathscomp0_dep :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2
  paths -> 'a2 paths -> 'a2 paths

val transportf_set : 'a1 -> 'a1 paths -> 'a2 -> 'a1 isaset -> 'a2 paths

val transportf_pair :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths

val weqhomot :
  ('a1 -> 'a2) -> ('a1, 'a2) weq -> ('a1, 'a2) homot -> ('a1, 'a2) isweq

val invmap_eq : ('a1, 'a2) weq -> 'a2 -> 'a1 -> 'a2 paths -> 'a1 paths

val pr1_transportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> 'a2 paths

val pr2_transportf :
  'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) dirprod -> 'a3 paths

val coprodcomm_coprodcomm : ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths

val sumofmaps_funcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a5) -> ('a3 -> 'a4) -> ('a4 -> 'a5) -> (('a1, 'a3)
  coprod, 'a5) homot

val sumofmaps_homot :
  ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3)
  homot -> ('a2, 'a3) homot -> (('a1, 'a2) coprod, 'a3) homot

val coprod_rect_compute_1 : ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a1 -> 'a3 paths

val coprod_rect_compute_2 : ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a2 -> 'a3 paths

val flipsec : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

val isweq_flipsec : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) isweq

val flipsec_weq : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) weq

val empty_hlevel : nat -> empty isofhlevel

val empty_HLevel : nat -> coq_HLevel

val coq_HLevel_fun : nat -> coq_HLevel -> coq_HLevel -> coq_HLevel

val isofhlevel_hsubtype :
  nat -> 'a1 isofhlevel -> 'a1 hsubtype -> 'a1 carrier isofhlevel

val weqtotal2 :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) weq

val weq_subtypes' :
  ('a1, 'a2) weq -> ('a1, 'a3) isPredicate -> ('a2, 'a4) isPredicate -> ('a1
  -> ('a3, 'a4) logeq) -> (('a1, 'a3) total2, ('a2, 'a4) total2) weq

val weq_subtypes_iff :
  ('a1, 'a2) isPredicate -> ('a1, 'a3) isPredicate -> ('a1 -> ('a2, 'a3)
  logeq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq

val hlevel_total2 :
  nat -> ('a1, 'a2) total2 isofhlevel -> 'a1 isofhlevel -> 'a1 -> 'a2
  isofhlevel

val path_sigma_hprop :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a2 isaprop -> (('a1, 'a2) total2
  paths, 'a1 paths) weq

type coq_PointedType = (coq_UU, __) total2

val pointedType : 'a1 -> coq_PointedType

type underlyingType = __

val basepoint : coq_PointedType -> __

val loopSpace : coq_PointedType -> coq_PointedType

val underlyingLoop : coq_PointedType -> underlyingType -> __ paths

val _UU03a9_ : coq_PointedType -> coq_PointedType

val weq_total2_prod :
  (('a2, ('a1, 'a3) dirprod) total2, ('a1, ('a2, 'a3) total2) dirprod) weq

val totalAssociativity :
  (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq

val paths3 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a3 -> 'a1 paths -> 'a2 paths -> 'a3
  paths -> ('a1, ('a2, 'a3) dirprod) dirprod paths

val confun : 'a2 -> 'a1 -> 'a2

type 'x path_type = 'x

val path_start : 'a1 -> 'a1 -> 'a1 paths -> 'a1

val path_end : 'a1 -> 'a1 -> 'a1 paths -> 'a1

val uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths

val uniqueness' : 'a1 iscontr -> 'a1 -> 'a1 paths

val path_inverse_to_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val path_inverse_to_right' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val pathsinv0_to_right :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathsinv0_to_right' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val pathsinv0_to_right'' :
  'a1 -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val loop_power_nat : 'a1 -> 'a1 paths -> nat -> 'a1 paths

val irrel_paths :
  ('a1 -> 'a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths

val path_inv_rotate_2 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths -> 'a1 paths paths -> 'a1 paths paths

val maponpaths_naturality :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths

val maponpaths_naturality' :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths

val pr2_of_make_hfiber :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a2 paths paths

val pr2_of_pair : 'a1 -> 'a2 -> 'a2 paths

val pr2_of_make_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isweq paths

val pair_path2 :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
  ('a1, 'a2) total2 paths

val pair_path_in2_comp1 : 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths

val total2_paths2_comp1 :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths

val total2_paths2_comp2 :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths

val from_total2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val inv_equality_by_case_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths -> ('a1,
  'a2) coprod paths paths

val equality_by_case_inv_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
  ('a1, 'a2) equality_cases paths

val equality_by_case_equiv :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> (('a1, 'a2) coprod paths, ('a1,
  'a2) equality_cases) weq

val paths_inl_inl_equiv :
  'a1 -> 'a1 -> (('a1, 'a2) coprod paths, 'a1 paths) weq

val paths_inl_inr_equiv : 'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq

val paths_inr_inr_equiv :
  'a2 -> 'a2 -> (('a1, 'a2) coprod paths, 'a2 paths) weq

val paths_inr_inl_equiv : 'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq

val isInjective_inl : ('a1, ('a1, 'a2) coprod) isInjective

val isInjective_inr : ('a2, ('a1, 'a2) coprod) isInjective

val homotsec_natural :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 -> 'a1 -> 'a1 paths
  -> 'a2 paths paths

val evalat : 'a1 -> ('a1 -> 'a2) -> 'a2

val apfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> 'a1 -> 'a1 -> 'a1
  paths -> 'a2 paths

val fromemptysec : empty -> 'a1

val maponpaths_idpath : ('a1 -> 'a2) -> 'a1 -> 'a2 paths paths

val cast : __ paths -> 'a1 -> 'a2

val transport_type_path : __ paths -> 'a1 -> 'a2 paths

val transport_fun_path :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2
  paths -> 'a2 paths paths -> 'a2 paths paths

val transportf_pathsinv0' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths

val transport_idfun : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_functions :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a3) -> 'a1
  -> 'a3 paths

val transport_funapp :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 paths

val helper_A : 'a2 -> 'a2 -> ('a1 -> 'a3) -> 'a2 paths -> 'a1 -> 'a3 paths

val helper_B :
  ('a1 -> 'a2) -> 'a2 -> 'a2 -> ('a1 -> 'a2 paths) -> 'a2 paths -> 'a1 -> 'a2
  paths paths

val transport_invweq :
  ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3, 'a2) weq paths

val transport_invmap :
  ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) paths

val transportf2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val transportb2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val maponpaths_pr1_pr2 :
  ('a1, ('a2, 'a3) total2) total2 -> ('a1, ('a2, 'a3) total2) total2 -> ('a1,
  ('a2, 'a3) total2) total2 paths -> 'a2 paths

val transportb_pair :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 -> ('a2, 'a3) total2 paths

val transportf_total2_const :
  'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> ('a2, 'a3) total2 paths

val isaprop_wma_inhab : ('a1 -> 'a1 isaprop) -> 'a1 isaprop

val isaprop_wma_inhab' : ('a1 -> 'a1 iscontr) -> 'a1 isaprop

val coq_Unnamed_thm :
  hSet -> pr1hSet -> pr1hSet -> pr1hSet paths -> pr1hSet paths -> pr1hSet
  paths paths

val coq_Unnamed_thm0 :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 isaset -> 'a1 paths paths

val funset : hSet -> hSet

val eq_equalities_between_pairs :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> ('a1,
  'a2) total2 paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2)
  total2 paths paths

val total2_reassoc_paths :
  'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
  paths -> 'a3 paths -> ('a2, 'a3) total2 paths

val total2_reassoc_paths' :
  'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
  paths -> 'a3 paths -> ('a2, 'a3) total2 paths

val invrot :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val invrot' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths

val invrot'rot :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths
  paths

val invrotrot' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths
  paths

val hornRotation_rr :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_lr :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_rl :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val hornRotation_ll :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
  paths, 'a1 paths paths) weq

val uniqueFiller :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> ('a1 paths, 'a1 paths paths)
  total2 iscontr

val fillerEquation :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> ('a1 paths, 'a1 paths paths) total2 paths

val isweqpathscomp0r' :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq

val transportPathTotal :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) total2 paths -> 'a3 -> 'a3

val inductionOnFiller :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a1 paths -> 'a1
  paths paths -> 'a2

val transportf_paths_FlFr :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2
  paths paths

val transportf_sec_constant :
  'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a3) -> ('a2 -> 'a3) paths

val path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp paths

val maponpaths_hfpg_path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a1 paths paths

val maponpaths_hfpg'_path_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a2 paths paths

val path_hfp_eta :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp paths paths

val homot_hfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp
  -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 paths -> 'a2 paths ->
  'a2 paths paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp paths paths

val homot_hfp_one_type :
  'a3 isofhlevel -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp ->
  ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp
  paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2, 'a3) hfp paths
  paths

val hfp_is_of_hlevel :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> 'a3 isofhlevel -> ('a1 -> 'a3)
  -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp isofhlevel

val hfp_HLevel :
  nat -> coq_HLevel -> coq_HLevel -> coq_HLevel -> (__ -> __) -> (__ -> __)
  -> coq_HLevel

val transportf_total2_paths_f :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths

val maponpaths_pr1_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths

val maponpaths_pr2_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths

val pathsdirprod_eta :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod paths ->
  ('a1, 'a2) dirprod paths paths

val paths_pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths -> 'a2
  paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2) dirprod paths
  paths

val app_fun : ('a1 -> 'a2, 'a1) dirprod -> 'a2

val app_homot :
  ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3
  paths) -> 'a2 -> ('a1 -> 'a3) paths

val maponpaths_app_fun :
  ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2, 'a1)
  dirprod paths -> 'a2 paths paths

val dirprod_with_prop : 'a1 isaprop -> (('a1, 'a1) dirprod, 'a1) weq

val dirprod_with_prop' :
  'a1 isaprop -> (('a1, ('a2, 'a1) dirprod) dirprod, ('a2, 'a1) dirprod) weq

val issurjective_idfun : ('a1, 'a1) issurjective

val issurjective_to_contr :
  'a1 -> ('a1 -> 'a2) -> 'a2 iscontr -> ('a1, 'a2) issurjective

val issurjective_tounit : 'a1 -> ('a1, coq_unit) issurjective

val issurjective_coprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
  issurjective -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) issurjective

val issurjective_dirprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
  issurjective -> (('a1, 'a2) dirprod, ('a3, 'a4) dirprod) issurjective

val issurjective_totalfun :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> ('a2, 'a3) issurjective) -> (('a1, 'a2)
  total2, ('a1, 'a3) total2) issurjective

val issurjective_sumofmaps_1 :
  ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a2, 'a1) issurjective -> (('a2, 'a3)
  coprod, 'a1) issurjective

val issurjective_sumofmaps_2 :
  ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a3, 'a1) issurjective -> (('a2, 'a3)
  coprod, 'a1) issurjective
open Preamble

type __ = Obj.t

val fromempty : empty -> 'a1

val tounit : 'a1 -> coq_unit

val termfun : 'a1 -> coq_unit -> 'a1

val idfun : 'a1 -> 'a1

val funcomp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val curry : (('a1, 'a2) total2 -> 'a3) -> 'a1 -> 'a2 -> 'a3

val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

type 'x binop = 'x -> 'x -> 'x

val iteration : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1

val adjev : 'a1 -> ('a1 -> 'a2) -> 'a2

val adjev2 : ((('a1 -> 'a2) -> 'a2) -> 'a2) -> 'a1 -> 'a2

type ('x, 'y) dirprod = ('x, 'y) total2

val dirprod_pr1 : ('a1, 'a2) dirprod -> 'a1

val dirprod_pr2 : ('a1, 'a2) dirprod -> 'a2

val make_dirprod : 'a1 -> 'a2 -> ('a1, 'a2) dirprod

val dirprodadj : (('a1, 'a2) dirprod -> 'a3) -> 'a1 -> 'a2 -> 'a3

val dirprodf :
  ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) dirprod -> ('a2, 'a4) dirprod

val ddualand :
  (('a1 -> 'a3) -> 'a3) -> (('a2 -> 'a3) -> 'a3) -> (('a1, 'a2) dirprod ->
  'a3) -> 'a3

type 'x neg = 'x -> empty

val negf : ('a1 -> 'a2) -> 'a2 neg -> 'a1 neg

type 'x dneg = 'x neg neg

val dnegf : ('a1 -> 'a2) -> 'a1 dneg -> 'a2 dneg

val todneg : 'a1 -> 'a1 dneg

val dnegnegtoneg : 'a1 neg dneg -> 'a1 neg

val dneganddnegl1 : 'a1 dneg -> 'a2 dneg -> ('a1 -> 'a2 neg) neg

val dneganddnegimpldneg : 'a1 dneg -> 'a2 dneg -> ('a1, 'a2) dirprod dneg

type ('x, 'y) logeq = ('x -> 'y, 'y -> 'x) dirprod

val isrefl_logeq : ('a1, 'a1) logeq

val issymm_logeq : ('a1, 'a2) logeq -> ('a2, 'a1) logeq

val logeqnegs : ('a1, 'a2) logeq -> ('a1 neg, 'a2 neg) logeq

val logeq_both_true : 'a1 -> 'a2 -> ('a1, 'a2) logeq

val logeq_both_false : 'a1 neg -> 'a2 neg -> ('a1, 'a2) logeq

val logeq_trans : ('a1, 'a2) logeq -> ('a2, 'a3) logeq -> ('a1, 'a3) logeq

val funcomp_assoc :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1 -> 'a4) paths

val uncurry_curry :
  (('a1, 'a3) total2 -> 'a2) -> ('a1, 'a3) total2 -> 'a2 paths

val curry_uncurry : ('a1 -> 'a3 -> 'a2) -> 'a1 -> 'a3 -> 'a2 paths

val pathscomp0 : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths

val pathscomp0rid : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths

val path_assoc :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths

val pathsinv0l : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0r : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0inv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathscomp_cancel_left :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathscomp_cancel_right :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathscomp_inv :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) dirprod
  paths

val dirprodeq :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) dirprod paths

val maponpaths : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val map_on_two_paths :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val maponpathscomp0 :
  'a1 -> 'a1 -> 'a1 -> ('a1 -> 'a2) -> 'a1 paths -> 'a1 paths -> 'a2 paths
  paths

val maponpathsinv0 :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths

val maponpathsidfun : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val maponpathscomp :
  'a1 -> 'a1 -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 paths -> 'a3 paths paths

type ('x, 'p) homot = 'x -> 'p paths

val homotrefl : ('a1 -> 'a2) -> ('a1, 'a2) homot

val homotcomp :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1,
  'a2) homot -> ('a1, 'a2) homot

val invhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) homot

val funhomot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val funhomotsec :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val homotfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a3) -> ('a1,
  'a3) homot

val toforallpaths :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot

val eqtohomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot

val maponpathshomidinv :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths

val maponpathshomid1 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths
  paths

val maponpathshomid2 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths
  paths

val pathssec1 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a2 -> 'a2
  paths -> 'a1 paths

val pathssec2 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a2
  paths -> 'a1 paths

val pathssec2id :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 paths paths

val pathssec3 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1
  paths -> 'a1 paths paths

val constr1 :
  'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2, ('a2 -> ('a1, 'a2) total2 paths,
  'a2 -> 'a1 paths paths) total2) total2

val transportf : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2

val transportf_eq : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) total2 paths

val transportb : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2

val idpath_transportf : 'a1 -> 'a2 -> 'a2 paths

val functtransportf :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths

val functtransportb :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths

val transport_f_b :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_b_f :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_f_f :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_b_b :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_map :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths

val transport_section : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val transportf_fun :
  'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) -> ('a3 -> 'a2) paths

val transportb_fun' :
  'a1 -> 'a1 -> ('a2 -> 'a3) -> 'a1 paths -> 'a2 -> 'a3 paths

val transportf_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths

val transportb_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths

val transportf_paths :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 paths

val transportbfinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val transportfbinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val base_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a1
  paths

val two_arg_paths :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val two_arg_paths_f :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val two_arg_paths_b :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val dirprod_paths :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) dirprod paths

val total2_paths_f :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) total2 paths

val total2_paths_b :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) total2 paths

val total2_paths2 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val total2_paths2_f :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val total2_paths2_b :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val pair_path_in2 : 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) total2 paths

val fiber_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a2
  paths

val total2_fiber_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> ('a1,
  'a2) total2 paths paths

val base_total2_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a1
  paths paths

val transportf_fiber_total2_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a2
  paths paths

val total2_base_map : ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val total2_section_path :
  'a1 -> 'a2 -> ('a1 -> 'a2) -> ('a1, 'a2) total2 paths -> 'a2 paths

val transportD : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val transportf_total2 :
  'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 paths

val transportf_dirprod :
  ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 -> 'a1
  paths -> ('a2, 'a3) dirprod paths

val transportb_dirprod :
  ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 -> 'a1
  paths -> ('a2, 'a3) dirprod paths

val transportf_id1 :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val transportf_id2 :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val transportf_id3 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val famhomotfun :
  ('a1, coq_UU) homot -> ('a1, 'a2) total2 -> ('a1, 'a3) total2

val famhomothomothomot :
  ('a1, coq_UU) homot -> ('a1, coq_UU) homot -> ('a1, coq_UU paths) homot ->
  (('a1, 'a2) total2, ('a1, 'a3) total2) homot

type 't iscontr = ('t, 't -> 't paths) total2

val make_iscontr : 'a1 -> ('a1 -> 'a1 paths) -> 'a1 iscontr

val iscontrpr1 : 'a1 iscontr -> 'a1

val iscontr_uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths

val iscontrretract :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 iscontr -> 'a2
  iscontr

val proofirrelevancecontr : 'a1 iscontr -> 'a1 -> 'a1 -> 'a1 paths

val path_to_ctr : ('a1, 'a2) total2 iscontr -> 'a1 -> 'a2 -> 'a1 paths

type ('x, 'y) hfiber = ('x, 'y paths) total2

val make_hfiber : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val hfiberpr1 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a1

val hfiberpr2 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a2 paths

val hfibershomotftog :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibershomotgtof :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibertriangle1 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle1' :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths -> 'a2
  paths paths

val hfibertriangle1inv0 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle1inv0' :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2 paths) total2 paths
  -> 'a2 paths paths

val hfibertriangle2 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> 'a1 paths
  -> 'a2 paths paths -> ('a1, 'a2) hfiber paths

type 't coconusfromt = ('t, 't paths) total2

val coconusfromtpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconusfromt

val coconusfromtpr1 : 'a1 -> 'a1 coconusfromt -> 'a1

type 't coconustot = ('t, 't paths) total2

val coconustotpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconustot

val coconustotpr1 : 'a1 -> 'a1 coconustot -> 'a1

val coconustot_isProofIrrelevant :
  'a1 -> 'a1 coconustot -> 'a1 coconustot -> 'a1 coconustot paths

val iscontrcoconustot : 'a1 -> 'a1 coconustot iscontr

val coconusfromt_isProofIrrelevant :
  'a1 -> 'a1 coconusfromt -> 'a1 coconusfromt -> 'a1 coconusfromt paths

val iscontrcoconusfromt : 'a1 -> 'a1 coconusfromt iscontr

type 't pathsspace = ('t, 't coconusfromt) total2

val pathsspacetriple : 'a1 -> 'a1 -> 'a1 paths -> 'a1 pathsspace

val deltap : 'a1 -> 'a1 pathsspace

type 't pathsspace' = (('t, 't) dirprod, 't paths) total2

type ('x, 'y) coconusf = ('y, ('x, 'y) hfiber) total2

val fromcoconusf : ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> 'a1

val tococonusf : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) coconusf

val homottofromcoconusf :
  ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> ('a1, 'a2) coconusf paths

val homotfromtococonusf : ('a1 -> 'a2) -> 'a1 -> 'a1 paths

type ('x, 'y) isweq = 'y -> ('x, 'y) hfiber iscontr

val idisweq : ('a1, 'a1) isweq

type ('x, 'y) weq = ('x -> 'y, ('x, 'y) isweq) total2

val pr1weq : ('a1, 'a2) weq -> 'a1 -> 'a2

val weqproperty : ('a1, 'a2) weq -> ('a1, 'a2) isweq

val weqccontrhfiber : ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber

val weqccontrhfiber2 :
  ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths

val make_weq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) weq

val idweq : ('a1, 'a1) weq

val isweqtoempty : ('a1 -> empty) -> ('a1, empty) isweq

val weqtoempty : ('a1 -> empty) -> ('a1, empty) weq

val isweqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) isweq

val weqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) weq

val weqempty : 'a1 neg -> 'a2 neg -> ('a1, 'a2) weq

val invmap : ('a1, 'a2) weq -> 'a2 -> 'a1

val homotweqinvweq : ('a1, 'a2) weq -> 'a2 -> 'a2 paths

val homotinvweqweq0 : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val homotinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val invmaponpathsweq : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths

val invmaponpathsweqid : ('a1, 'a2) weq -> 'a1 -> 'a1 paths paths

val pathsweq1 : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths

val pathsweq1' : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths

val pathsweq3 : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsweq4 : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths paths

val homotweqinv :
  ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) homot -> ('a2,
  'a3) homot

val homotweqinv' :
  ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val internal_paths_rew : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

val internal_paths_rew_r : 'a1 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2

val isinjinvmap :
  ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a1) homot -> ('a1, 'a2) homot

val isinjinvmap' :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2, 'a2)
  homot -> ('a1, 'a1) homot -> ('a2, 'a1) homot -> ('a1, 'a2) homot

val diaglemma2 :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths ->
  'a2 paths paths

val homotweqinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a2 paths paths

val weq_transportf_adjointness : ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths

val weq_transportb_adjointness : ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths

val isweqtransportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val isweqtransportb : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val iscontrweqb : ('a1, 'a2) weq -> 'a2 iscontr -> 'a1 iscontr

val isProofIrrelevantUnit : coq_unit -> coq_unit -> coq_unit paths

val unitl0 : coq_unit paths -> coq_unit coconustot

val unitl1 : coq_unit coconustot -> coq_unit paths

val unitl2 : coq_unit paths -> coq_unit paths paths

val unitl3 : coq_unit paths -> coq_unit paths paths

val iscontrunit : coq_unit iscontr

val iscontrpathsinunit : coq_unit -> coq_unit -> coq_unit paths iscontr

val ifcontrthenunitl0 :
  coq_unit paths -> coq_unit paths -> coq_unit paths paths

val isweqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) isweq

val weqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) weq

val iscontrifweqtounit : ('a1, coq_unit) weq -> 'a1 iscontr

val hfibersgftog :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a3) hfiber -> ('a2, 'a3)
  hfiber

val constr2 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a2, 'a1)
  hfiber -> (('a1, 'a1) hfiber, ('a2, 'a1) hfiber paths) total2

val iscontrhfiberl1 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a1, 'a1)
  hfiber iscontr -> ('a2, 'a1) hfiber iscontr

val homothfiber1 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val homothfiber2 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val homothfiberretr :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber paths

val iscontrhfiberl2 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber iscontr -> ('a1, 'a2) hfiber iscontr

val isweqhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isweq ->
  ('a1, 'a2) isweq

val remakeweq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) weq

val remakeweq_eq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1 -> 'a2) paths

val remakeweq_eq' :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a1) paths

val iscontr_move_point : 'a1 -> 'a1 iscontr -> 'a1 iscontr

val iscontr_move_point_eq : 'a1 -> 'a1 iscontr -> 'a1 paths

val remakeweqinv :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1, 'a2) weq

val remakeweqinv_eq :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1 -> 'a2) paths

val remakeweqinv_eq' :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a2 -> 'a1) paths

val remakeweqboth :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a1, 'a2) weq

val remakeweqboth_eq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a1 -> 'a2) paths

val remakeweqboth_eq' :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a2 -> 'a1) paths

val isweqhomot_iff :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> (('a1, 'a2) isweq,
  ('a1, 'a2) isweq) logeq

val isweq_to_isweq_unit :
  ('a1 -> coq_unit) -> ('a1 -> coq_unit) -> ('a1, coq_unit) isweq -> ('a1,
  coq_unit) isweq

val isweq_iso :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths) ->
  ('a1, 'a2) isweq

val weq_iso :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths) ->
  ('a1, 'a2) weq

type ('x, 'y) coq_UniqueConstruction =
  ('y -> ('x, 'y paths) total2, 'x -> 'x -> 'y paths -> 'x paths) dirprod

val coq_UniqueConstruction_to_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> ('a1, 'a2) isweq

val isweqinvmap : ('a1, 'a2) weq -> ('a2, 'a1) isweq

val invweq : ('a1, 'a2) weq -> ('a2, 'a1) weq

val invinv : ('a1, 'a2) weq -> 'a1 -> 'a2 paths

val pr1_invweq : ('a1, 'a2) weq -> ('a2 -> 'a1) paths

val iscontrweqf : ('a1, 'a2) weq -> 'a1 iscontr -> 'a2 iscontr

type ('a, 'b) coq_PathPair = ('a paths, 'b paths) total2

val total2_paths_equiv :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
  'a2) coq_PathPair) weq

val wequnittocontr : 'a1 iscontr -> (coq_unit, 'a1) weq

val isweqmaponpaths :
  ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) isweq

val weqonpaths : ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) weq

val isweqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) isweq

val weqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) weq

val isweqpathscomp0r :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq

val isweqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) isweq

val weqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) weq

val isweqfromcoconusf : ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) isweq

val weqfromcoconusf : ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) weq

val isweqdeltap : ('a1, 'a1 pathsspace) isweq

val isweqpr1pr1 : ('a1 pathsspace', 'a1) isweq

val weqhfibershomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a2) hfiber) weq

val twooutof3a :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a2) isweq

val twooutof3b :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isweq ->
  ('a2, 'a3) isweq

val isweql3 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1, 'a2) isweq ->
  ('a2, 'a1) isweq

val twooutof3c :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a3) isweq

val twooutof3c_iff_2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> (('a2, 'a3) isweq,
  ('a1, 'a3) isweq) logeq

val twooutof3c_iff_1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isweq -> (('a1, 'a2) isweq,
  ('a1, 'a3) isweq) logeq

val twooutof3c_iff_1_homot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a2,
  'a3) isweq -> (('a1, 'a2) isweq, ('a1, 'a3) isweq) logeq

val twooutof3c_iff_2_homot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a1,
  'a2) isweq -> (('a2, 'a3) isweq, ('a1, 'a3) isweq) logeq

val isweqcontrcontr :
  ('a1 -> 'a2) -> 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) isweq

val weqcontrcontr : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq

val weqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq

val weqcomp_to_funcomp_app :
  'a1 -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a3 paths

val weqcomp_to_funcomp :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1 -> 'a3) paths

val invmap_weqcomp_expand :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths

val twooutofsixu :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a1, 'a2) isweq

val twooutofsixv :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a2, 'a3) isweq

val twooutofsixw :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a3, 'a4) isweq

val isweqdirprodf :
  ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
  dirprod) isweq

val weqdirprodf :
  ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
  dirprod) weq

val weqtodirprodwithunit : ('a1, ('a1, coq_unit) dirprod) weq

val total2asstor :
  (('a1, 'a2) total2, 'a3) total2 -> ('a1, ('a2, 'a3) total2) total2

val total2asstol :
  ('a1, ('a2, 'a3) total2) total2 -> (('a1, 'a2) total2, 'a3) total2

val weqtotal2asstor :
  ((('a1, 'a2) total2, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq

val weqtotal2asstol :
  (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq

val weqdirprodasstor :
  ((('a1, 'a2) dirprod, 'a3) dirprod, ('a1, ('a2, 'a3) dirprod) dirprod) weq

val weqdirprodasstol :
  (('a1, ('a2, 'a3) dirprod) dirprod, (('a1, 'a2) dirprod, 'a3) dirprod) weq

val weqdirprodcomm : (('a1, 'a2) dirprod, ('a2, 'a1) dirprod) weq

val weqtotal2dirprodcomm :
  ((('a1, 'a2) dirprod, 'a3) total2, (('a2, 'a1) dirprod, 'a3) total2) weq

val weqtotal2dirprodassoc :
  ((('a1, 'a2) dirprod, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq

val weqtotal2dirprodassoc' :
  ((('a1, 'a2) dirprod, 'a3) total2, ('a2, ('a1, 'a3) total2) total2) weq

val weqtotal2comm12 :
  ((('a1, 'a2) total2, 'a3) total2, (('a1, 'a3) total2, 'a2) total2) weq

val rdistrtocoprod :
  ('a1, ('a2, 'a3) coprod) dirprod -> (('a1, 'a2) dirprod, ('a1, 'a3)
  dirprod) coprod

val rdistrtoprod :
  (('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod -> ('a1, ('a2, 'a3) coprod)
  dirprod

val isweqrdistrtoprod :
  ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3) coprod)
  dirprod) isweq

val weqrdistrtoprod :
  ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3) coprod)
  dirprod) weq

val isweqrdistrtocoprod :
  (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3) dirprod)
  coprod) isweq

val weqrdistrtocoprod :
  (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3) dirprod)
  coprod) weq

val fromtotal2overcoprod :
  (('a1, 'a2) coprod, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3) total2)
  coprod

val tototal2overcoprod :
  (('a1, 'a3) total2, ('a2, 'a3) total2) coprod -> (('a1, 'a2) coprod, 'a3)
  total2

val weqtotal2overcoprod :
  ((('a1, 'a2) coprod, 'a3) total2, (('a1, 'a3) total2, ('a2, 'a3) total2)
  coprod) weq

val sumofmaps : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

val coprodasstor :
  (('a1, 'a2) coprod, 'a3) coprod -> ('a1, ('a2, 'a3) coprod) coprod

val coprodasstol :
  ('a1, ('a2, 'a3) coprod) coprod -> (('a1, 'a2) coprod, 'a3) coprod

val sumofmaps_assoc_left :
  ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> (('a1, ('a2, 'a3) coprod)
  coprod, 'a4) homot

val sumofmaps_assoc_right :
  ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> ((('a1, 'a2) coprod, 'a3)
  coprod, 'a4) homot

val isweqcoprodasstor :
  ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) isweq

val weqcoprodasstor :
  ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) weq

val isweqcoprodasstol :
  (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) isweq

val weqcoprodasstol :
  (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) weq

val coprodcomm : ('a1, 'a2) coprod -> ('a2, 'a1) coprod

val isweqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) isweq

val weqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) weq

val isweqii1withneg : ('a2 -> empty) -> ('a1, ('a1, 'a2) coprod) isweq

val weqii1withneg : 'a2 neg -> ('a1, ('a1, 'a2) coprod) weq

val isweqii2withneg : ('a1 -> empty) -> ('a2, ('a1, 'a2) coprod) isweq

val weqii2withneg : 'a1 neg -> ('a2, ('a1, 'a2) coprod) weq

val coprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) coprod -> ('a3, 'a4) coprod

val coprodf1 : ('a1 -> 'a3) -> ('a1, 'a2) coprod -> ('a3, 'a2) coprod

val coprodf2 : ('a2 -> 'a3) -> ('a1, 'a2) coprod -> ('a1, 'a3) coprod

val homotcoprodfcomp :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3 -> 'a5) -> ('a4 -> 'a6) -> (('a1, 'a2)
  coprod, ('a5, 'a6) coprod) homot

val homotcoprodfhomot :
  ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a2 -> 'a4) -> ('a1, 'a3)
  homot -> ('a2, 'a4) homot -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) homot

val isweqcoprodf :
  ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4) coprod)
  isweq

val weqcoprodf :
  ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4) coprod)
  weq

val weqcoprodf1 : ('a1, 'a3) weq -> (('a1, 'a2) coprod, ('a3, 'a2) coprod) weq

val weqcoprodf2 : ('a2, 'a3) weq -> (('a1, 'a2) coprod, ('a1, 'a3) coprod) weq

type ('p, 'q) equality_cases = __

val equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths -> ('a1,
  'a2) equality_cases

val inv_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
  ('a1, 'a2) coprod paths

val ii1_injectivity : 'a1 -> 'a1 -> ('a1, 'a2) coprod paths -> 'a1 paths

val ii2_injectivity : 'a2 -> 'a2 -> ('a1, 'a2) coprod paths -> 'a2 paths

val negpathsii1ii2 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val negpathsii2ii1 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val boolascoprod : ((coq_unit, coq_unit) coprod, bool) weq

val coprodtobool : ('a1, 'a2) coprod -> bool

type ('x, 'y) boolsumfun = __

val coprodtoboolsum :
  ('a1, 'a2) coprod -> (bool, ('a1, 'a2) boolsumfun) total2

val boolsumtocoprod :
  (bool, ('a1, 'a2) boolsumfun) total2 -> ('a1, 'a2) coprod

val isweqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) isweq

val weqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) weq

val isweqboolsumtocoprod :
  ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) isweq

val weqboolsumtocoprod :
  ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) weq

val weqcoprodsplit :
  ('a1 -> ('a2, 'a3) coprod) -> ('a1, (('a2, ('a1, ('a2, 'a3) coprod) hfiber)
  total2, ('a3, ('a1, ('a2, 'a3) coprod) hfiber) total2) coprod) weq

val boolchoice : bool -> (bool paths, bool paths) coprod

type bool_to_type = __

val nopathstruetofalse : bool paths -> empty

val nopathsfalsetotrue : bool paths -> empty

val truetonegfalse : bool -> bool paths -> bool paths neg

val falsetonegtrue : bool -> bool paths -> bool paths neg

val negtruetofalse : bool -> bool paths neg -> bool paths

val negfalsetotrue : bool -> bool paths neg -> bool paths

val onefiber :
  'a1 -> ('a1 -> ('a1 paths, 'a2 neg) coprod) -> ('a2, ('a1, 'a2) total2)
  isweq

type ('x, 'y, 'z) complxstr = 'x -> 'z paths

val ezmap :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a1 ->
  ('a2, 'a3) hfiber

type ('x, 'y, 'z) isfibseq = ('x, ('y, 'z) hfiber) isweq

type ('x, 'y, 'z) fibseqstr =
  (('x, 'y, 'z) complxstr, ('x, 'y, 'z) isfibseq) total2

val make_fibseqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> ('a1,
  'a2, 'a3) isfibseq -> (('a1, 'a2, 'a3) complxstr, ('a1, 'a2, 'a3) isfibseq)
  total2

val fibseqstrtocomplxstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
  'a2, 'a3) complxstr

val ezweq :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
  ('a2, 'a3) hfiber) weq

val d1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a3 paths -> 'a1

val ezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a3 paths -> ('a1, 'a2) hfiber

val invezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a2 ->
  ('a1, 'a2) hfiber -> 'a3 paths

val isweqezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, ('a1, 'a2) hfiber) isweq

val ezweq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, ('a1, 'a2) hfiber) weq

val fibseq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, 'a1, 'a2) fibseqstr

val d2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> 'a2 paths -> 'a3 paths

val ezweq2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> ('a2 paths, ('a3 paths, 'a1) hfiber) weq

val fibseq2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> ('a2 paths, 'a3 paths, 'a1) fibseqstr

val ezmappr1 : 'a1 -> 'a2 -> (('a1, 'a2) total2, 'a1) hfiber

val invezmappr1 : 'a1 -> (('a1, 'a2) total2, 'a1) hfiber -> 'a2

val isweqezmappr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) isweq

val ezweqpr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) weq

val isfibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) isfibseq

val fibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) fibseqstr

val ezweq1pr1 :
  'a1 -> ('a1, 'a2) total2 -> ('a1 paths, ('a2, ('a1, 'a2) total2) hfiber) weq

val isfibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) isfibseq

val ezweqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, ('a1, 'a2) hfiber) weq

val fibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) fibseqstr

val d1g : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val ezweq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, (('a1, 'a2) hfiber, 'a1) hfiber)
  weq

val fibseq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, ('a1, 'a2) hfiber, 'a1) fibseqstr

val d2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a1 paths -> 'a2 paths

val ezweq2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, ('a2 paths,
  ('a1, 'a2) hfiber) hfiber) weq

val fibseq2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, 'a2 paths,
  ('a1, 'a2) hfiber) fibseqstr

val d3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1, 'a2)
  hfiber paths -> 'a1 paths

val homotd3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1, 'a2)
  hfiber paths -> 'a1 paths paths

val ezweq3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1, 'a2)
  hfiber paths, ('a1 paths, 'a2 paths) hfiber) weq

val fibseq3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1, 'a2)
  hfiber paths, 'a1 paths, 'a2 paths) fibseqstr

val hfibersftogf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
  hfiber -> ('a1, 'a3) hfiber

val ezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
  hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber

val invezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> ('a1, 'a2) hfiber

val ffgg :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber)
  hfiber

val homotffggid :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber)
  hfiber paths

val isweqezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) isweq

val ezweqhf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) weq

val fibseqhf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, ('a1, 'a3) hfiber, ('a2, 'a3) hfiber) fibseqstr

val isweqinvezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ((('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber, ('a1, 'a2) hfiber) isweq

val weqhfibersgwtog :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) weq

val totalfun : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> ('a1, 'a3) total2

val isweqtotaltofib :
  ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq -> 'a1
  -> ('a2, 'a3) isweq

val weqtotaltofib :
  ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq -> 'a1
  -> ('a2, 'a3) weq

val isweqfibtototal :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq

val isweqfibtototal' :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq

val weqfibtototal :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq

val fpmap : ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val hffpmap2 :
  ('a1 -> 'a2) -> ('a1, 'a3) total2 -> (('a2, 'a3) total2, ('a1, 'a2) hfiber)
  total2

val centralfiber : 'a1 -> ('a2, ('a1 coconusfromt, 'a2) total2) isweq

val isweqhff :
  ('a1 -> 'a2) -> (('a1, 'a3) total2, (('a2, 'a3) total2, ('a1, 'a2) hfiber)
  total2) isweq

val hfiberfpmap :
  ('a1 -> 'a2) -> ('a2, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3) total2)
  hfiber -> ('a1, 'a2) hfiber

val isweqhfiberfp :
  ('a1 -> 'a2) -> ('a2, 'a3) total2 -> ((('a1, 'a3) total2, ('a2, 'a3)
  total2) hfiber, ('a1, 'a2) hfiber) isweq

val isweqfpmap :
  ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) isweq

val weqfp_map : ('a1, 'a2) weq -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val weqfp_invmap : ('a1, 'a2) weq -> ('a2, 'a3) total2 -> ('a1, 'a3) total2

val weqfp : ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) weq

val weqfp_compute_1 :
  ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) homot

val weqfp_compute_2 :
  ('a1, 'a2) weq -> (('a2, 'a3) total2, ('a1, 'a3) total2) homot

val weqtotal2overcoprod' :
  (('a2, 'a3) coprod, 'a1) weq -> (('a1, 'a4) total2, (('a2, 'a4) total2,
  ('a3, 'a4) total2) coprod) weq

val fromtotal2overunit : (coq_unit, 'a1) total2 -> 'a1

val tototal2overunit : 'a1 -> (coq_unit, 'a1) total2

val weqtotal2overunit : ((coq_unit, 'a1) total2, 'a1) weq

val bandfmap :
  ('a1 -> 'a2) -> ('a1 -> 'a3 -> 'a4) -> ('a1, 'a3) total2 -> ('a2, 'a4)
  total2

val isweqbandfmap :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) isweq

val weqbandf :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) weq

type ('x, 'x0, 'y, 'z) commsqstr = 'z -> 'y paths

val hfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a1 -> ('a4, 'a1) hfiber -> ('a2, 'a3) hfiber

val hfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a2 -> ('a4, 'a2) hfiber -> ('a1, 'a3) hfiber

val transposcommsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a2, 'a1, 'a3, 'a4) commsqstr

val complxstrtocommsqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr ->
  (coq_unit, 'a2, 'a3, 'a1) commsqstr

val commsqstrtocomplxstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1) commsqstr
  -> ('a1, 'a2, 'a3) complxstr

type ('x, 'x0, 'y) hfp = (('x, 'x0) dirprod, 'y paths) total2

val hfpg : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a1

val hfpg' : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a2

val commsqZtohfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> ('a1, 'a2, 'a3) hfp

val commsqZtohfphomot :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> 'a1 paths

val commsqZtohfphomot' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> 'a2 paths

type ('x, 'x0, 'y) hfpoverX = ('x, ('x0, 'y) hfiber) total2

type ('x, 'x0, 'y) hfpoverX' = ('x0, ('x, 'y) hfiber) total2

val weqhfptohfpoverX :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
  hfpoverX) weq

val weqhfptohfpoverX' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
  hfpoverX') weq

val weqhfpcomm :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, 'a1, 'a3) hfp)
  weq

val commhfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) hfp)
  commsqstr

val hfibertohfp :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> (coq_unit, 'a1, 'a2) hfp

val hfptohfiber :
  ('a1 -> 'a2) -> 'a2 -> (coq_unit, 'a1, 'a2) hfp -> ('a1, 'a2) hfiber

val weqhfibertohfp :
  ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, (coq_unit, 'a1, 'a2) hfp) weq

val hfp_left :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, ('a2, 'a3)
  hfiber) total2) weq

val hfp_right :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, ('a1, 'a3)
  hfiber) total2) weq

val hfiber_comm :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, ('a2, 'a3) hfiber) total2, ('a2,
  ('a1, 'a3) hfiber) total2) weq

type ('x, 'x0, 'y, 'z) ishfsq = ('z, ('x, 'x0, 'y) hfp) isweq

type ('x, 'x0, 'y, 'z) hfsqstr =
  (('x, 'x0, 'y, 'z) commsqstr, ('z, ('x, 'x0, 'y) hfp) isweq) total2

val make_hfsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) isweq -> (('a1, 'a2, 'a3,
  'a4) commsqstr, ('a4, ('a1, 'a2, 'a3) hfp) isweq) total2

val hfsqstrtocommsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a1, 'a2, 'a3, 'a4) commsqstr

val weqZtohfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) weq

val isweqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber) isweq

val weqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber) weq

val ishfsqweqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber)
  isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr

val isweqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber) isweq

val weqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber) weq

val ishfsqweqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber)
  isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr

val transposhfpsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a2, 'a1, 'a3, 'a4) hfsqstr

val fibseqstrtohfsqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  (coq_unit, 'a2, 'a3, 'a1) hfsqstr

val hfsqstrtofibseqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1) hfsqstr ->
  ('a1, 'a2, 'a3) fibseqstr
open PartA
open Preamble

type __ = Obj.t

type 'x isofhlevel = __

val hlevelretract :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 isofhlevel
  -> 'a2 isofhlevel

val isofhlevelweqf : nat -> ('a1, 'a2) weq -> 'a1 isofhlevel -> 'a2 isofhlevel

val isofhlevelweqb : nat -> ('a1, 'a2) weq -> 'a2 isofhlevel -> 'a1 isofhlevel

val isofhlevelsn : nat -> ('a1 -> 'a1 isofhlevel) -> 'a1 isofhlevel

val isofhlevelssn : nat -> ('a1 -> 'a1 paths isofhlevel) -> 'a1 isofhlevel

type ('x, 'y) isofhlevelf = 'y -> ('x, 'y) hfiber isofhlevel

val isofhlevelfhomot :
  nat -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelfpmap :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> (('a1, 'a3) total2, ('a2,
  'a3) total2) isofhlevelf

val isofhlevelfffromZ :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  'a3 isofhlevel -> ('a1, 'a2) isofhlevelf

val isofhlevelXfromg :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  ('a2, 'a3) isofhlevelf -> 'a1 isofhlevel

val isofhlevelffromXY :
  nat -> ('a1 -> 'a2) -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2)
  isofhlevelf

val isofhlevelXfromfY :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> 'a2 isofhlevel -> 'a1
  isofhlevel

val isofhlevelffib :
  nat -> 'a1 -> ('a1 -> 'a1 paths isofhlevel) -> ('a2, ('a1, 'a2) total2)
  isofhlevelf

val isofhlevelfhfiberpr1y :
  nat -> ('a1 -> 'a2) -> 'a2 -> ('a2 -> 'a2 paths isofhlevel) -> (('a1, 'a2)
  hfiber, 'a1) isofhlevelf

val isofhlevelfsnfib :
  nat -> 'a1 -> 'a1 paths isofhlevel -> ('a2, ('a1, 'a2) total2) isofhlevelf

val isofhlevelfsnhfiberpr1 :
  nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 paths isofhlevel -> (('a1, 'a2) hfiber,
  'a1) isofhlevelf

val isofhlevelfhfiberpr1 :
  nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 isofhlevel -> (('a1, 'a2) hfiber, 'a1)
  isofhlevelf

val isofhlevelff :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a2) isofhlevelf

val isofhlevelfgf :
  nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1, 'a3) isofhlevelf

val isofhlevelfgwtog :
  nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
  'a3) isofhlevelf

val isofhlevelfgtogw :
  nat -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isofhlevelf -> ('a1,
  'a3) isofhlevelf

val isofhlevelfhomot2 :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) weq -> ('a1 -> 'a3 paths)
  -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3) isofhlevelf

val isofhlevelfonpaths :
  nat -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> ('a1, 'a2) isofhlevelf -> ('a1 paths,
  'a2 paths) isofhlevelf

val isofhlevelfsn :
  nat -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> ('a1 paths, 'a2 paths) isofhlevelf)
  -> ('a1, 'a2) isofhlevelf

val isofhlevelfssn :
  nat -> ('a1 -> 'a2) -> ('a1 -> ('a1 paths, 'a2 paths) isofhlevelf) -> ('a1,
  'a2) isofhlevelf

val isofhlevelfpr1 :
  nat -> ('a1 -> 'a2 isofhlevel) -> (('a1, 'a2) total2, 'a1) isofhlevelf

val isweqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) isweq

val weqpr1 : ('a1 -> 'a2 iscontr) -> (('a1, 'a2) total2, 'a1) weq

val isofhleveltotal2 :
  nat -> 'a1 isofhlevel -> ('a1 -> 'a2 isofhlevel) -> ('a1, 'a2) total2
  isofhlevel

val isofhleveldirprod :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) dirprod isofhlevel

type 'x isaprop = 'x isofhlevel

type ('x, 'y) isPredicate = 'x -> 'y isaprop

val isapropunit : coq_unit isaprop

val isapropdirprod : 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) dirprod isaprop

val isapropifcontr : 'a1 iscontr -> 'a1 isaprop

val hlevelntosn : nat -> 'a1 isofhlevel -> 'a1 isofhlevel

val isofhlevelcontr : nat -> 'a1 iscontr -> 'a1 isofhlevel

val isofhlevelfweq : nat -> ('a1, 'a2) weq -> ('a1, 'a2) isofhlevelf

val isweqfinfibseq :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a3
  iscontr -> ('a1, 'a2) isweq

val weqhfibertocontr :
  ('a1 -> 'a2) -> 'a2 -> 'a2 iscontr -> (('a1, 'a2) hfiber, 'a1) weq

val weqhfibertounit : (('a1, coq_unit) hfiber, 'a1) weq

val isofhleveltofun : nat -> 'a1 isofhlevel -> ('a1, coq_unit) isofhlevelf

val isofhlevelfromfun : nat -> ('a1, coq_unit) isofhlevelf -> 'a1 isofhlevel

val weqhfiberunit :
  ('a1 -> 'a2) -> 'a2 -> (('a1, (coq_unit, 'a2) hfiber) total2, ('a1, 'a2)
  hfiber) weq

val isofhlevelsnprop : nat -> 'a1 isaprop -> 'a1 isofhlevel

val iscontraprop1 : 'a1 isaprop -> 'a1 -> 'a1 iscontr

val iscontraprop1inv : ('a1 -> 'a1 iscontr) -> 'a1 isaprop

type 'x isProofIrrelevant = 'x -> 'x -> 'x paths

val proofirrelevance : 'a1 isaprop -> 'a1 isProofIrrelevant

val invproofirrelevance : 'a1 isProofIrrelevant -> 'a1 isaprop

val isProofIrrelevant_paths :
  'a1 isProofIrrelevant -> 'a1 -> 'a1 -> 'a1 paths isProofIrrelevant

val isapropcoprod :
  'a1 isaprop -> 'a2 isaprop -> ('a1 -> 'a2 -> empty) -> ('a1, 'a2) coprod
  isaprop

val isweqimplimpl :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2)
  isweq

val weqimplimpl :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) weq

val weqiff : ('a1, 'a2) logeq -> 'a1 isaprop -> 'a2 isaprop -> ('a1, 'a2) weq

val weq_to_iff : ('a1, 'a2) weq -> ('a1, 'a2) logeq

val isapropempty : empty isaprop

val isapropifnegtrue : ('a1 -> empty) -> 'a1 isaprop

val isapropretract :
  'a2 isaprop -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a1) homot -> 'a1
  isaprop

val isapropcomponent1 : ('a1, 'a2) coprod isaprop -> 'a1 isaprop

val isapropcomponent2 : ('a1, 'a2) coprod isaprop -> 'a2 isaprop

type ('x, 'y) isincl = ('x, 'y) isofhlevelf

type ('x, 'y) incl = ('x -> 'y, ('x, 'y) isincl) total2

val make_incl : ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) incl

val pr1incl : ('a1, 'a2) incl -> 'a1 -> 'a2

val isinclweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isincl

val isofhlevelfsnincl :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isofhlevelf

val weqtoincl : ('a1, 'a2) weq -> ('a1, 'a2) incl

val isinclcomp : ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) isincl

val inclcomp : ('a1, 'a2) incl -> ('a2, 'a3) incl -> ('a1, 'a3) incl

val isincltwooutof3a :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl ->
  ('a1, 'a2) isincl

val isinclgwtog :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) isincl -> ('a2, 'a3) isincl

val isinclgtogw :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isincl

val isinclhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isincl ->
  ('a1, 'a2) isincl

val isofhlevelsninclb :
  nat -> ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isofhlevel -> 'a1 isofhlevel

val isapropinclb :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a2 isaprop -> 'a1 isaprop

val iscontrhfiberofincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> ('a1, 'a2) hfiber iscontr

type ('x, 'y) isInjective = 'x -> 'x -> ('x paths, 'y paths) isweq

val coq_Injectivity :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> 'a1 -> 'a1 -> ('a1 paths, 'a2
  paths) weq

val isweqonpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) isInjective

val weqonpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths)
  weq

val invmaponpathsincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths

val isinclweqonpaths :
  ('a1 -> 'a2) -> ('a1, 'a2) isInjective -> ('a1, 'a2) isincl

val isinclpr1 : ('a1 -> 'a2 isaprop) -> (('a1, 'a2) total2, 'a1) isincl

val subtypeInjectivity :
  ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1,
  'a2) total2 paths, 'a1 paths) weq

val subtypePath :
  ('a1, 'a2) isPredicate -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1
  paths -> ('a1, 'a2) total2 paths

val subtypePath' :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 isaprop -> ('a1,
  'a2) total2 paths

val unique_exists :
  'a1 -> 'a2 -> ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2 -> 'a1 paths) -> ('a1,
  'a2) total2 iscontr

val subtypePairEquality :
  ('a1, 'a2) isPredicate -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1,
  'a2) total2 paths

val subtypePairEquality' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 isaprop -> ('a1, 'a2) total2
  paths

val samehfibers :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a3) hfiber) weq

type 'x isaset = 'x -> 'x -> 'x paths isaprop

val isasetunit : coq_unit isaset

val isasetempty : empty isaset

val isasetifcontr : 'a1 iscontr -> 'a1 isaset

val isasetaprop : 'a1 isaprop -> 'a1 isaset

val isaset_total2 :
  'a1 isaset -> ('a1 -> 'a2 isaset) -> ('a1, 'a2) total2 isaset

val isaset_dirprod : 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) dirprod isaset

val isaset_hfiber :
  ('a1 -> 'a2) -> 'a2 -> 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) hfiber isaset

val uip :
  'a1 isaset -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val isofhlevelssnset : nat -> 'a1 isaset -> 'a1 isofhlevel

val isasetifiscontrloops : ('a1 -> 'a1 paths iscontr) -> 'a1 isaset

val iscontrloopsifisaset : 'a1 isaset -> 'a1 -> 'a1 paths iscontr

val isasetsubset :
  ('a1 -> 'a2) -> 'a2 isaset -> ('a1, 'a2) isincl -> 'a1 isaset

val isinclfromhfiber :
  ('a1 -> 'a2) -> 'a2 isaset -> 'a2 -> (('a1, 'a2) hfiber, 'a1) isincl

val isinclbetweensets :
  ('a1 -> 'a2) -> 'a1 isaset -> 'a2 isaset -> ('a1 -> 'a1 -> 'a2 paths -> 'a1
  paths) -> ('a1, 'a2) isincl

val isinclfromunit : (coq_unit -> 'a1) -> 'a1 isaset -> (coq_unit, 'a1) isincl

val set_bijection_to_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> 'a2 isaset -> ('a1,
  'a2) isweq

type ('p, 'q) complementary = ('p -> 'q -> empty, ('p, 'q) coprod) dirprod

val complementary_to_neg_iff :
  ('a1, 'a2) complementary -> ('a1 neg, 'a2) logeq

type 'x decidable = ('x, 'x neg) coprod

val decidable_to_complementary : 'a1 decidable -> ('a1, 'a1 neg) complementary

val decidable_dirprod :
  'a1 decidable -> 'a2 decidable -> ('a1, 'a2) dirprod decidable

type 'p isdecprop = (('p, 'p neg) coprod, 'p isaprop) dirprod

val isdecproptoisaprop : 'a1 isdecprop -> 'a1 isaprop

val isdecpropif : 'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop

val isdecpropfromiscontr : 'a1 iscontr -> 'a1 isdecprop

val isdecpropempty : empty isdecprop

val isdecpropweqf : ('a1, 'a2) weq -> 'a1 isdecprop -> 'a2 isdecprop

val isdecpropweqb : ('a1, 'a2) weq -> 'a2 isdecprop -> 'a1 isdecprop

val isdecproplogeqf :
  'a1 isdecprop -> 'a2 isaprop -> ('a1, 'a2) logeq -> 'a2 isdecprop

val isdecproplogeqb :
  'a1 isaprop -> 'a2 isdecprop -> ('a1, 'a2) logeq -> 'a1 isdecprop

val isdecpropfromneg : 'a1 neg -> 'a1 isdecprop

type 'x isdeceq = 'x -> 'x -> 'x paths decidable

val isdeceqweqf : ('a1, 'a2) weq -> 'a1 isdeceq -> 'a2 isdeceq

val isdeceqweqb : ('a1, 'a2) weq -> 'a2 isdeceq -> 'a1 isdeceq

val isdeceqinclb :
  ('a1 -> 'a2) -> 'a2 isdeceq -> ('a1, 'a2) isincl -> 'a1 isdeceq

val isdeceqifisaprop : 'a1 isaprop -> 'a1 isdeceq

val booleq : 'a1 isdeceq -> 'a1 -> 'a1 -> bool

val eqfromdnegeq : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths dneg -> 'a1 paths

val isdecequnit : coq_unit isdeceq

val isdeceqbool : bool isdeceq

val isdeceqcoprod : 'a1 isdeceq -> 'a2 isdeceq -> ('a1, 'a2) coprod isdeceq

type 'x isisolated = 'x -> ('x paths, 'x paths neg) coprod

type 't isolated = ('t, 't isisolated) total2

val make_isolated : 'a1 -> 'a1 isisolated -> 'a1 isolated

val pr1isolated : 'a1 isolated -> 'a1

val isaproppathsfromisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop

val isaproppathstoisolated : 'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop

val isisolatedweqf : ('a1, 'a2) weq -> 'a1 -> 'a1 isisolated -> 'a2 isisolated

val isisolatedinclb :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a2 isisolated -> 'a1 isisolated

val disjointl1 : ('a1, coq_unit) coprod isisolated

val isasetifdeceq : 'a1 isdeceq -> 'a1 isaset

val isdeceq_total2 :
  'a1 isdeceq -> ('a1 -> 'a2 isdeceq) -> ('a1, 'a2) total2 isdeceq

val isolfun1 : 'a1 -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a1 -> 'a2

val decfun1 : 'a1 isdeceq -> 'a1 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isolfun2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a2 -> 'a2 -> 'a2 -> 'a1
  -> 'a2

val decfun2 : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isolfun3 :
  'a1 -> 'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 isisolated ->
  'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val decfun3 :
  'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a1 -> 'a2

val isasetbool : bool isaset

val subsetsplit :
  ('a1 -> bool) -> 'a1 -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod

val subsetsplitinv :
  ('a1 -> bool) -> (('a1, bool) hfiber, ('a1, bool) hfiber) coprod -> 'a1

val weqsubsetsplit :
  ('a1 -> bool) -> ('a1, (('a1, bool) hfiber, ('a1, bool) hfiber) coprod) weq
open PartA
open PartB
open Preamble
open UnivalenceAxiom

val isapropneg : 'a1 neg isaprop

val isaprop_isProofIrrelevant : 'a1 isProofIrrelevant isaprop

val isapropdneg : 'a1 dneg isaprop

type 'x isaninvprop = ('x, 'x dneg) isweq

val invimpl : 'a1 isaninvprop -> 'a1 dneg -> 'a1

val isapropaninvprop : 'a1 isaninvprop -> 'a1 isaprop

val isaninvpropneg : 'a1 neg isaninvprop

val isapropdec : 'a1 isaprop -> 'a1 decidable isaprop

type 'x compl = ('x, 'x paths neg) total2

val make_compl : 'a1 -> 'a1 -> 'a1 paths neg -> ('a1, 'a1 paths neg) total2

val pr1compl : 'a1 -> ('a1, 'a1 paths neg) total2 -> 'a1

val isinclpr1compl : 'a1 -> (('a1, 'a1 paths neg) total2, 'a1) isincl

val recompl : 'a1 -> ('a1 compl, coq_unit) coprod -> 'a1

val maponcomplincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 compl -> 'a2 compl

val weqoncompl : ('a1, 'a2) weq -> 'a1 -> ('a1 compl, 'a2 compl) weq

val weqoncompl_compute : ('a1, 'a2) weq -> 'a1 -> 'a1 compl -> 'a2 paths

val homotweqoncomplcomp :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a1 -> ('a1 compl, 'a3 compl) homot

val invrecompl : 'a1 -> 'a1 isisolated -> 'a1 -> ('a1 compl, coq_unit) coprod

val isweqrecompl :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq

val weqrecompl :
  'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) weq

val homotrecomplnat :
  ('a1, 'a2) weq -> 'a1 -> ('a1 compl, coq_unit) coprod -> 'a2 paths

val recomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 -> 'a2

val weqrecomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl, 'a2 compl)
  weq -> ('a1, 'a2) weq

val homotrecomplfhomot :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> ('a1 compl ->
  'a2 compl) -> ('a1 compl, 'a2 compl) homot -> ('a1, 'a2) homot

val pathsrecomplfxtoy :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a2 paths

val homotrecomplfcomp :
  'a1 -> 'a2 -> 'a3 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl -> 'a2
  compl) -> ('a2 compl -> 'a3 compl) -> ('a1, 'a3) homot

val homotrecomplfidfun : 'a1 -> 'a1 isisolated -> ('a1, 'a1) homot

val ishomotinclrecomplf :
  'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 compl ->
  'a2 compl -> 'a2 paths -> 'a2 compl paths

val funtranspos0 : 'a1 -> 'a1 -> 'a1 isisolated -> 'a1 compl -> 'a1 compl

val homottranspos0t2t1t1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl)
  homot

val weqtranspos0 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl) weq

val funtranspos : 'a1 isolated -> 'a1 isolated -> 'a1 -> 'a1

val homottranspost2t1t1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot

val weqtranspos :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) weq

val pathsfuntransposoft1 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths

val pathsfuntransposoft2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths

val pathsfuntransposofnet1t2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 -> 'a1 paths neg ->
  'a1 paths neg -> 'a1 paths

val homotfuntranspos2 :
  'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot

val eqbx : 'a1 -> 'a1 isisolated -> 'a1 -> bool

val iscontrhfibereqbx : 'a1 -> 'a1 isisolated -> ('a1, bool) hfiber iscontr

type ('x, 'y) bhfiber = ('x, bool) hfiber

val weqhfibertobhfiber :
  ('a1 -> 'a2) -> 'a2 -> 'a2 isisolated -> (('a1, 'a2) hfiber, ('a1, 'a2)
  bhfiber) weq

val isinclii1 : ('a1, ('a1, 'a2) coprod) isincl

val iscontrhfiberii1x : 'a1 -> ('a1, ('a1, 'a2) coprod) hfiber iscontr

val neghfiberii1y : 'a2 -> ('a1, ('a1, 'a2) coprod) hfiber neg

val isinclii2 : ('a2, ('a1, 'a2) coprod) isincl

val iscontrhfiberii2y : 'a2 -> ('a2, ('a1, 'a2) coprod) hfiber iscontr

val neghfiberii2x : 'a1 -> ('a2, ('a1, 'a2) coprod) hfiber neg

val negintersectii1ii2 :
  ('a1, 'a2) coprod -> ('a1, ('a1, 'a2) coprod) hfiber -> ('a2, ('a1, 'a2)
  coprod) hfiber -> empty

val isolatedtoisolatedii1 :
  'a1 -> 'a1 isisolated -> ('a1, 'a2) coprod isisolated

val isolatedtoisolatedii2 :
  'a2 -> 'a2 isisolated -> ('a1, 'a2) coprod isisolated

val weqhfibercoprodf1 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 -> (('a1, 'a3) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val weqhfibercoprodf2 :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a4 -> (('a2, 'a4) hfiber, (('a1, 'a2)
  coprod, ('a3, 'a4) coprod) hfiber) weq

val isofhlevelfcoprodf :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a4)
  isofhlevelf -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) isofhlevelf

val isofhlevelsnsummand1 :
  nat -> ('a1, 'a2) coprod isofhlevel -> 'a1 isofhlevel

val isofhlevelsnsummand2 :
  nat -> ('a1, 'a2) coprod isofhlevel -> 'a2 isofhlevel

val isofhlevelssncoprod :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) coprod isofhlevel

val isasetcoprod : 'a1 isaset -> 'a2 isaset -> ('a1, 'a2) coprod isaset

val coprodofhfiberstohfiber :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) coprod -> (('a1, 'a2) coprod, 'a3) hfiber

val hfibertocoprodofhfibers :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a2) coprod, 'a3) hfiber ->
  (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) coprod

val weqhfibersofsumofmaps :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> ((('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) coprod, (('a1, 'a2) coprod, 'a3) hfiber) weq

val isofhlevelfssnsumofmaps :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> (('a1, 'a2) coprod, 'a3) isofhlevelf

val noil1 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a1, 'a3) hfiber -> ('a2, 'a3) hfiber -> empty

val weqhfibernoi1 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a1, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a1, 'a3) hfiber)
  weq

val weqhfibernoi2 :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
  ('a2, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a2, 'a3) hfiber)
  weq

val isofhlevelfsumofmapsnoi :
  nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2, 'a3)
  isofhlevelf -> ('a1 -> 'a2 -> 'a3 paths neg) -> (('a1, 'a2) coprod, 'a3)
  isofhlevelf

val tocompltoii1x : 'a1 -> ('a1 compl, 'a2) coprod -> ('a1, 'a2) coprod compl

val fromcompltoii1x :
  'a1 -> ('a1, 'a2) coprod compl -> ('a1 compl, 'a2) coprod

val isweqtocompltoii1x :
  'a1 -> (('a1 compl, 'a2) coprod, ('a1, 'a2) coprod compl) isweq

val tocompltoii2y : 'a2 -> ('a1, 'a2 compl) coprod -> ('a1, 'a2) coprod compl

val fromcompltoii2y :
  'a2 -> ('a1, 'a2) coprod compl -> ('a1, 'a2 compl) coprod

val isweqtocompltoii2y :
  'a2 -> (('a1, 'a2 compl) coprod, ('a1, 'a2) coprod compl) isweq

val tocompltodisjoint : 'a1 -> ('a1, coq_unit) coprod compl

val fromcompltodisjoint : ('a1, coq_unit) coprod compl -> 'a1

val isweqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) isweq

val weqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) weq

val isweqfromcompltodisjoint : (('a1, coq_unit) coprod compl, 'a1) isweq

val isdecpropif' :
  'a1 isaprop -> ('a1, 'a1 neg) coprod -> ('a1, 'a1 neg) coprod iscontr

val isdecproppaths : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths isdecprop

val isdeceqif : ('a1 -> 'a1 -> 'a1 paths isdecprop) -> 'a1 isdeceq

val isaninv1 : 'a1 isdecprop -> 'a1 isaninvprop

val isdecpropfibseq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a1
  isdecprop -> 'a3 isaprop -> 'a2 isdecprop

val isdecpropfibseq0 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
  isdecprop -> 'a3 isdeceq -> 'a1 isdecprop

val isdecpropdirprod :
  'a1 isdecprop -> 'a2 isdecprop -> ('a1, 'a2) dirprod isdecprop

val fromneganddecx :
  'a1 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod

val fromneganddecy :
  'a2 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod

val isdecproppathsfromisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop

val isdecproppathstoisolated :
  'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop

type ('x, 'y) isdecincl = 'y -> ('x, 'y) hfiber isdecprop

val isdecincltoisincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) isincl

val isdecinclfromisweq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isdecincl

val isdecpropfromdecincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> 'a2 isdecprop -> 'a1 isdecprop

val isdecinclii1 : ('a1, ('a1, 'a2) coprod) isdecincl

val isdecinclii2 : ('a2, ('a1, 'a2) coprod) isdecincl

val isdecinclpr1 :
  ('a1 -> 'a2 isdecprop) -> (('a1, 'a2) total2, 'a1) isdecincl

val isdecinclhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) isdecincl
  -> ('a1, 'a2) isdecincl

val isdecinclcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isdecincl -> ('a2, 'a3)
  isdecincl -> ('a1, 'a3) isdecincl

val isdecinclf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isdecincl
  -> ('a1, 'a2) isdecincl

val isdecinclg :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isdecincl ->
  ('a2, 'a3) isdecincl

val isisolateddecinclf :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) isdecincl -> 'a1 isisolated -> 'a2
  isisolated

type ('x, 'y) negimage = ('y, ('x, 'y) hfiber neg) total2

val make_negimage :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber neg -> ('a2, ('a1, 'a2) hfiber
  neg) total2

val isinclfromcoprodwithnegimage :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> (('a1, ('a2, ('a1, 'a2) hfiber neg)
  total2) coprod, 'a2) isincl

type ('x, 'y) iscoproj =
  (('x, ('y, ('x, 'y) hfiber neg) total2) coprod, 'y) isweq

val weqcoproj :
  ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> (('a1, ('a1, 'a2) negimage) coprod,
  'a2) weq

val iscoprojfromisdecincl :
  ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) iscoproj

val isdecinclfromiscoproj :
  ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> ('a1, 'a2) isdecincl
open PartA
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

val eqweqmap_transportb : __ paths -> ('a2 -> 'a1) paths

val eqweqmap_weqtopaths : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val sum_of_fibers : ('a1 -> 'a2) -> (('a2, ('a1, 'a2) hfiber) total2, 'a1) weq

type 'a display = (__, 'a) hfiber

val totalfst : (__, __ -> 'a1) total2

val totalfst_display : (__, __ -> 'a1) total2 -> (__, __ -> 'a1) total2 paths

val display_totalfst : __ paths

val display_weq : ((__, __ -> 'a1) total2, __) weq
open PartA
open PartB
open PartC
open Preamble
open UnivalenceAxiom

val totaltoforall :
  ('a1 -> 'a2, 'a1 -> 'a3) total2 -> 'a1 -> ('a2, 'a3) total2

val foralltototal :
  ('a1 -> ('a2, 'a3) total2) -> ('a1 -> 'a2, 'a1 -> 'a3) total2

val isweqforalltototal :
  ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) isweq

val isweqtotaltoforall :
  (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) isweq

val weqforalltototal :
  ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq

val weqtotaltoforall :
  (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) weq

val weqfuntototaltototal :
  ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq

val funtoprodtoprod :
  ('a1 -> ('a2, 'a3) dirprod) -> ('a1 -> 'a2, 'a1 -> 'a3) dirprod

val prodtofuntoprod :
  ('a1 -> 'a2, 'a1 -> 'a3) dirprod -> 'a1 -> ('a2, 'a3) dirprod

val weqfuntoprodtoprod :
  ('a1 -> ('a2, 'a3) dirprod, ('a1 -> 'a2, 'a1 -> 'a3) dirprod) weq

val maponsec : ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val maponsec1 : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val hfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a2, 'a1 -> 'a3) hfiber ->
  'a1 -> ('a2, 'a3) hfiber

val foralltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber) -> ('a1
  -> 'a2, 'a1 -> 'a3) hfiber

val isweqhfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
  'a1 -> ('a2, 'a3) hfiber) isweq

val weqhfibertoforall :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
  'a1 -> ('a2, 'a3) hfiber) weq

val isweqforalltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
  'a2, 'a1 -> 'a3) hfiber) isweq

val weqforalltohfiber :
  ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
  'a2, 'a1 -> 'a3) hfiber) weq

val isweqmaponsec : ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) isweq

val weqonsecfibers : ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) weq

val weqffun : ('a2, 'a3) weq -> ('a1 -> 'a2, 'a1 -> 'a3) weq

val maponsec1l0 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2

val maponsec1l1 : 'a1 -> ('a1 -> 'a2) -> 'a2 paths

val maponsec1l2 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths

val isweqmaponsec1 : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val weqonsecbase : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq

val weqbfun : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq

val iscontrsecoverempty : (empty -> 'a1) iscontr

val iscontrsecoverempty2 : 'a1 neg -> ('a1 -> 'a2) iscontr

val secovercoprodtoprod :
  (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod

val prodtosecovercoprod :
  ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3

val weqsecovercoprodtoprod :
  (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq

val iscontrfunfromempty : (empty -> 'a1) iscontr

val iscontrfunfromempty2 : 'a2 neg -> ('a2 -> 'a1) iscontr

val funfromcoprodtoprod :
  (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod

val prodtofunfromcoprod :
  ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3

val weqfunfromcoprodtoprod :
  (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq

val tosecoverunit : 'a1 -> coq_unit -> 'a1

val weqsecoverunit : (coq_unit -> 'a1, 'a1) weq

val weqsecovercontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq

val tosecovertotal2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val weqsecovertotal2 : (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq

val weqfunfromunit : (coq_unit -> 'a1, 'a1) weq

val weqfunfromcontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq

val weqfunfromtotal2 : (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq

val weqfunfromdirprod : (('a1, 'a2) dirprod -> 'a3, 'a1 -> 'a2 -> 'a3) weq

val impred : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel

val impred_iscontr : ('a1 -> 'a2 iscontr) -> ('a1 -> 'a2) iscontr

val impred_isaprop : ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2) isaprop

val impred_isaset : ('a1 -> 'a2 isaset) -> ('a1 -> 'a2) isaset

val impredtwice :
  nat -> ('a1 -> 'a2 -> 'a3 isofhlevel) -> ('a1 -> 'a2 -> 'a3) isofhlevel

val impredfun : nat -> 'a2 isofhlevel -> ('a1 -> 'a2) isofhlevel

val impredtech1 : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel

val iscontrfuntounit : ('a1 -> coq_unit) iscontr

val iscontrfuntocontr : 'a2 iscontr -> ('a1 -> 'a2) iscontr

val isapropimpl : 'a2 isaprop -> ('a1 -> 'a2) isaprop

val isapropneg2 : 'a2 neg -> ('a1 -> 'a2) isaprop

val iscontriscontr : 'a1 iscontr -> 'a1 iscontr iscontr

val isapropiscontr : 'a1 iscontr isaprop

val isapropisweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq isaprop

val isapropisisolated : 'a1 -> 'a1 isisolated isaprop

val isapropisdeceq : 'a1 isdeceq isaprop

val isapropisofhlevel : nat -> 'a1 isofhlevel isaprop

val isapropisaprop : 'a1 isaprop isaprop

val isapropisdecprop : 'a1 isdecprop isaprop

val isapropisaset : 'a1 isaset isaprop

val isapropisofhlevelf : nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop

val isapropisincl : ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop

val isaprop_isInjective : ('a1 -> 'a2) -> ('a1, 'a2) isInjective isaprop

val incl_injectivity :
  ('a1 -> 'a2) -> (('a1, 'a2) isincl, ('a1, 'a2) isInjective) weq

val isinclpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isincl

val isinjpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isInjective

val isinclpr1isolated : ('a1 isolated, 'a1) isincl

val weqcomp_assoc :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths

val eqweqmap_pathscomp0 : coq_UU paths -> coq_UU paths -> ('a1, 'a3) weq paths

val inv_idweq_is_idweq : ('a1, 'a1) weq paths

val eqweqmap_pathsinv0 : coq_UU paths -> ('a2, 'a1) weq paths

val weqfweq : ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) weq

val weqbweq : ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) weq

val weqweq : ('a1, 'a2) weq -> (('a1, 'a1) weq, ('a2, 'a2) weq) weq

val weqinvweq : (('a1, 'a2) weq, ('a2, 'a1) weq) weq

val isofhlevelsnweqtohlevelsn :
  nat -> 'a2 isofhlevel -> ('a1, 'a2) weq isofhlevel

val isofhlevelsnweqfromhlevelsn :
  nat -> 'a2 isofhlevel -> ('a2, 'a1) weq isofhlevel

val isapropweqtocontr : 'a2 iscontr -> ('a1, 'a2) weq isaprop

val isapropweqfromcontr : 'a2 iscontr -> ('a2, 'a1) weq isaprop

val isapropweqtoprop : 'a2 isaprop -> ('a1, 'a2) weq isaprop

val isapropweqfromprop : 'a2 isaprop -> ('a2, 'a1) weq isaprop

val isasetweqtoset : 'a2 isaset -> ('a1, 'a2) weq isaset

val isasetweqfromset : 'a2 isaset -> ('a2, 'a1) weq isaset

val isapropweqtoempty : ('a1, empty) weq isaprop

val isapropweqtoempty2 : 'a2 neg -> ('a1, 'a2) weq isaprop

val isapropweqfromempty : (empty, 'a1) weq isaprop

val isapropweqfromempty2 : 'a2 neg -> ('a2, 'a1) weq isaprop

val isapropweqtounit : ('a1, coq_unit) weq isaprop

val isapropweqfromunit : (coq_unit, 'a1) weq isaprop

val cutonweq :
  'a1 -> 'a1 isisolated -> ('a1, 'a1) weq -> ('a1 isolated, ('a1 compl, 'a1
  compl) weq) dirprod

val invcutonweq :
  'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq) dirprod
  -> ('a1, 'a1) weq

val pathsinvcuntonweqoft :
  'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq) dirprod
  -> 'a1 paths

val weqcutonweq :
  'a1 -> 'a1 isisolated -> (('a1, 'a1) weq, ('a1 isolated, ('a1 compl, 'a1
  compl) weq) dirprod) weq

val weqcompidl : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val weqcompidr : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val weqcompinvl : ('a1, 'a2) weq -> ('a2, 'a2) weq paths

val weqcompinvr : ('a1, 'a2) weq -> ('a1, 'a1) weq paths

val weqcompassoc :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths

val weqcompweql : ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) isweq

val weqcompweqr : ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) isweq

val weqcompinjr :
  ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq paths
  -> ('a1, 'a2) weq paths

val weqcompinjl :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq paths
  -> ('a2, 'a3) weq paths

val invweqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a1) weq paths

val invmapweqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths
open PartA
open PartA0
open PartB
open Preamble

type __ = Obj.t

type ('x, 'y) coq_PathOver = __

val coq_PathOverToPathPair :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathPair

val apd : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> ('a1, 'a2) coq_PathOver

val coq_PathOverToTotalPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) total2 paths

val coq_PathOverUniqueness :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a2, ('a1, 'a2) coq_PathOver) total2
  iscontr

val stdPathOver : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver

val stdPathOver' : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver

val identityPathOver : 'a1 -> 'a2 -> ('a1, 'a2) coq_PathOver

val pathOverIdpath : 'a1 -> 'a2 -> 'a2 -> __ paths

val toPathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver

val fromPathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2 paths

val inductionPathOver :
  'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver ->
  'a3

val transportPathOver :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> 'a3 ->
  'a3

val transportPathOver' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a3 ->
  'a3

val composePathOver :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1,
  'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver

val composePathOverPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver

val composePathOverIdpath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathPathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver

val composeIdpathPathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathPathOverRotate :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver paths,
  ('a1, 'a2) coq_PathOver paths) logeq

val composePathOverPathRotate :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver paths,
  ('a1, 'a2) coq_PathOver paths) logeq

val composePathPathOverPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1,
  'a2) coq_PathOver -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val composePathOverLeftUnit :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathOverRightUnit :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val assocPathOver :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a2 ->
  'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val inversePathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver

val inversePathOver' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver

val inverseInversePathOver1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inverseInversePathOver2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inversePathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val inversePathOverIdpath' :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val inverseInversePathOver :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inversePathOverWeq :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
  'a2) coq_PathOver) weq

val inversePathOverWeq' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
  'a2) coq_PathOver) weq

val coq_PathOverConstant_id :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> coq_UU paths

val coq_PathOverConstant_map1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver

val coq_PathOverConstant_map1_eq1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1, 'a2) coq_PathOver paths

val coq_PathOverConstant_map1_eq2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1, 'a2) coq_PathOver paths

val coq_PathOverConstant_map2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2
  paths

val coq_PathOverConstant_map2_apd :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths paths

val coq_PathOverConstant_map2_eq1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> 'a2 paths paths

val coq_PathOverConstant_map2_eq2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> 'a2 paths paths

val coq_PathOverConstant_map1_map2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths paths

val coq_Lemma023 :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
  'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver)
  isweq

val composePathOver_weq :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
  'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) weq

val coq_Lemma0_2_4 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) isweq

val cp :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) weq

val composePathOverPath_compute :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver paths

val composePathPathOver_compute :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val cp_idpath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val cp_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val cp_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val cp_in_family :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a2 -> 'a1 paths) -> 'a3 -> 'a3
  -> ('a2 -> ('a1, 'a3) coq_PathOver) -> ('a1, 'a3) coq_PathOver paths

val cp_irrelevance :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  'a1 paths paths -> 'a1 isofhlevel -> (('a1, 'a2) coq_PathOver, ('a1, 'a2)
  coq_PathOver) weq paths

val coq_Unnamed_thm :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> coq_UU paths

val inverse_cp_p :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val inverse_cp_p' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver

val inverse_cp_p'' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver

val inverse_cp_p_compare :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver paths

val cp_inverse_cp :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val composePathOverRightInverse :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathOverLeftInverse :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val cp_pathscomp0 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths -> 'a1 paths paths -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val apstar :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
  'a1 paths paths -> 'a1 paths paths -> 'a1 paths paths

val cp_apstar :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
  'a1 paths paths -> 'a1 paths paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val cp_apstar' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val pathOverEquations :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> __ paths

val pathOverEquations1 :
  ('a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> __
  paths

val mapPathOver :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a3) coq_PathOver

val binopPathOver :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a2 -> 'a2 -> 'a3
  -> 'a3 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a3) coq_PathOver -> ('a1, 'a4)
  coq_PathOver

type ('x, 'x0, 'y) pullBackFamily = 'y

val pullBackSection : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val pullBackPointOver :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a1, 'a2, 'a3)
  pullBackFamily

val pullBackPointOverWithSection :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3)
  pullBackFamily paths

val pullBackPointOverWithSection' :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a2 -> 'a3) -> 'a3 paths
  -> ('a1, 'a2, 'a3) pullBackFamily paths

val pullBackPathOverPoint :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> ('a1,
  'a2, 'a3) pullBackFamily paths

val pullBackPathOver :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> ('a1, ('a1, 'a2, 'a3) pullBackFamily) coq_PathOver

val pullBackPathOverPath :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
  coq_PathOver paths

val pullBackPathPathOver :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
  coq_PathOver paths

val transportf_to_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver

val isweq_transportf_to_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
  coq_PathOver) isweq

val transportf_weq_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
  coq_PathOver) weq

module PathsOverNotations :
 sig
 end

type __ = Obj.t

type coq_UU = __

type 'x fromUUtoType = 'x

type empty = |

val empty_rect : empty -> 'a1

val empty_rec : empty -> 'a1

type coq_unit =
| Coq_tt

val unit_rect : 'a1 -> coq_unit -> 'a1

val unit_rec : 'a1 -> coq_unit -> 'a1

type bool =
| Coq_true
| Coq_false

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

val negb : bool -> bool

type ('a, 'b) coprod =
| Coq_ii1 of 'a
| Coq_ii2 of 'b

val coprod_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

val coprod_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

type nat =
| O
| S of nat

val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

val succ : nat -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val mul : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

type 'a paths =
| Coq_paths_refl

val paths_rect : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

val paths_rec : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }

val total2_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val total2_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val pr1 : ('a1, 'a2) total2 -> 'a1

val pr2 : ('a1, 'a2) total2 -> 'a2
open Notations
open PartA
open PartA0
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

val ishinh_irrel : 'a1 -> hProptoType -> hProptoType paths

val squash_to_hProp :
  hProp -> hProptoType -> ('a1 -> hProptoType) -> hProptoType

val hdisj_impl_1 :
  hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) -> hProptoType

val hdisj_impl_2 :
  hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) -> hProptoType

val weqlogeq : hProp -> hProp -> (hProp paths, hProptoType) weq

val decidable_proof_by_contradiction :
  hProp -> hProptoType decidable -> hProptoType -> hProptoType

val proof_by_contradiction :
  hProp -> hProptoType -> hProptoType -> hProptoType

val dneg_elim_to_LEM : (hProp -> hProptoType -> hProptoType) -> hProptoType

val negforall_to_existsneg :
  ('a1 -> hProp) -> hProptoType -> hProptoType -> hProptoType

val negimpl_to_conj :
  hProp -> hProp -> hProptoType -> hProptoType -> hProptoType

val hrel_set : hSet -> hSet

val isaprop_assume_it_is : ('a1 -> 'a1 isaprop) -> 'a1 isaprop

val isaproptotal2 :
  ('a1, 'a2) isPredicate -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> ('a1,
  'a2) total2 isaprop

val squash_rec :
  (hProptoType -> hProp) -> ('a1 -> hProptoType) -> hProptoType -> hProptoType

val logeq_if_both_true :
  hProp -> hProp -> hProptoType -> hProptoType -> hProptoType

val logeq_if_both_false :
  hProp -> hProp -> hProptoType -> hProptoType -> hProptoType

val proofirrelevance_hProp : hProp -> hProptoType isProofIrrelevant

val iscontr_hProp : hProp

val islogeqassochconj :
  hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq

val islogeqcommhconj : hProp -> hProp -> (hProptoType, hProptoType) logeq

val islogeqassochdisj :
  hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq

val islogeqhconj_absorb_hdisj :
  hProp -> hProp -> (hProptoType, hProptoType) logeq

val islogeqhdisj_absorb_hconj :
  hProp -> hProp -> (hProptoType, hProptoType) logeq

val islogeqhfalse_hdisj : hProp -> (hProptoType, hProptoType) logeq

val islogeqhhtrue_hconj : hProp -> (hProptoType, hProptoType) logeq

val isassoc_hconj : hProp -> hProp -> hProp -> hProp paths

val iscomm_hconj : hProp -> hProp -> hProp paths

val isassoc_hdisj : hProp -> hProp -> hProp -> hProp paths

val iscomm_hdisj : hProp -> hProp -> hProp paths

val hconj_absorb_hdisj : hProp -> hProp -> hProp paths

val hdisj_absorb_hconj : hProp -> hProp -> hProp paths

val hfalse_hdisj : hProp -> hProp paths

val htrue_hconj : hProp -> hProp paths

val squash_uniqueness : 'a1 -> hProptoType -> hProptoType paths

val coq_Unnamed_thm : 'a2 isaprop -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths

val factor_dep_through_squash :
  (hProptoType -> 'a2 isaprop) -> ('a1 -> 'a2) -> hProptoType -> 'a2

val factor_through_squash_hProp :
  hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType

val funspace_isaset : 'a2 isaset -> ('a1 -> 'a2) isaset

val squash_map_uniqueness :
  'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1, 'a2)
  homot -> (hProptoType, 'a2) homot

val squash_map_epi :
  'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1 -> 'a2)
  paths -> (hProptoType -> 'a2) paths

val uniqueExists :
  'a1 -> 'a1 -> ('a1, 'a2) total2 iscontr -> 'a2 -> 'a2 -> 'a1 paths

val isConnected : hProp

val predicateOnConnectedType :
  hProptoType -> ('a1 -> hProp) -> 'a1 -> hProptoType -> 'a1 -> hProptoType

val isBaseConnected : coq_PointedType -> hProp

val isConnected_isBaseConnected :
  coq_PointedType -> (hProptoType, hProptoType) logeq

val coq_BasePointComponent : coq_PointedType -> coq_PointedType

val basePointComponent_inclusion :
  coq_PointedType -> underlyingType -> underlyingType

val coq_BasePointComponent_isBaseConnected : coq_PointedType -> hProptoType

val coq_BasePointComponent_isincl :
  coq_PointedType -> (underlyingType, underlyingType) isincl

val coq_BasePointComponent_isweq :
  coq_PointedType -> hProptoType -> (underlyingType, underlyingType) isweq

val coq_BasePointComponent_weq :
  coq_PointedType -> hProptoType -> (underlyingType, underlyingType) weq

val baseConnectedness : coq_PointedType -> hProptoType -> hProptoType

val predicateOnBaseConnectedType :
  coq_PointedType -> hProptoType -> (underlyingType -> hProp) -> hProptoType
  -> underlyingType -> hProptoType

val predicateOnBasePointComponent :
  coq_PointedType -> (underlyingType -> hProp) -> hProptoType ->
  underlyingType -> hProptoType
open PartA
open PartB
open PartC
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

type hProp = (coq_UU, __ isaprop) total2

val make_hProp : 'a1 isaprop -> hProp

type hProptoType = __

val propproperty : hProp -> __ isaprop

type tildehProp = (hProp, hProptoType) total2

val make_tildehProp : hProp -> hProptoType -> tildehProp

val subtypeInjectivity_prop :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  (('a1, hProptoType) total2 paths, 'a1 paths) weq

val subtypePath_prop :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  'a1 paths -> ('a1, hProptoType) total2 paths

val impred_prop : ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop

val isaprop_total2 :
  hProp -> (hProptoType -> hProp) -> (hProptoType, hProptoType) total2 isaprop

val isaprop_forall_hProp : ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop

val forall_hProp : ('a1 -> hProp) -> hProp

type 'x ishinh_UUU = hProp -> ('x -> hProptoType) -> hProptoType

val isapropishinh : 'a1 ishinh_UUU isaprop

val ishinh : hProp

val hinhpr : 'a1 -> hProptoType

val hinhfun : ('a1 -> 'a2) -> hProptoType -> hProptoType

val hinhuniv : hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType

val factor_through_squash : 'a2 isaprop -> ('a1 -> 'a2) -> hProptoType -> 'a2

val squash_to_prop : hProptoType -> 'a2 isaprop -> ('a1 -> 'a2) -> 'a2

val hinhand : hProptoType -> hProptoType -> hProptoType

val hinhuniv2 :
  hProp -> ('a1 -> 'a2 -> hProptoType) -> hProptoType -> hProptoType ->
  hProptoType

val hinhfun2 :
  ('a1 -> 'a2 -> 'a3) -> hProptoType -> hProptoType -> hProptoType

val hinhunivcor1 : hProp -> hProptoType -> hProptoType

val weqishinhnegtoneg : (hProptoType, 'a1 neg) weq

val weqnegtonegishinh : ('a1 neg, hProptoType neg) weq

val hinhcoprod : hProptoType -> hProptoType

val decidable_ishinh : 'a1 decidable -> hProptoType decidable

type ('x, 'y) image = ('y, hProptoType) total2

val make_image :
  ('a1 -> 'a2) -> 'a2 -> hProptoType -> ('a2, hProptoType) total2

val pr1image : ('a1 -> 'a2) -> ('a2, hProptoType) total2 -> 'a2

val prtoimage : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) image

type ('x, 'y) issurjective = 'y -> hProptoType

val isapropissurjective : ('a1 -> 'a2) -> ('a1, 'a2) issurjective isaprop

val isinclpr1image : ('a1 -> 'a2) -> (('a2, hProptoType) total2, 'a2) isincl

val issurjprtoimage : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) image) issurjective

val issurjcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective -> ('a2, 'a3)
  issurjective -> ('a1, 'a3) issurjective

val issurjtwooutof3b :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) issurjective -> ('a2, 'a3)
  issurjective

val isweqinclandsurj :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) issurjective -> ('a1, 'a2)
  isweq

val issurjectiveweq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) issurjective

val htrue : hProp

val hfalse : hProp

val hconj : hProp -> hProp -> hProp

val hdisj : hProp

val hdisj_in1 : 'a1 -> hProptoType

val hdisj_in2 : 'a2 -> hProptoType

val disjoint_disjunction :
  hProp -> hProp -> (hProptoType -> hProptoType -> empty) -> hProp

val hneg : hProp

val himpl : hProp -> hProp

val hexists : hProp

val wittohexists : 'a1 -> 'a2 -> hProptoType

val total2tohexists : ('a1, 'a2) total2 -> hProptoType

val weqneghexistsnegtotal2 : (hProptoType neg, ('a1, 'a2) total2 neg) weq

val islogeqcommhdisj : hProp -> hProp -> (hProptoType, hProptoType) logeq

val hconjtohdisj : hProp -> hProptoType -> hProptoType

val hexistsnegtonegforall : hProptoType -> ('a1 -> 'a2) neg

val forallnegtoneghexists : ('a1 -> 'a2 neg) -> hProptoType neg

val neghexisttoforallneg : hProptoType -> 'a1 -> hProptoType

val weqforallnegtonegexists : ('a1 -> hProptoType, hProptoType) weq

val tonegdirprod : hProptoType -> hProptoType

val weak_fromnegdirprod : hProp -> hProp -> hProptoType -> hProptoType dneg

val tonegcoprod : (hProptoType, hProptoType) dirprod -> hProptoType

val toneghdisj : (hProptoType, hProptoType) dirprod -> hProptoType

val fromnegcoprod : hProptoType -> (hProptoType, hProptoType) dirprod

val fromnegcoprod_prop : hProp -> hProp -> hProptoType -> hProptoType

val hdisjtoimpl : hProp -> hProptoType -> hProptoType -> hProptoType

val isdecprophdisj : 'a1 isdecprop -> 'a2 isdecprop -> hProptoType isdecprop

val isinhdneg : hProp

val inhdnegpr : 'a1 -> hProptoType

val inhdnegfun : ('a1 -> 'a2) -> hProptoType -> hProptoType

val inhdneguniv : ('a2, 'a2 dneg) isweq -> ('a1 -> 'a2) -> hProptoType -> 'a2

val inhdnegand : hProptoType -> hProptoType -> hProptoType

val hinhimplinhdneg : hProptoType -> hProptoType

val hPropUnivalence :
  hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
  hProptoType) -> hProp paths

val eqweqmaphProp :
  hProp -> hProp -> hProp paths -> (hProptoType, hProptoType) weq

val weqtopathshProp :
  hProp -> hProp -> (hProptoType, hProptoType) weq -> hProp paths

val weqpathsweqhProp :
  hProp -> hProp -> (hProptoType, hProptoType) weq -> (hProptoType,
  hProptoType) weq paths

val univfromtwoaxiomshProp :
  hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) isweq

val weqeqweqhProp :
  hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) weq

val isasethProp : hProp isaset

val weqpathsweqhProp' : hProp -> hProp -> hProp paths -> hProp paths paths

val iscontrtildehProp : tildehProp iscontr

val isaproptildehProp : tildehProp isaprop

val isasettildehProp : tildehProp isaset

val logeqweq :
  hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
  hProptoType) -> (hProptoType, hProptoType) weq

val total2_paths_hProp_equiv :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  (('a1, hProptoType) total2 paths, 'a1 paths) weq
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

type __ = Obj.t

val hProp_set : hSet

val isconst : hSet -> ('a1 -> pr1hSet) -> hProp

val squash_to_hSet :
  hSet -> ('a1 -> pr1hSet) -> hProptoType -> hProptoType -> pr1hSet

val isconst_2 : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp

val squash_to_hSet_2 :
  hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
  hProptoType -> pr1hSet

val isconst_2' : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp

val squash_to_hSet_2' :
  hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
  hProptoType -> pr1hSet

val eqset_to_path : hSet -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths

val isapropiscomprelfun :
  hSet -> 'a1 hrel -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun isaprop

val iscomprelfun_funcomp :
  'a1 hrel -> 'a2 hrel -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2)
  iscomprelrelfun -> ('a2, 'a3) iscomprelfun -> ('a1, 'a3) iscomprelfun

val fun_hrel_comp : ('a1 -> 'a2) -> 'a2 hrel -> 'a1 hrel

val setquotunivprop' :
  'a1 eqrel -> ('a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a2) -> 'a1 setquot ->
  'a2

val setquotuniv2prop' :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a1 ->
  'a2) -> 'a1 setquot -> 'a1 setquot -> 'a2

val setquotuniv3prop' :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a2 isaprop) ->
  ('a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
  'a2

val setquotuniv4prop' :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
  'a2 isaprop) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1
  setquot -> 'a1 setquot -> 'a1 setquot -> 'a2

val same_fiber_eqrel : hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet eqrel

val pi0 : hSet

val _UU03c0__UU2080_ : hSet

val component : 'a1 -> pr1hSet

val _UU03c0__UU2080__map : ('a1 -> 'a2) -> pr1hSet -> pr1hSet

val _UU03c0__UU2080__universal_property :
  hSet -> (pr1hSet -> pr1hSet, 'a1 -> pr1hSet) weq

val _UU03c0__UU2080__universal_map :
  hSet -> ('a1 -> pr1hSet) -> pr1hSet -> pr1hSet

val _UU03c0__UU2080__universal_map_eqn :
  hSet -> ('a1 -> pr1hSet) -> 'a1 -> pr1hSet paths

val _UU03c0__UU2080__universal_map_uniq :
  hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet) -> ('a1 -> pr1hSet
  paths) -> (pr1hSet, pr1hSet) homot

val isaprop_eqrel_from_hrel :
  'a1 hrel -> 'a1 -> 'a1 -> ('a1 eqrel -> ('a1 -> 'a1 -> hProptoType ->
  hProptoType) -> hProptoType) isaprop

val eqrel_from_hrel : 'a1 hrel -> 'a1 hrel

val iseqrel_eqrel_from_hrel : 'a1 hrel -> 'a1 iseqrel

val eqrel_impl : 'a1 hrel -> 'a1 -> 'a1 -> hProptoType -> hProptoType

val minimal_eqrel_from_hrel :
  'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1
  -> 'a1 -> hProptoType -> hProptoType

val eqreleq : 'a1 eqrel -> 'a1 -> 'a1 -> 'a1 paths -> hProptoType

val isaprop_isirrefl : 'a1 hrel -> 'a1 isirrefl isaprop

val isaprop_issymm : 'a1 hrel -> 'a1 issymm isaprop

val isaprop_iscotrans : 'a1 hrel -> 'a1 iscotrans isaprop

val univalence_hSet : hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths

val hSet_univalence_map_univalence_hSet :
  hSet -> hSet -> (pr1hSet, pr1hSet) weq -> (__, __) weq paths

val hSet_univalence_univalence_hSet_map :
  hSet -> hSet -> hSet paths -> hSet paths paths

val univalence_hSet_idweq : hSet -> hSet paths paths

val hSet_univalence_map_inv : hSet -> hSet -> hSet paths -> (__, __) weq paths

val univalence_hSet_inv :
  hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths paths
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t



val make_hSet : 'a1 isaset -> hSet

type pr1hSet = __

val eqset : hSet -> pr1hSet -> pr1hSet -> hProp

val neqset : hSet -> pr1hSet -> pr1hSet -> hProp

val setproperty : hSet -> __ isaset

val setdirprod : hSet -> hSet -> hSet

val setcoprod : hSet -> hSet -> hSet

val isaset_total2_hSet :
  hSet -> (pr1hSet -> hSet) -> (pr1hSet, pr1hSet) total2 isaset

val total2_hSet : hSet -> (pr1hSet -> hSet) -> hSet

val hfiber_hSet : hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet -> hSet

val isaset_forall_hSet : ('a1 -> hSet) -> ('a1 -> pr1hSet) isaset

val forall_hSet : ('a1 -> hSet) -> hSet

val unitset : hSet

val dirprod_hSet_subproof : hSet -> hSet -> (pr1hSet, pr1hSet) dirprod isaset

val dirprod_hSet : hSet -> hSet -> hSet

val hPropset : hSet

val hProp_to_hSet : hProp -> hSet

val boolset : hSet

val isaprop_isInjectiveFunction :
  hSet -> hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet -> pr1hSet
  paths -> pr1hSet paths) isaprop

val isInjectiveFunction : hSet -> hSet -> (pr1hSet -> pr1hSet) -> hProp

type 'x ischoicebase_uu1 = __ -> ('x -> hProptoType) -> hProptoType

val isapropischoicebase : 'a1 ischoicebase_uu1 isaprop

val ischoicebase : hProp

val ischoicebaseweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType

val ischoicebaseweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType

val ischoicebaseunit : hProptoType

val ischoicebasecontr : 'a1 iscontr -> hProptoType

val ischoicebaseempty : hProptoType

val ischoicebaseempty2 : 'a1 neg -> hProptoType

val ischoicebasecoprod : hProptoType -> hProptoType -> hProptoType

type 'x hsubtype = 'x -> hProp

val id_hsubtype : 'a1 hsubtype -> 'a1 -> hProp

type 'x carrier = ('x, hProptoType) total2

val make_carrier :
  'a1 hsubtype -> 'a1 -> hProptoType -> ('a1, hProptoType) total2

val pr1carrier : 'a1 hsubtype -> 'a1 carrier -> 'a1

val isaset_carrier_subset :
  hSet -> pr1hSet hsubtype -> (pr1hSet, hProptoType) total2 isaset

val carrier_subset : hSet -> pr1hSet hsubtype -> hSet

val isinclpr1carrier : 'a1 hsubtype -> ('a1 carrier, 'a1) isincl

val isasethsubtype : 'a1 hsubtype isaset

val totalsubtype : 'a1 hsubtype

val weqtotalsubtype : ('a1 carrier, 'a1) weq

val weq_subtypes :
  ('a1, 'a2) weq -> 'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> (hProptoType,
  hProptoType) logeq) -> ('a1 carrier, 'a2 carrier) weq

val subtypesdirprod :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod hsubtype

val fromdsubtypesdirprodcarrier :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod carrier -> ('a1 carrier,
  'a2 carrier) dirprod

val tosubtypesdirprodcarrier :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1 carrier, 'a2 carrier) dirprod -> ('a1,
  'a2) dirprod carrier

val weqsubtypesdirprod :
  'a1 hsubtype -> 'a2 hsubtype -> (('a1, 'a2) dirprod carrier, ('a1 carrier,
  'a2 carrier) dirprod) weq

val ishinhsubtypedirprod :
  'a1 hsubtype -> 'a2 hsubtype -> hProptoType -> hProptoType -> hProptoType

val isapropsubtype :
  'a1 hsubtype -> ('a1 -> 'a1 -> hProptoType -> hProptoType -> 'a1 paths) ->
  'a1 carrier isaprop

val squash_pairs_to_set :
  'a1 isaset -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> hProptoType -> 'a1

val squash_to_set :
  'a2 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2 paths) -> hProptoType ->
  'a2

type 'x hrel = 'x -> 'x -> hProp

val idhrel : 'a1 hrel -> 'a1 -> 'a1 -> hProp

type 'x brel = 'x -> 'x -> bool

val idbrel : 'a1 brel -> 'a1 -> 'a1 -> bool

type 'x istrans = 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

type 'x isrefl = 'x -> hProptoType

type 'x issymm = 'x -> 'x -> hProptoType -> hProptoType

type 'x ispreorder = ('x istrans, 'x isrefl) dirprod

type 'x iseqrel = ('x ispreorder, 'x issymm) dirprod

val iseqrelconstr :
  'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 iseqrel

type 'x isirrefl = 'x -> hProptoType neg

type 'x isasymm = 'x -> 'x -> hProptoType -> hProptoType -> empty

type 'x iscoasymm = 'x -> 'x -> hProptoType neg -> hProptoType

type 'x istotal = 'x -> 'x -> hProptoType

type 'x isdectotal = 'x -> 'x -> (hProptoType, hProptoType) coprod

type 'x iscotrans = 'x -> 'x -> 'x -> hProptoType -> hProptoType

type 'x isdeccotrans =
  'x -> 'x -> 'x -> hProptoType -> (hProptoType, hProptoType) coprod

type 'x isdecrel = 'x -> 'x -> (hProptoType, hProptoType neg) coprod

type 'x isnegrel = 'x -> 'x -> hProptoType neg neg -> hProptoType

type 'x isantisymm = 'x -> 'x -> hProptoType -> hProptoType -> 'x paths

type 'x isPartialOrder = ('x ispreorder, 'x isantisymm) dirprod

type 'x isantisymmneg =
  'x -> 'x -> hProptoType neg -> hProptoType neg -> 'x paths

type 'x iscoantisymm =
  'x -> 'x -> hProptoType neg -> (hProptoType, 'x paths) coprod

type 'x neqchoice =
  'x -> 'x -> 'x paths neg -> (hProptoType, hProptoType) coprod

val isaprop_istrans : hSet -> pr1hSet hrel -> pr1hSet istrans isaprop

val isaprop_isrefl : hSet -> pr1hSet hrel -> pr1hSet isrefl isaprop

val isaprop_istotal : hSet -> pr1hSet hrel -> pr1hSet istotal isaprop

val isaprop_isantisymm : hSet -> pr1hSet hrel -> pr1hSet isantisymm isaprop

val isaprop_ispreorder : hSet -> pr1hSet hrel -> pr1hSet ispreorder isaprop

val isaprop_isPartialOrder :
  hSet -> pr1hSet hrel -> pr1hSet isPartialOrder isaprop

val isaset_hrel : hSet -> pr1hSet hrel isaset

val istransandirrefltoasymm :
  'a1 hrel -> 'a1 istrans -> 'a1 isirrefl -> 'a1 isasymm

val istotaltoiscoasymm : 'a1 hrel -> 'a1 istotal -> 'a1 iscoasymm

val isdecreltoisnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isnegrel

val isantisymmnegtoiscoantisymm :
  'a1 hrel -> 'a1 isdecrel -> 'a1 isantisymmneg -> 'a1 iscoantisymm

val rtoneq :
  'a1 hrel -> 'a1 isirrefl -> 'a1 -> 'a1 -> hProptoType -> 'a1 paths neg

type 'x hrellogeq = 'x -> 'x -> (hProptoType, hProptoType) logeq

val istranslogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 istrans -> 'a1 istrans

val isrefllogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isrefl -> 'a1 isrefl

val issymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 issymm -> 'a1 issymm

val ispologeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 ispreorder -> 'a1 ispreorder

val iseqrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iseqrel -> 'a1 iseqrel

val isirrefllogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isirrefl -> 'a1 isirrefl

val isasymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isasymm -> 'a1 isasymm

val iscoasymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscoasymm -> 'a1 iscoasymm

val istotallogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 istotal -> 'a1 istotal

val iscotranslogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscotrans -> 'a1 iscotrans

val isdecrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isdecrel -> 'a1 isdecrel

val isnegrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isnegrel -> 'a1 isnegrel

val isantisymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isantisymm -> 'a1 isantisymm

val isantisymmneglogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isantisymmneg -> 'a1 isantisymmneg

val iscoantisymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscoantisymm -> 'a1 iscoantisymm

val neqchoicelogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 neqchoice -> 'a1 neqchoice

type 'x po = ('x hrel, 'x ispreorder) total2

val make_po : 'a1 hrel -> 'a1 ispreorder -> 'a1 po

val carrierofpo : 'a1 po -> 'a1 -> 'a1 -> hProp

type coq_PreorderedSet = (hSet, pr1hSet po) total2

val coq_PreorderedSetPair : hSet -> pr1hSet po -> coq_PreorderedSet

val carrierofPreorderedSet : coq_PreorderedSet -> hSet

val coq_PreorderedSetRelation : coq_PreorderedSet -> pr1hSet hrel

type coq_PartialOrder = (pr1hSet hrel, pr1hSet isPartialOrder) total2

val make_PartialOrder :
  hSet -> pr1hSet hrel -> pr1hSet isPartialOrder -> coq_PartialOrder

val carrierofPartialOrder : hSet -> coq_PartialOrder -> pr1hSet hrel

type coq_Poset = (hSet, coq_PartialOrder) total2

val make_Poset : hSet -> coq_PartialOrder -> coq_Poset

val carrierofposet : coq_Poset -> hSet

val posetRelation : coq_Poset -> pr1hSet hrel

val isrefl_posetRelation : coq_Poset -> pr1hSet isrefl

val istrans_posetRelation : coq_Poset -> pr1hSet istrans

val isantisymm_posetRelation : coq_Poset -> pr1hSet isantisymm

type isaposetmorphism = pr1hSet -> pr1hSet -> hProptoType -> hProptoType

type posetmorphism = (pr1hSet -> pr1hSet, isaposetmorphism) total2

val make_posetmorphism :
  coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism ->
  (pr1hSet -> pr1hSet, isaposetmorphism) total2

val carrierofposetmorphism :
  coq_Poset -> coq_Poset -> posetmorphism -> pr1hSet -> pr1hSet

type isdec_ordering = pr1hSet -> pr1hSet -> hProptoType decidable

val isaprop_isaposetmorphism :
  coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism isaprop

val isaset_po : hSet -> pr1hSet po isaset

val isaset_PartialOrder : hSet -> coq_PartialOrder isaset

type isPosetEquivalence = (isaposetmorphism, isaposetmorphism) dirprod

val isaprop_isPosetEquivalence :
  coq_Poset -> coq_Poset -> (pr1hSet, pr1hSet) weq -> isPosetEquivalence
  isaprop

val isPosetEquivalence_idweq : coq_Poset -> isPosetEquivalence

type coq_PosetEquivalence =
  ((pr1hSet, pr1hSet) weq, isPosetEquivalence) total2

val posetUnderlyingEquivalence :
  coq_Poset -> coq_Poset -> coq_PosetEquivalence -> (pr1hSet, pr1hSet) weq

val identityPosetEquivalence : coq_Poset -> coq_PosetEquivalence

val isincl_pr1_PosetEquivalence :
  coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
  isincl

val isinj_pr1_PosetEquivalence :
  coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
  isInjective

type isMinimal = pr1hSet -> hProptoType

type isMaximal = pr1hSet -> hProptoType

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> ((hProptoType,
  pr1hSet paths neg) dirprod, (hProptoType, pr1hSet paths neg) dirprod)
  dirprod neg) dirprod

val isaprop_isMinimal : coq_Poset -> pr1hSet -> isMaximal isaprop

val isaprop_isMaximal : coq_Poset -> pr1hSet -> isMaximal isaprop

val isaprop_consecutive :
  coq_Poset -> pr1hSet -> pr1hSet -> consecutive isaprop

type 'x eqrel = ('x hrel, 'x iseqrel) total2

val make_eqrel : 'a1 hrel -> 'a1 iseqrel -> 'a1 eqrel

val eqrelconstr :
  'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 eqrel

val pr1eqrel : 'a1 eqrel -> 'a1 -> 'a1 -> hProp

val eqreltrans : 'a1 eqrel -> 'a1 istrans

val eqrelrefl : 'a1 eqrel -> 'a1 isrefl

val eqrelsymm : 'a1 eqrel -> 'a1 issymm

val hreldirprod : 'a1 hrel -> 'a2 hrel -> ('a1, 'a2) dirprod hrel

val istransdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 istrans -> 'a2 istrans -> ('a1, 'a2) dirprod
  istrans

val isrefldirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 isrefl -> 'a2 isrefl -> ('a1, 'a2) dirprod
  isrefl

val issymmdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 issymm -> 'a2 issymm -> ('a1, 'a2) dirprod
  issymm

val eqreldirprod : 'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod eqrel

val negrel : 'a1 hrel -> 'a1 hrel

val istransnegrel : 'a1 hrel -> 'a1 iscotrans -> 'a1 istrans

val isasymmnegrel : 'a1 hrel -> 'a1 iscoasymm -> 'a1 isasymm

val iscoasymmgenrel : 'a1 hrel -> 'a1 isasymm -> 'a1 iscoasymm

val isdecnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isdecrel

val isnegnegrel : 'a1 hrel -> 'a1 isnegrel

val isantisymmnegrel : 'a1 hrel -> 'a1 isantisymmneg -> 'a1 isantisymm

val eqh : 'a1 isdeceq -> 'a1 hrel

val neqh : 'a1 isdeceq -> 'a1 hrel

val isrefleqh : 'a1 isdeceq -> 'a1 isrefl

val weqeqh : 'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths, hProptoType) weq

val weqneqh : 'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths neg, hProptoType) weq

type 'x decrel = ('x hrel, 'x isdecrel) total2

val pr1decrel : 'a1 decrel -> 'a1 hrel

val make_decrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 decrel

val decreltobrel : 'a1 decrel -> 'a1 brel

val breltodecrel : 'a1 brel -> 'a1 decrel

val pathstor : 'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType

val rtopaths : 'a1 decrel -> 'a1 -> 'a1 -> hProptoType -> bool paths

val pathstonegr : 'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType neg

val negrtopaths : 'a1 decrel -> 'a1 -> 'a1 -> hProptoType neg -> bool paths

val ctlong :
  'a1 hrel -> 'a1 isdecrel -> 'a1 -> 'a1 -> bool paths -> hProptoType

val deceq_to_decrel : 'a1 isdeceq -> 'a1 decrel

val confirm_equal : 'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths

val confirm_not_equal :
  'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths neg

val resrel : 'a1 hrel -> 'a1 hsubtype -> 'a1 carrier hrel

val istransresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 istrans -> 'a1 carrier istrans

val isreflresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isrefl -> 'a1 carrier isrefl

val issymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 issymm -> 'a1 carrier issymm

val isporesrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 ispreorder -> 'a1 carrier ispreorder

val iseqrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqrel -> 'a1 carrier iseqrel

val isirreflresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isirrefl -> 'a1 carrier isirrefl

val isasymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isasymm -> 'a1 carrier isasymm

val iscoasymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscoasymm -> 'a1 carrier iscoasymm

val istotalresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 istotal -> 'a1 carrier istotal

val iscotransresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscotrans -> 'a1 carrier iscotrans

val isdecrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isdecrel -> 'a1 carrier isdecrel

val isnegrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isnegrel -> 'a1 carrier isnegrel

val isantisymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymm -> 'a1 carrier isantisymm

val isantisymmnegresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymmneg -> 'a1 carrier isantisymmneg

val iscoantisymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscoantisymm -> 'a1 carrier iscoantisymm

val neqchoiceresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 neqchoice -> 'a1 carrier neqchoice

type 'x iseqclass =
  (hProptoType, ('x -> 'x -> hProptoType -> hProptoType -> hProptoType, 'x ->
  'x -> hProptoType -> hProptoType -> hProptoType) dirprod) dirprod

val iseqclassconstr :
  'a1 hrel -> 'a1 hsubtype -> hProptoType -> ('a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> hProptoType -> hProptoType ->
  hProptoType) -> 'a1 iseqclass

val eqax0 : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> hProptoType

val eqax1 :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType

val eqax2 :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType

val isapropiseqclass : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass isaprop

val iseqclassdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 hsubtype -> 'a2 hsubtype -> 'a1 iseqclass ->
  'a2 iseqclass -> ('a1, 'a2) dirprod iseqclass

val surjectionisepitosets :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective ->
  'a3 isaset -> ('a1 -> 'a3 paths) -> 'a2 -> 'a3 paths

val isaset_set_fun_space : hSet -> ('a1 -> pr1hSet) isaset

val epiissurjectiontosets :
  ('a1 -> 'a2) -> 'a2 isaset -> (hSet -> ('a2 -> pr1hSet) -> ('a2 -> pr1hSet)
  -> ('a1 -> pr1hSet paths) -> 'a2 -> pr1hSet paths) -> ('a1, 'a2)
  issurjective

val surjective_iscontr_im :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> (('a1, 'a2) hfiber, 'a3)
  image iscontr

val univ_surj :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> 'a3

val univ_surj_ax :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a1 -> 'a3 paths

val univ_surj_unique :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> ('a2 -> 'a3) -> ('a1 -> 'a3 paths)
  -> 'a2 -> 'a3 paths

type 'x setquot = ('x hsubtype, 'x iseqclass) total2

val make_setquot : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 setquot

val pr1setquot : 'a1 hrel -> 'a1 setquot -> 'a1 hsubtype

val isinclpr1setquot : 'a1 hrel -> ('a1 setquot, 'a1 hsubtype) isincl

val isasetsetquot : 'a1 hrel -> 'a1 setquot isaset

val setquotinset : 'a1 hrel -> hSet

val setquotpr : 'a1 eqrel -> 'a1 -> 'a1 setquot

val setquotl0 : 'a1 eqrel -> 'a1 setquot -> 'a1 carrier -> 'a1 setquot paths

val issurjsetquotpr : 'a1 eqrel -> ('a1, 'a1 setquot) issurjective

val iscompsetquotpr :
  'a1 eqrel -> 'a1 -> 'a1 -> hProptoType -> 'a1 setquot paths

type ('x, 'y) iscomprelfun = 'x -> 'x -> hProptoType -> 'y paths

val iscomprelfunlogeqf :
  'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) -> ('a1, 'a2)
  iscomprelfun -> ('a1, 'a2) iscomprelfun

val isapropimeqclass :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot -> ('a1 carrier, pr1hSet) image isaprop

val setquotuniv :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot -> pr1hSet

val setquotunivcomm :
  'a1 eqrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  -> pr1hSet paths

val weqpathsinsetquot :
  'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot paths) weq

type ('x, 'y) iscomprelrelfun = 'x -> 'x -> hProptoType -> hProptoType

val iscomprelfunlogeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) -> ('a1,
  'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun

val iscomprelfunlogeqf2 :
  'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a2) -> ('a1,
  'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun

val setquotfun :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun -> 'a1
  setquot -> 'a2 setquot

val setquotfuncomm :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun -> 'a1
  -> 'a2 setquot paths

val setquotunivprop :
  'a1 eqrel -> ('a1 setquot -> hProp) -> ('a1 -> __) -> 'a1 setquot -> __

val setquotuniv2prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> hProp) -> ('a1 -> 'a1 ->
  hProptoType) -> 'a1 setquot -> 'a1 setquot -> hProptoType

val setquotuniv3prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> hProp) -> ('a1
  -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot
  -> hProptoType

val setquotuniv4prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
  hProp) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1
  setquot -> 'a1 setquot -> 'a1 setquot -> hProptoType

val issurjsetquotfun :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> ('a1,
  'a2) iscomprelrelfun -> ('a1 setquot, 'a2 setquot) issurjective

val isinclsetquotfun :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
  isincl

val setquotincl :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
  incl

val weqsetquotweq :
  'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) weq -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot) weq

val weqsetquotsurj :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> ('a1,
  'a2) iscomprelrelfun -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1
  setquot, 'a2 setquot) weq

val setquottodirprod :
  'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod setquot -> ('a1 setquot, 'a2
  setquot) dirprod

val dirprodtosetquot :
  'a1 hrel -> 'a2 hrel -> ('a1 setquot, 'a2 setquot) dirprod -> ('a1, 'a2)
  dirprod setquot

val weqsetquottodirprod :
  'a1 eqrel -> 'a2 eqrel -> (('a1, 'a2) dirprod setquot, ('a1 setquot, 'a2
  setquot) dirprod) weq

type ('x, 'y) iscomprelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> 'y paths

val iscomprelfun2if :
  'a1 hrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 -> hProptoType -> 'a2
  paths) -> ('a1 -> 'a1 -> 'a1 -> hProptoType -> 'a2 paths) -> ('a1, 'a2)
  iscomprelfun2

val iscomprelfun2logeqf :
  'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
  iscomprelfun2 -> ('a1, 'a2) iscomprelfun2

val setquotuniv2_iscomprelfun :
  'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun2
  -> 'a1 setquot -> 'a1 setquot -> (('a1, 'a1) dirprod, pr1hSet) iscomprelfun

val setquotuniv2 :
  'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun2
  -> 'a1 setquot -> 'a1 setquot -> pr1hSet

val setquotuniv2comm :
  'a1 eqrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet)
  iscomprelfun2 -> 'a1 -> 'a1 -> pr1hSet paths

type ('x, 'y) iscomprelrelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

val iscomprelrelfun2if :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType) -> ('a1, 'a2) iscomprelrelfun2

val iscomprelrelfun2logeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2) ->
  ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2

val iscomprelrelfun2logeqf2 :
  'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a1 -> 'a2) ->
  ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2

val setquotfun2_iscomprelfun2 :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun2
  -> 'a1 setquot -> 'a1 setquot -> ('a1, 'a2 setquot) iscomprelfun2

val setquotfun2 :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun2
  -> 'a1 setquot -> 'a1 setquot -> 'a2 setquot

val setquotfun2comm :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
  iscomprelrelfun2 -> 'a1 -> 'a1 -> 'a2 setquot paths

val isdeceqsetquot_non_constr :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq

val setquotbooleqint :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 -> 'a1 -> bool

val setquotbooleqintcomp :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> ('a1, bool)
  iscomprelfun2

val setquotbooleq :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> bool

val setquotbooleqtopaths :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> bool paths -> 'a1 setquot paths

val setquotpathstobooleq :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> 'a1 setquot paths -> bool paths

val isdeceqsetquot :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq

type 'x iscomprelrel = ('x, hProp) iscomprelfun2

val iscomprelrelif :
  'a1 hrel -> 'a1 hrel -> 'a1 issymm -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> 'a1 iscomprelrel

val iscomprelrellogeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
  'a1 iscomprelrel

val iscomprelrellogeqf2 :
  'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
  'a1 iscomprelrel

val quotrel : 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 setquot hrel

val istransquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istrans -> 'a1 setquot
  istrans

val issymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 issymm -> 'a1 setquot
  issymm

val isreflquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isrefl -> 'a1 setquot
  isrefl

val ispoquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 ispreorder -> 'a1 setquot
  ispreorder

val iseqrelquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iseqrel -> 'a1 setquot
  iseqrel

val isirreflquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isirrefl -> 'a1 setquot
  isirrefl

val isasymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isasymm -> 'a1 setquot
  isasymm

val iscoasymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscoasymm -> 'a1 setquot
  iscoasymm

val istotalquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istotal -> 'a1 setquot
  istotal

val iscotransquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscotrans -> 'a1 setquot
  iscotrans

val isantisymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymm -> 'a1 setquot
  isantisymm

val isantisymmnegquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymmneg -> 'a1
  setquot isantisymmneg

val quotrelimpl :
  'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
  -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1 setquot -> 'a1 setquot
  -> hProptoType -> hProptoType

val quotrellogeq :
  'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
  -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) -> 'a1 setquot -> 'a1
  setquot -> (hProptoType, hProptoType) logeq

val quotdecrelint :
  'a1 hrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot brel

val quotdecrelintlogeq :
  'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot -> 'a1 setquot
  -> (hProptoType, hProptoType) logeq

val isdecquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isdecrel -> 'a1 setquot
  isdecrel

val decquotrel :
  'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot decrel

val reseqrel : 'a1 eqrel -> 'a1 hsubtype -> 'a1 carrier eqrel

val iseqclassresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 iseqclass -> ('a1 ->
  hProptoType -> hProptoType) -> 'a1 carrier iseqclass

val fromsubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 setquot carrier -> 'a1 carrier
  setquot

val tosubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 carrier setquot -> 'a1 setquot
  carrier

val weqsubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> ('a1 setquot carrier, 'a1 carrier
  setquot) weq

val pathshrel : 'a1 -> 'a1 -> hProp

val istranspathshrel : 'a1 istrans

val isreflpathshrel : 'a1 isrefl

val issymmpathshrel : 'a1 issymm

val pathseqrel : 'a1 eqrel

type 'x pi0 = 'x setquot

val pi0pr : 'a1 -> 'a1 setquot

type ('x, 's) compfun = ('x -> 's, ('x, 's) iscomprelfun) total2

val make_compfun :
  'a1 hrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelfun -> ('a1, 'a2) compfun

val pr1compfun : 'a1 hrel -> ('a1, 'a2) compfun -> 'a1 -> 'a2

val compevmapset :
  'a1 hrel -> 'a1 -> hSet -> ('a1, pr1hSet) compfun -> pr1hSet

val compfuncomp :
  'a1 hrel -> ('a1, 'a2) compfun -> ('a2 -> 'a3) -> ('a1, 'a3) compfun

type 'x setquot2 = ('x, hSet -> ('x, pr1hSet) compfun -> pr1hSet) image

val isasetsetquot2 : 'a1 hrel -> 'a1 setquot2 isaset

val setquot2inset : 'a1 hrel -> hSet

val setquot2pr : 'a1 hrel -> 'a1 -> 'a1 setquot2

val issurjsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) issurjective

val iscompsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) iscomprelfun

val setquot2univ :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot2 -> pr1hSet

val setquot2univcomm :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  -> pr1hSet paths

val weqpathssetquot2l1 : 'a1 eqrel -> 'a1 -> ('a1, hProp) iscomprelfun

val weqpathsinsetquot2 :
  'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot2 paths) weq

val setquottosetquot2 : 'a1 hrel -> 'a1 iseqrel -> 'a1 setquot -> 'a1 setquot2

val hSet_univalence_map : hSet -> hSet -> hSet paths -> (__, __) weq

val hSet_univalence : hSet -> hSet -> (hSet paths, (pr1hSet, pr1hSet) weq) weq

val hSet_rect :
  hSet -> hSet -> (hSet paths -> 'a1) -> (pr1hSet, pr1hSet) weq -> 'a1
open DecidablePropositions
open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type stn = (nat, hProptoType) total2

val make_stn : nat -> nat -> hProptoType -> stn

val stntonat : nat -> stn -> nat

val stnlt : nat -> stn -> hProptoType

val stn_eq : nat -> stn -> stn -> nat paths -> stn paths

val isinclstntonat : nat -> (stn, nat) isincl

val stntonat_incl : nat -> (stn, nat) incl

val isdecinclstntonat : nat -> (stn, nat) isdecincl

val neghfiberstntonat : nat -> nat -> hProptoType -> (stn, nat) hfiber neg

val iscontrhfiberstntonat :
  nat -> nat -> hProptoType -> (stn, nat) hfiber iscontr

val stn_ne_iff_neq : nat -> stn -> stn -> (stn paths neg, hProptoType) logeq

val stnneq : nat -> stn neqReln

val isisolatedinstn : nat -> stn -> stn isisolated

val stnneq_iff_nopath :
  nat -> stn -> stn -> (stn paths neg, hProptoType) logeq

val stnneq_to_nopath : nat -> stn -> stn -> hProptoType -> stn paths neg

val isdeceqstn : nat -> stn isdeceq

val stn_eq_or_neq : nat -> stn -> stn -> (stn paths, hProptoType) coprod

val weqisolatedstntostn : nat -> (stn isolated, stn) weq

val isasetstn : nat -> stn isaset

val stnset : nat -> hSet

val stn_to_nat : nat -> pr1hSet -> pr1hSet

val stnposet : nat -> coq_Poset

val lastelement : nat -> stn

val lastelement_ge : nat -> stn -> hProptoType

val firstelement : nat -> stn

val firstelement_le : nat -> stn -> hProptoType

val firstValue : nat -> (stn -> 'a1) -> 'a1

val lastValue : nat -> (stn -> 'a1) -> 'a1

val dualelement_0_empty : nat -> stn -> nat paths -> empty

val dualelement_lt : nat -> nat -> hProptoType -> hProptoType

val dualelement : nat -> stn -> stn

val stnmtostnn : nat -> nat -> hProptoType -> stn -> stn

val stn_left : nat -> nat -> stn -> stn

val stn_right : nat -> nat -> stn -> stn

val stn_left_compute : nat -> nat -> stn -> nat paths

val stn_right_compute : nat -> nat -> stn -> nat paths

val stn_left_0 : nat -> stn -> nat paths -> stn paths

val stn_left' : nat -> nat -> hProptoType -> stn -> stn

val stn_left'' : nat -> nat -> hProptoType -> stn -> stn

val stn_left_compare : nat -> nat -> hProptoType -> (stn -> stn) paths

val dni : nat -> stn -> stn -> stn

val compute_pr1_dni_last : nat -> stn -> nat paths

val compute_pr1_dni_first : nat -> stn -> nat paths

val dni_last : nat -> stn -> nat paths

val dni_first : nat -> stn -> nat paths

val dni_firstelement : nat -> stn -> stn

val replace_dni_first : nat -> (stn -> stn) paths

val dni_lastelement : nat -> stn -> stn

val replace_dni_last : nat -> (stn -> stn) paths

val dni_lastelement_ord : nat -> stn -> stn -> hProptoType -> hProptoType

val pr1_dni_lastelement : nat -> stn -> nat paths

val dni_last_lt : nat -> stn -> hProptoType

val dnicommsq : nat -> stn -> (nat, stn, nat, stn) commsqstr

val dnihfsq : nat -> stn -> (nat, stn, nat, stn) hfsqstr

val dni_neq_i : nat -> stn -> stn -> hProptoType

val weqhfiberdnihfiberdi :
  nat -> stn -> stn -> ((stn, stn) hfiber, (nat, nat) hfiber) weq

val neghfiberdni : nat -> stn -> (stn, stn) hfiber neg

val iscontrhfiberdni :
  nat -> stn -> stn -> hProptoType -> (stn, stn) hfiber iscontr

val isdecincldni : nat -> stn -> (stn, stn) isdecincl

val isincldni : nat -> stn -> (stn, stn) isincl

val sni : nat -> stn -> stn -> stn

type stn_compl = stn compl_ne

val dnitocompl : nat -> stn -> stn -> stn_compl

val isweqdnitocompl : nat -> stn -> (stn, stn_compl) isweq

val weqdnicompl : nat -> stn -> (stn, stn_compl) weq

val weqdnicompl_compute : nat -> stn -> stn -> stn paths

val weqdnicoprod_provisional : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqdnicoprod_map : nat -> stn -> (stn, coq_unit) coprod -> stn

val weqdnicoprod_compute : nat -> stn -> ((stn, coq_unit) coprod, stn) homot

val weqdnicoprod : nat -> stn -> ((stn, coq_unit) coprod, stn) weq

val weqoverdnicoprod :
  nat -> ((stn, 'a1) total2, ((stn, 'a1) total2, 'a1) coprod) weq

val weqoverdnicoprod_eq1 : nat -> stn -> 'a1 -> (stn, 'a1) total2 paths

val weqoverdnicoprod_eq1' :
  nat -> (stn, 'a1) total2 -> (stn, 'a1) total2 paths

val weqoverdnicoprod_eq2 : nat -> 'a1 -> (stn, 'a1) total2 paths

val weqdnicoprod_invmap : nat -> stn -> stn -> (stn, coq_unit) coprod

val negstn0 : stn neg

val weqstn0toempty : (stn, empty) weq

val weqstn1tounit : (stn, coq_unit) weq

val iscontrstn1 : stn iscontr

val isconnectedstn1 : stn -> stn -> stn paths

val isinclfromstn1 : (stn -> 'a1) -> 'a1 isaset -> (stn, 'a1) isincl

val weqstn2tobool : (stn, bool) weq

val isinjstntonat : nat -> hProptoType

val weqfromcoprodofstn_invmap : nat -> nat -> stn -> (stn, stn) coprod

val weqfromcoprodofstn_invmap_r0 : nat -> stn -> (stn, stn) coprod paths

val weqfromcoprodofstn_map : nat -> nat -> (stn, stn) coprod -> stn

val weqfromcoprodofstn_eq1 :
  nat -> nat -> (stn, stn) coprod -> (stn, stn) coprod paths

val weqfromcoprodofstn_eq2 : nat -> nat -> stn -> stn paths

val weqfromcoprodofstn : nat -> nat -> ((stn, stn) coprod, stn) weq

val pr1_eqweqmap_stn : nat -> nat -> nat paths -> stn -> nat paths

val coprod_stn_assoc :
  nat -> nat -> nat -> (((stn, stn) coprod, stn) coprod, stn) homot

val stnsum : nat -> (stn -> nat) -> nat

val stnsum_step : nat -> (stn -> nat) -> nat paths

val stnsum_eq :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths

val transport_stnsum : nat -> nat -> nat paths -> (stn -> nat) -> nat paths

val stnsum_le :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val transport_stn : nat -> nat -> nat paths -> stn -> stn paths

val stnsum_left_right : nat -> nat -> (stn -> nat) -> nat paths

val stnsum_left_le : nat -> nat -> (stn -> nat) -> hProptoType

val stnsum_left_le' : nat -> nat -> (stn -> nat) -> hProptoType -> hProptoType

val stnsum_dni : nat -> (stn -> nat) -> stn -> nat paths

val stnsum_pos : nat -> (stn -> nat) -> stn -> hProptoType

val stnsum_pos_0 : nat -> (stn -> nat) -> hProptoType

val stnsum_1 : nat -> nat paths

val stnsum_const : nat -> nat -> nat paths

val stnsum_last_le : nat -> (stn -> nat) -> hProptoType

val stnsum_first_le : nat -> (stn -> nat) -> hProptoType

val _c_ : nat -> (stn -> nat) -> (stn, stn) total2 -> hProptoType

val weqstnsum_map : nat -> (stn -> nat) -> (stn, stn) total2 -> stn

val weqstnsum_invmap : nat -> (stn -> nat) -> stn -> (stn, stn) total2

val weqstnsum_invmap_step1 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val weqstnsum_invmap_step2 :
  nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths

val partial_sum_prop_aux :
  nat -> (stn -> nat) -> stn -> stn -> stn -> stn -> hProptoType ->
  hProptoType

val partial_sum_prop :
  nat -> (stn -> nat) -> nat -> (stn, (stn, nat paths) total2) total2 isaprop

val partial_sum_slot_subproof :
  nat -> (stn -> nat) -> nat -> stn -> stn -> nat paths -> nat paths

val partial_sum_slot :
  nat -> (stn -> nat) -> nat -> hProptoType -> (stn, (stn, nat paths) total2)
  total2 iscontr

val stn_right_first : nat -> nat -> stn paths

val nat_rect_step : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 paths

val weqstnsum1_prelim : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_step :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq paths

val weqstnsum1_prelim_eq :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) homot

val weqstnsum1_prelim_eq' :
  nat -> (stn -> nat) -> (stn, (stn, stn) total2) homot

val weqstnsum1 : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val weqstnsum1_eq : nat -> (stn -> nat) -> ((stn, stn) total2 -> stn) paths

val weqstnsum1_eq' : nat -> (stn -> nat) -> (stn -> (stn, stn) total2) paths

val weqstnsum :
  nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> ((stn, 'a1) total2, stn)
  weq

val weqstnsum2 :
  nat -> (stn -> nat) -> ('a1 -> stn) -> (stn -> (stn, ('a1, stn) hfiber)
  weq) -> ('a1, stn) weq

val lexicalEnumeration : nat -> (stn -> nat) -> (stn, (stn, stn) total2) weq

val inverse_lexicalEnumeration :
  nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq

val foldleft : 'a1 -> 'a1 binop -> nat -> (stn -> 'a1) -> 'a1

val foldright : 'a1 binop -> 'a1 -> nat -> (stn -> 'a1) -> 'a1

val weqfromprodofstn : nat -> nat -> ((stn, stn) dirprod, stn) weq

val weqfromdecsubsetofstn :
  nat -> (stn -> bool) -> (nat, ((stn, bool) hfiber, stn) weq) total2

val weqfromhfiberfromstn :
  nat -> 'a1 -> 'a1 isisolated -> (stn -> 'a1) -> (nat, ((stn, 'a1) hfiber,
  stn) weq) total2

val weqfromfunstntostn : nat -> nat -> (stn -> stn, stn) weq

val stnprod : nat -> (stn -> nat) -> nat

val stnprod_step : nat -> (stn -> nat) -> nat paths

val stnprod_eq :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths

val weqstnprod :
  nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> (stn -> 'a1, stn) weq

val weqweqstnsn : nat -> ((stn, stn) weq, (stn, (stn, stn) weq) dirprod) weq

val weqfromweqstntostn : nat -> ((stn, stn) weq, stn) weq

val ischoicebasestn : nat -> hProptoType

val negweqstnsn0 : nat -> (stn, stn) weq neg

val negweqstn0sn : nat -> (stn, stn) weq neg

val weqcutforstn : nat -> nat -> (stn, stn) weq -> (stn, stn) weq

val weqtoeqstn : nat -> nat -> (stn, stn) weq -> nat paths

val eqtoweqstn_subproof : nat -> nat -> nat paths -> stn -> hProptoType

val eqtoweqstn_subproof0 : nat -> nat -> nat paths -> stn -> hProptoType

val eqtoweqstn_subproof1 : nat -> nat -> nat paths -> stn -> stn paths

val eqtoweqstn_subproof2 : nat -> nat -> nat paths -> stn -> stn paths

val eqtoweqstn : nat -> nat -> nat paths -> (stn, stn) weq

val stnsdnegweqtoeq : nat -> nat -> (stn, stn) weq dneg -> nat paths

val weqforallnatlehn0 :
  (nat -> hProp) -> (nat -> hProptoType -> hProptoType, hProptoType) weq

val weqforallnatlehnsn' :
  nat -> (nat -> hProp) -> (nat -> hProptoType -> hProptoType, (nat ->
  hProptoType -> hProptoType, hProptoType) dirprod) weq

val weqexistsnatlehn0 : (nat -> hProp) -> (hProptoType, hProptoType) weq

val weqexistsnatlehnsn' :
  nat -> (nat -> hProp) -> (hProptoType, hProptoType) weq

val isdecbexists : nat -> (nat -> 'a1 isdecprop) -> hProptoType isdecprop

val isdecbforall :
  nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) isdecprop

val negbforalldectototal2neg :
  nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) neg -> (nat,
  (hProptoType, 'a1 neg) dirprod) total2

type 'f natdecleast = (nat, ('f, nat -> 'f -> hProptoType) dirprod) total2

val isapropnatdecleast : (nat -> 'a1 isdecprop) -> 'a1 natdecleast isaprop

val accth : (nat -> 'a1 isdecprop) -> hProptoType -> 'a1 natdecleast

val dni_lastelement_is_inj : nat -> stn -> stn -> stn paths -> stn paths

val dni_lastelement_eq : nat -> stn -> hProptoType -> stn paths

val lastelement_eq : nat -> stn -> nat paths -> stn paths

val concatenate' : nat -> nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1

val concatenate'_r0 :
  nat -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1) paths

val concatenate'_r0' : nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1 paths

val flatten' : nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> stn -> 'a1

val stn_predicate : nat -> nat -> hProptoType -> hProptoType -> 'a1 -> 'a1

type two = stn

val two_rec : 'a1 -> 'a1 -> stn -> 'a1

val two_rec_dep : 'a1 -> 'a1 -> two -> 'a1

type three = stn

val three_rec : 'a1 -> 'a1 -> 'a1 -> stn -> 'a1

val three_rec_dep : 'a1 -> 'a1 -> 'a1 -> three -> 'a1

type is_stn_increasing = stn -> stn -> hProptoType -> hProptoType

type is_stn_strictly_increasing = stn -> stn -> hProptoType -> hProptoType

val is_strincr_impl_incr :
  nat -> (stn -> nat) -> is_stn_strictly_increasing -> is_stn_increasing

val is_incr_impl_strincr :
  nat -> (stn -> nat) -> (stn, nat) isincl -> is_stn_increasing ->
  is_stn_strictly_increasing

val stnsum_ge1 : nat -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val stnsum_add : nat -> (stn -> nat) -> (stn -> nat) -> nat paths

val stnsum_lt :
  nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType

val stnsum_diffs : nat -> (stn -> nat) -> is_stn_increasing -> nat paths

val stn_ord_incl :
  nat -> (stn -> nat) -> is_stn_strictly_increasing -> hProptoType

val stn_ord_inj :
  nat -> (stn, stn) incl -> (stn -> stn -> hProptoType -> hProptoType) -> stn
  -> stn paths

val stn_ord_bij :
  nat -> (stn, stn) weq -> (stn -> stn -> hProptoType -> hProptoType) -> stn
  -> stn paths
open PartB
open Preamble
open Propositions
open Sets

type coq_Subposet = pr1hSet hsubtype

type coq_Subposet' =
  (coq_Poset, (posetmorphism, (pr1hSet, pr1hSet) isincl) total2) total2

val coq_Subposet'_to_Poset : coq_Poset -> coq_Subposet' -> coq_Poset

val coq_Subposet_to_Subposet' : coq_Poset -> coq_Subposet -> coq_Subposet'

val coq_Subposet'_to_Subposet : coq_Poset -> coq_Subposet' -> coq_Subposet
open Notations
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

val subtype_set : hSet

val subtype_isIn : 'a1 hsubtype -> 'a1 carrier -> 'a1 hsubtype -> hProp

val subtype_containedIn : pr1hSet hrel

val subtype_notContainedIn : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_inc :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> 'a1 carrier -> 'a1 carrier

val subtype_smallerThan : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_equal : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val subtype_notEqual_to_negEqual :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType

val subtype_notEqual_from_negEqual :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val emptysubtype : 'a1 hsubtype

val subtype_difference : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val subtype_difference_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_equal_cond : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_union : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype

val subtype_binaryunion : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val subtype_binaryunion_leq1 : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_binaryunion_leq2 : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_union_containedIn :
  hSet -> ('a1 -> pr1hSet hsubtype) -> 'a1 -> hProptoType

val subtype_intersection : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype

val hsubtype_univalence :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths, hProptoType) weq

val hsubtype_rect :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths -> 'a2, hProptoType ->
  'a2) weq

val subtype_containment_istrans : pr1hSet istrans

val subtype_containment_isrefl : pr1hSet isrefl

val subtype_containment_ispreorder : pr1hSet ispreorder

val subtype_containment_isantisymm : pr1hSet isantisymm

val subtype_containment_isPartialOrder : pr1hSet isPartialOrder

val subtype_inc_comp :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType
  -> 'a1 carrier -> 'a1 carrier paths

val subtype_deceq : 'a1 hsubtype -> 'a1 isdeceq -> 'a1 carrier isdeceq

type 'x isDecidablePredicate = 'x -> hProptoType decidable

val subtype_plus : 'a1 hsubtype -> 'a1 -> 'a1 hsubtype

val subtype_plus_incl : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_has_point : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_in :
  'a1 hsubtype -> 'a1 -> 'a1 hsubtype -> hProptoType -> hProptoType ->
  hProptoType

val subtype_complement : 'a1 hsubtype -> 'a1 hsubtype

val not_in_subtype_and_complement :
  'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType -> empty

val subtype_complement_intersection_empty :
  'a1 hsubtype -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 hsubtype paths) total2
  -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType

val subtype_complement_union :
  'a1 hsubtype -> hProptoType -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 hsubtype
  paths) total2 -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType

val binary_intersection' : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val binary_intersection : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val binary_intersection_commutative :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType

val intersection_contained_l : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val intersection_contained_r : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val intersection_contained :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> hProptoType
  -> hProptoType -> hProptoType

val isaprop_subtype_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType isaprop

val image_hsubtype : 'a1 hsubtype -> ('a1 -> 'a2) -> 'a2 hsubtype

val image_hsubtype_emptyhsubtype : ('a1 -> 'a2) -> 'a2 hsubtype paths

val image_hsubtype_id : 'a1 hsubtype -> 'a1 hsubtype paths

val image_hsubtype_comp :
  'a1 hsubtype -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 hsubtype paths

type ('x, 'y) hsubtype_preserving = hProptoType

val isaprop_hsubtype_preserving :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> 'a2) -> ('a1, 'a2)
  hsubtype_preserving isaprop

val id_hsubtype_preserving : 'a1 hsubtype -> ('a1, 'a1) hsubtype_preserving

val comp_hsubtype_preserving :
  'a1 hsubtype -> 'a2 hsubtype -> 'a3 hsubtype -> ('a1 -> 'a2) -> ('a2 ->
  'a3) -> ('a1, 'a2) hsubtype_preserving -> ('a2, 'a3) hsubtype_preserving ->
  ('a1, 'a3) hsubtype_preserving

val empty_hsubtype_preserving : ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving

val total_hsubtype_preserving : ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving

val singleton : 'a1 -> 'a1 hsubtype

val singleton_point : 'a1 -> 'a1 carrier

val iscontr_singleton : hSet -> pr1hSet -> pr1hSet carrier iscontr

val singleton_is_in : 'a1 hsubtype -> 'a1 carrier -> hProptoType

val coprod_carrier_binary_union :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 carrier, 'a1 carrier) coprod -> 'a1
  carrier

val issurjective_coprod_carrier_binary_union :
  'a1 hsubtype -> 'a1 hsubtype -> (('a1 carrier, 'a1 carrier) coprod, 'a1
  carrier) issurjective
open PartA
open PartB
open Preamble

val post_cat : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths

val pre_cat : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths

val iscontrweqb' : 'a2 iscontr -> ('a1, 'a2) weq -> 'a1 iscontr

val isaprop_goal : 'a1 isaprop -> ('a1 isaprop -> 'a1) -> 'a1
open NaturalNumbers
open PartA
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

val stnweq : nat -> ((stn, coq_unit) coprod, stn) weq

val extend_tuple : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1

val extend_tuple_dep :
  nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> stn -> 'a2

val extend_tuple_dep_const :
  nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> (stn -> 'a2) paths

val extend_tuple_i :
  nat -> (stn -> 'a1) -> 'a1 -> nat -> hProptoType -> hProptoType -> 'a1 paths

val extend_tuple_last :
  nat -> (stn -> 'a1) -> 'a1 -> stn -> nat paths -> 'a1 paths

val extend_tuple_inl : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1 paths

val extend_tuple_inr : nat -> (stn -> 'a1) -> 'a1 -> 'a1 paths

val extend_tuple_eq :
  nat -> 'a1 -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1 paths) -> 'a1
  paths -> (stn -> 'a1) paths
open PartA
open PartB
open PartD
open Preamble
open UnivalenceAxiom

val isaprop_univalenceStatement : univalenceStatement isaprop

val isaprop_funextemptyStatement : funextemptyStatement isaprop

val isaprop_isweqtoforallpathsStatement : isweqtoforallpathsStatement isaprop

val isaprop_propositionalUnivalenceStatement :
  propositionalUnivalenceStatement isaprop

val isaprop_funcontrStatement : funcontrStatement isaprop

val isaprop_funextcontrStatement : funextcontrStatement isaprop
open PartA
open PartB
open Preamble

type __ = Obj.t

val eqweqmap : coq_UU paths -> ('a1, 'a2) weq

val sectohfiber :
  ('a1 -> 'a2) -> ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber

val hfibertosec : ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber -> 'a1 -> 'a2

val sectohfibertosec : ('a1 -> 'a2) -> ('a1 -> 'a2) paths

val isweqtransportf10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val isweqtransportb10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val l1 :
  coq_UU paths -> 'a3 -> (__ -> __ -> (__, __) weq -> 'a3 -> 'a3) -> (__ ->
  'a3 -> 'a3 paths) -> 'a3 paths

type univalenceStatement = __ -> __ -> (coq_UU paths, (__, __) weq) isweq

type funextemptyStatement =
  __ -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

type propositionalUnivalenceStatement =
  __ -> __ -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU
  paths

type funcontrStatement = __ -> __ -> (__ -> __ iscontr) -> (__ -> __) iscontr

type funextcontrStatement =
  __ -> __ -> (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

type isweqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  isweq

type funextsecStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type funextfunStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type weqtopathsStatement = __ -> __ -> (__, __) weq -> coq_UU paths

type weqpathsweqStatement = __ -> __ -> (__, __) weq -> (__, __) weq paths

type weqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  weq

val funextsecImplication :
  isweqtoforallpathsStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot
  -> (__ -> __) paths

val funextfunImplication :
  funextsecStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ ->
  __) paths

val univfromtwoaxioms :
  ((weqtopathsStatement, weqpathsweqStatement) total2, univalenceStatement)
  logeq

val univalenceUAH : univalenceStatement -> (coq_UU paths, ('a1, 'a2) weq) weq

val weqtopathsUAH : univalenceStatement -> (__, __) weq -> coq_UU paths

val weqpathsweqUAH : univalenceStatement -> (__, __) weq -> (__, __) weq paths

val propositionalUnivalenceUAH :
  univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __)
  -> coq_UU paths

val weqtransportbUAH :
  univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
  'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> 'a1 -> 'a1 paths

val isweqweqtransportbUAH :
  univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
  'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> ('a1, 'a1) isweq

val isweqcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val eqcor0UAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2 -> 'a3) ->
  ('a1 -> 'a3) paths -> ('a2 -> 'a3) paths

val apathpr1toprUAH : univalenceStatement -> ('a1 pathsspace -> 'a1) paths

val funextfunPreliminaryUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ ->
  __) paths

val funextemptyUAH :
  univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val isweqlcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq

val isweqrcompwithweqUAH :
  univalenceStatement -> ('a1, 'a2) weq -> ('a3 -> 'a1, 'a3 -> 'a2) isweq

val funcontrUAH :
  univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr

val funextcontrUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
  iscontr

val isweqtoforallpathsUAH :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__,
  __) homot) isweq

val funcontrFromUnivalence :
  univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr

val funextsecweqFromUnivalence :
  univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__,
  __) homot) isweq

val funextemptyFromUnivalence :
  univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val propositionalUnivalenceFromUnivalence :
  univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __)
  -> coq_UU paths

val funextcontrStatementFromUnivalence :
  univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
  iscontr

val univalenceAxiom : (coq_UU paths, (__, __) weq) isweq

val funextemptyAxiom : (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val isweqtoforallpathsAxiom :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq

val funcontrAxiom : (__ -> __ iscontr) -> (__ -> __) iscontr

val propositionalUnivalenceAxiom :
  __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU paths

val funextcontrAxiom : (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

val funextempty : (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

val univalence : (coq_UU paths, ('a1, 'a2) weq) weq

val weqtopaths : (__, __) weq -> coq_UU paths

val weqpathsweq : (__, __) weq -> (__, __) weq paths

val funcontr : (__ -> __ iscontr) -> (__ -> __) iscontr

val funextcontr : (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

val isweqtoforallpaths :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq

val weqtoforallpaths :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) weq

val funextsec : (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

val funextfun : (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

val weqfunextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot, ('a1 -> 'a2) paths) weq

val funcontrtwice : ('a1 -> 'a1 -> 'a2 iscontr) -> ('a1 -> 'a1 -> 'a2) iscontr

val toforallpaths_induction :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1 -> 'a2) paths -> 'a3) -> ('a1 -> 'a2
  paths) -> 'a3

val transportf_funextfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> 'a1 -> 'a3 -> 'a3
  paths

val coq_UU_rect : (coq_UU paths -> 'a3) -> ('a1, 'a2) weq -> 'a3
open PartA
open PartA0
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

val funextsec_toforallpaths :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths
  paths

val toforallpaths_funextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) homot paths

val toforallpaths_funextsec_comp :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot -> ('a1, 'a2) homot) paths

val maponpaths_funextsec :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) homot -> 'a2 paths paths

val weqonsec :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> ('a1 -> 'a3, 'a2 -> 'a4) weq

val weq_transportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) weq

val weq_transportf_comp : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val weqonpaths2 :
  ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1 paths, 'a2 paths) weq

val eqweqmap_ap : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val eqweqmap_ap' : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths

val pr1_eqweqmap : __ paths -> ('a1 -> 'a2) paths

val path_to_fun : __ paths -> 'a1 -> 'a2

val pr1_eqweqmap2 : coq_UU paths -> ('a1 -> 'a2) paths

val weqpath_transport : ('a1, 'a2) weq -> ('a1 -> 'a2) paths

val weqpath_cast : ('a1, 'a2) weq -> ('a1 -> 'a2) paths

val switch_weq : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths

val switch_weq' : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths

val weq_over_sections :
  ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths ->
  (('a2 -> 'a3) -> ('a4, 'a5) weq) -> ((('a2 -> 'a3, 'a4) total2, 'a3)
  hfiber, (('a1 -> 'a3, 'a5) total2, 'a3) hfiber) weq

val maponpaths_app_homot :
  ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3
  paths) -> 'a1 -> 'a2 -> 'a3 paths paths

val path_path_fun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths ->
  ('a1 -> 'a2 paths paths) -> ('a1 -> 'a2) paths paths
open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

type __ = Obj.t

val stn_extens : nat -> stn -> stn -> nat paths -> stn paths

val fromstn0 : stn -> 'a1

type 'a vec = __

val vnil : 'a1 vec

val vcons : nat -> 'a1 -> 'a1 vec -> 'a1 vec

val drop : nat -> (stn -> 'a1) -> stn -> 'a1

val make_vec : nat -> (stn -> 'a1) -> 'a1 vec

val hd : nat -> 'a1 vec -> 'a1

val tl : nat -> 'a1 vec -> 'a1 vec

val el : nat -> 'a1 vec -> stn -> 'a1

val el_make_vec : nat -> (stn -> 'a1) -> (stn, 'a1) homot

val el_make_vec_fun : nat -> (stn -> 'a1) -> (stn -> 'a1) paths

val el_vcons_tl : nat -> 'a1 vec -> 'a1 -> stn -> 'a1 paths

val el_vcons_hd : nat -> 'a1 vec -> 'a1 -> 'a1 paths

val drop_el : nat -> 'a1 vec -> stn -> 'a1 paths

val el_tl : nat -> 'a1 vec -> stn -> 'a1 paths

val vec0_eq : 'a1 vec -> 'a1 vec -> 'a1 vec paths

val vecS_eq :
  nat -> 'a1 vec -> 'a1 vec -> 'a1 paths -> 'a1 vec paths -> 'a1 vec paths

val vec_extens :
  nat -> 'a1 vec -> 'a1 vec -> (stn -> 'a1 paths) -> 'a1 vec paths

val make_vec_el : nat -> 'a1 vec -> 'a1 vec paths

val isweqvecfun : nat -> ('a1 vec, stn -> 'a1) isweq

val weqvecfun : nat -> ('a1 vec, stn -> 'a1) weq

val isofhlevelvec : nat -> 'a1 isofhlevel -> nat -> 'a1 vec isofhlevel

val vec_ind :
  'a2 -> ('a1 -> nat -> 'a1 vec -> 'a2 -> 'a2) -> nat -> 'a1 vec -> 'a2

val vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec

val hd_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 paths

val tl_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec paths

val el_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> stn -> 'a2 paths

val vec_map_as_make_vec : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec paths

val vec_foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> nat -> 'a1 vec -> 'a2

val vec_foldr1 : ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 vec -> 'a1

val vec_append : nat -> 'a1 vec -> nat -> 'a1 vec -> 'a1 vec

val vec_map_id : nat -> 'a1 vec -> 'a1 vec paths

val vec_map_comp :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> nat -> 'a1 vec -> 'a3 vec paths

val vec_map_make_vec : nat -> (stn -> 'a1) -> ('a1 -> 'a2) -> 'a2 vec paths

val vec_append_lid : 'a1 vec -> nat -> ('a1 vec -> 'a1 vec) paths

val vec_fill : 'a1 -> nat -> 'a1 vec

val vec_map_const : nat -> 'a1 vec -> 'a2 -> 'a2 vec paths

val vec_zip : nat -> 'a1 vec -> 'a2 vec -> ('a1, 'a2) dirprod vec
open Preamble
open StandardFiniteSets
open Vectors

val coq_Unnamed_thm : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm0 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec paths

val coq_Unnamed_thm4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> (stn -> 'a1) paths

val coq_Unnamed_thm5 :
  ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 -> 'a1 -> 'a1 -> 'a2 paths

val coq_Unnamed_thm6 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm7 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec paths
open PartA
open Preamble

val transitive_paths_weq :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) weq

val weqtotal2comm :
  (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq

val pathsdirprodweq :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (('a1, 'a2) dirprod paths, ('a1 paths, 'a2
  paths) dirprod) weq

val dirprod_with_contr_r : 'a1 iscontr -> ('a2, ('a2, 'a1) dirprod) weq

val dirprod_with_contr_l : 'a1 iscontr -> ('a2, ('a1, 'a2) dirprod) weq

val total2_assoc_fun_left :
  (('a1 -> ('a2, 'a3) total2, 'a4) total2, ('a1 -> 'a2, ('a1 -> 'a3, 'a4)
  total2) total2) weq

val sec_total2_distributivity :
  ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq
open NaturalNumbers
open PartA
open PartD
open Preamble
open Propositions
open Propositions0
open Univalence
open UnivalenceAxiom

type __ = Obj.t

type ('x, 'lt, 'p) hereditary = 'x -> ('x -> 'lt -> 'p) -> 'p

type ('x, 'lt) strongly_well_founded =
  __ -> ('x, 'lt, __) hereditary -> ('x -> __, 'x -> __ paths) total2

type ('x, 'lt) weakly_well_founded =
  ('x -> hProp) -> ('x, 'lt, hProptoType) hereditary -> 'x -> hProptoType

type ('x, 'lt) chain = __

type ('x, 'lt) le = (nat, ('x, 'lt) chain) total2

val nil : 'a1 -> ('a1, 'a2) le

val cons' :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) le -> 'a2 -> 'a1 paths -> ('a1, 'a2)
  le

val cons1 :
  nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) chain ->
  ('a1, 'a2) chain

val cons :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) le -> ('a1, 'a2)
  le

val coq_Unnamed_thm :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) le
  -> 'a2 -> 'a1 paths -> ('a1, 'a2) le paths

type ('x, 'lt, 'p) guided_by = 'x -> ('x, 'lt) le -> 'p paths

type ('x, 'lt, 'p) attempt =
  ('x -> ('x, 'lt) le -> 'p, ('x, 'lt, 'p) guided_by) total2

val attempt_fun :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 ->
  ('a1, 'a2) le -> 'a3

val attempt_comp :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) guided_by

val disassemble_attempt :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 -> 'a1
  -> 'a2 -> 'a1 paths -> ('a1, 'a2, 'a3) attempt

val assemble_attempt :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a1 paths ->
  ('a1, 'a2, 'a3) attempt) -> ('a1, 'a2, 'a3) attempt

val attempt_lemma :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt -> (('a1 -> ('a1, 'a2) le -> 'a3) paths -> 'a4) -> ('a1 ->
  ('a1, 'a2) le -> 'a3 paths) -> 'a4

val attempt_paths :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt -> ('a1 -> ('a1, 'a2) le -> 'a3 paths) -> ('a1 -> ('a1, 'a2)
  le -> 'a3 paths paths) -> ('a1, 'a2, 'a3) attempt paths

val assemble_disassemble :
  ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1, 'a2,
  'a3) attempt paths

val iscontr_attempt :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
  ('a1, 'a2, 'a3) attempt iscontr

val the_attempt :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
  ('a1, 'a2, 'a3) attempt

val the_value :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a3

val the_comp :
  ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a3
  paths

val strongly_from_weakly_well_founded :
  ('a1, 'a2) weakly_well_founded -> ('a1, 'a2, __) hereditary -> ('a1 -> __,
  'a1 -> __ paths) total2

val irrefl : ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a2 neg

val notboth : ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a1 -> 'a2 -> 'a2 neg

val diagRecursion :
  (nat -> 'a1) -> (nat -> nat -> 'a1 -> 'a1) -> nat -> nat -> 'a1

val chaintrans :
  'a1 -> 'a1 -> 'a1 -> nat -> nat -> ('a1, 'a2) chain -> ('a1, 'a2) chain ->
  ('a1, 'a2) chain
open AxiomOfChoice
open Notations
open OrderedSets
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open Sets0
open Subtypes
open UnivalenceAxiom

val coq_TotalOrdering : hSet -> hSet

val coq_TOSubset_set : hSet -> hSet

type coq_TOSubset = pr1hSet

val coq_TOSubset_to_subtype : hSet -> coq_TOSubset -> pr1hSet hsubtype

val coq_TOSrel : hSet -> coq_TOSubset -> pr1hSet hrel

val coq_TOtotal : hSet -> coq_TOSubset -> hProptoType

val coq_TOtot : hSet -> coq_TOSubset -> pr1hSet istotal

val coq_TOanti : hSet -> coq_TOSubset -> pr1hSet isantisymm

val coq_TOrefl : hSet -> coq_TOSubset -> pr1hSet isrefl

val coq_TOeq_to_refl : hSet -> coq_TOSubset -> hProptoType

val coq_TOeq_to_refl_1 : hSet -> coq_TOSubset -> hProptoType

val coq_TOtrans : hSet -> coq_TOSubset -> pr1hSet istrans

val h1'' :
  hSet -> coq_TOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
  carrier -> pr1hSet carrier -> hProptoType -> pr1hSet paths -> pr1hSet paths
  -> hProptoType

val tosub_order_compat :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> hProp

val tosub_le : hSet -> coq_TOSubset -> coq_TOSubset -> hProp

val sub_initial :
  hSet -> pr1hSet hsubtype -> coq_TOSubset -> hProptoType -> hProp

val same_induced_ordering :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType ->
  hProptoType -> hProp

val common_initial :
  hSet -> pr1hSet hsubtype -> coq_TOSubset -> coq_TOSubset -> hProp

val max_common_initial :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype

val max_common_initial_is_max :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType ->
  hProptoType

val max_common_initial_is_sub :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType

val max_common_initial_is_common_initial :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType

val tosub_fidelity :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier -> hProptoType

val coq_TOSubset_plus_point_rel :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> pr1hSet hrel

val isTotalOrder_TOSubset_plus_point :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> coq_TOSubset

val coq_TOSubset_plus_point_incl :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point_le :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point_initial :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val hasSmallest : 'a1 hrel -> hProp

val isWellOrder : hSet -> pr1hSet hrel -> hProp

val coq_WellOrdering : hSet -> hSet

val coq_WOSubset_set : hSet -> hSet

type coq_WOSubset = pr1hSet

val coq_WOSubset_to_subtype : hSet -> coq_WOSubset -> pr1hSet hsubtype

val coq_WOSrel : hSet -> coq_WOSubset -> pr1hSet hrel

val coq_WOStotal : hSet -> coq_WOSubset -> hProptoType

val coq_WOSubset_to_TOSubset : hSet -> coq_WOSubset -> coq_TOSubset

val coq_WOSwo : hSet -> coq_WOSubset -> pr1hSet

val lt : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProp

val coq_WOS_hasSmallest : hSet -> coq_WOSubset -> hProptoType

val wo_lt_to_le :
  hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProptoType
  -> hProptoType

val wosub_le : hSet -> coq_WOSubset hrel

val wosub_le_inc :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_comp :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_subi :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_isrefl : hSet -> coq_WOSubset isrefl

val wosub_equal : hSet -> coq_WOSubset hrel

val wosub_comparable : hSet -> coq_WOSubset hrel

val hasSmallest_WOSubset_plus_point :
  hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_WOSubset_plus_point :
  hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType ->
  coq_WOSubset

val wosub_univalence_map :
  hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType

val wosub_univalence :
  hSet -> coq_WOSubset -> coq_WOSubset -> (coq_WOSubset paths, hProptoType)
  weq

val wosub_univalence_compute :
  hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType
  paths

val wosub_inc :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier

val wosub_fidelity :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier -> hProptoType

val h1 :
  hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
  carrier -> pr1hSet carrier paths -> hProptoType -> hProptoType

val wosub_le_isPartialOrder : hSet -> coq_WOSubset isPartialOrder

val coq_WosubPoset : hSet -> coq_Poset

val wosub_le_smaller : hSet -> coq_WOSubset -> coq_WOSubset -> hProp

val upto : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet hsubtype

val upto_eqn :
  hSet -> coq_WOSubset -> coq_WOSubset -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType -> pr1hSet hsubtype paths

val isInterval :
  hSet -> pr1hSet hsubtype -> coq_WOSubset -> hProptoType -> hProptoType ->
  hProptoType -> hProptoType -> hProptoType

val is_wosubset_chain : hSet -> ('a1 -> coq_WOSubset) -> hProp

val common_index :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> pr1hSet ->
  hProptoType

val common_index2 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
  hProptoType

val common_index3 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
  pr1hSet -> hProptoType

val chain_union_prelim_eq0 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
  -> 'a1 -> hProptoType -> hProptoType -> hProptoType -> hProptoType -> hProp
  paths

val chain_union_rel :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet hrel

val chain_union_rel_eqn :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
  -> hProptoType -> hProptoType -> hProp paths

val chain_union_rel_istrans :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istrans

val chain_union_rel_isrefl :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isrefl

val chain_union_rel_isantisymm :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isantisymm

val chain_union_rel_istotal :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istotal

val chain_union_rel_isTotalOrder :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val chain_union_TOSubset :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_TOSubset

val chain_union_tosub_le :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType

val chain_union_rel_initial :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType

val chain_union_rel_hasSmallest :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val chain_union_WOSubset :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_WOSubset

val chain_union_le :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val proper_subtypes_set : hSet

val upto' : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet

val choice_fun : hSet -> hSet

val coq_AC_to_choice_fun : hSet -> hProptoType

val is_guided_WOSubset : hSet -> pr1hSet -> coq_WOSubset -> hProp

val upto'_eqn :
  hSet -> pr1hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet
  carrier -> pr1hSet carrier -> pr1hSet paths -> pr1hSet paths

type coq_Guided_WOSubset = (coq_WOSubset, hProptoType) total2

val guidedFamily : hSet -> pr1hSet -> coq_Guided_WOSubset -> coq_WOSubset

val guided_WOSubset_total : hSet -> pr1hSet -> hProptoType -> hProptoType

val coq_ZermeloWellOrdering : hSet -> hProptoType

type coq_WellOrderedSet = (hSet, pr1hSet) total2

val coq_WellOrderedSet_to_hSet : coq_WellOrderedSet -> hSet

val coq_WOrel : coq_WellOrderedSet -> pr1hSet hrel

val coq_WOlt : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp

val isaprop_theSmallest :
  hSet -> pr1hSet hrel -> hProptoType -> pr1hSet hsubtype -> pr1hSet isaprop

val coq_WO_isTotalOrder : coq_WellOrderedSet -> hProptoType

val coq_WO_isrefl : coq_WellOrderedSet -> pr1hSet isrefl

val coq_WO_istrans : coq_WellOrderedSet -> pr1hSet istrans

val coq_WO_istotal : coq_WellOrderedSet -> pr1hSet istotal

val coq_WO_isantisymm : coq_WellOrderedSet -> pr1hSet isantisymm

val coq_WO_hasSmallest : coq_WellOrderedSet -> hProptoType

val coq_WOlt_istrans : coq_WellOrderedSet -> pr1hSet istrans

val coq_WOlt_isirrefl : coq_WellOrderedSet -> pr1hSet isirrefl

val coq_WOlt'_subproof :
  coq_WellOrderedSet -> pr1hSet -> pr1hSet -> (hProptoType, pr1hSet paths
  neg) dirprod isaprop

val coq_WOlt' : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp

val coq_WOlt'_to_WOlt :
  coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType

val coq_WOlt_to_WOlt' :
  coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType
  -> hProptoType

val coq_WOlt_trich :
  coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType

val theSmallest : coq_WellOrderedSet -> pr1hSet hsubtype -> hProp

val coq_WO_theSmallest : coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType

val coq_WO_theUniqueSmallest :
  coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType

type iswofun =
  ((pr1hSet, pr1hSet) iscomprelrelfun, pr1hSet -> pr1hSet -> hProptoType ->
  hProptoType) dirprod

val isaprop_iswofun :
  coq_WellOrderedSet -> coq_WellOrderedSet -> (pr1hSet -> pr1hSet) -> iswofun
  isaprop

type wofun = (pr1hSet -> pr1hSet, iswofun) total2

val pr1wofun :
  coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> pr1hSet -> pr1hSet

val wofun_eq :
  coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> wofun -> (pr1hSet ->
  pr1hSet) paths -> wofun paths

val iswofun_idfun : coq_WellOrderedSet -> iswofun

val iswofun_funcomp :
  coq_WellOrderedSet -> coq_WellOrderedSet -> coq_WellOrderedSet -> wofun ->
  wofun -> iswofun

val empty_woset_subproof : pr1hSet

val empty_woset : coq_WellOrderedSet

val unit_woset_subproof : pr1hSet -> pr1hSet -> hProptoType isaprop

val unit_woset : coq_WellOrderedSet
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom
open WellOrderedSets

val contr_to_pr1contr :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
  paths iscontr -> 'a1 paths iscontr

val pr1contr_to_contr :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> 'a1 paths iscontr -> ('a1,
  hProptoType) total2 paths iscontr

val substructure_univalence :
  ('a1 -> 'a1 -> ('a1 paths, 'a2) weq) -> ('a1 -> hProp) -> ('a1,
  hProptoType) total2 -> ('a1, hProptoType) total2 -> (('a1, hProptoType)
  total2 paths, 'a2) weq

type coq_PointedGraph = (hSet, (pr1hSet hrel, pr1hSet) total2) total2

type isaroot = pr1hSet -> hProptoType

val isaprop_isaroot : hSet -> pr1hSet hrel -> pr1hSet -> isaroot isaprop

type isTRR = (pr1hSet isrefl, (pr1hSet istrans, isaroot) dirprod) dirprod

val isaprop_isTRR : hSet -> pr1hSet hrel -> pr1hSet -> isTRR isaprop

type coq_TRRGraphData = (pr1hSet hrel, (pr1hSet, isTRR) total2) total2

val isaset_TRRGraphData : hSet -> coq_TRRGraphData isaset

type coq_TRRGraph = (hSet, coq_TRRGraphData) total2

val coq_TRRG_edgerel : coq_TRRGraph -> pr1hSet hrel

val coq_TRRG_root : coq_TRRGraph -> pr1hSet

val coq_TRRG_transitivity : coq_TRRGraph -> pr1hSet istrans

val selfedge : coq_TRRGraph -> pr1hSet -> hProptoType

type isTRRGhomo =
  (pr1hSet -> pr1hSet -> (hProptoType, hProptoType) logeq, pr1hSet paths)
  dirprod

val isaprop_isTRRGhomo :
  coq_TRRGraph -> coq_TRRGraph -> (pr1hSet -> pr1hSet) -> isTRRGhomo isaprop

val coq_TRRGhomo_frompath :
  hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
  coq_TRRGraphData paths -> isTRRGhomo

val helper :
  hSet -> (pr1hSet -> pr1hSet -> hProp) -> (pr1hSet -> pr1hSet -> hProp) ->
  pr1hSet -> pr1hSet -> isTRR -> isTRR -> (pr1hSet -> pr1hSet -> hProp) paths
  -> pr1hSet paths -> (pr1hSet, isTRR) total2 paths

val coq_TRRGhomo_topath :
  hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
  isTRRGhomo -> coq_TRRGraphData paths

type coq_TRRGraphiso = ((pr1hSet, pr1hSet) weq, isTRRGhomo) total2

val id_TRRGraphiso : coq_TRRGraph -> coq_TRRGraphiso

val coq_TRRGraph_univalence_map :
  coq_TRRGraph -> coq_TRRGraph -> coq_TRRGraph paths -> coq_TRRGraphiso

val coq_TRRGraph_univalence_weq1 :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, (hSet,
  coq_TRRGraphData) coq_PathPair) weq

val coq_TRRGraph_univalence_weq2 :
  coq_TRRGraph -> coq_TRRGraph -> ((hSet, coq_TRRGraphData) coq_PathPair,
  coq_TRRGraphiso) weq

val coq_TRRGraph_univalence_weq2_idpath :
  coq_TRRGraph -> coq_TRRGraphiso paths

val coq_TRRGraph_univalence_weq1_idpath :
  coq_TRRGraph -> (hSet, coq_TRRGraphData) coq_PathPair paths

val isweq_TRRGraph_univalence_map :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso) isweq

val coq_TRRGraph_univalence :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso) weq

val coq_TRRGraph_univalence_compute :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths -> coq_TRRGraphiso)
  paths

type coq_DownwardClosure = (pr1hSet, hProptoType) total2

type antisymmetric = (hProptoType, hProptoType) dirprod -> pr1hSet paths

val total : coq_TRRGraph -> pr1hSet -> pr1hSet -> hProp

type isatree =
  pr1hSet -> coq_DownwardClosure -> coq_DownwardClosure -> (antisymmetric,
  hProptoType) dirprod

val isaprop_isatree : coq_TRRGraph -> isatree isaprop

type coq_Tree = (coq_TRRGraph, isatree) total2

type coq_Tree_iso = coq_TRRGraphiso

val coq_Tree_univalence :
  coq_Tree -> coq_Tree -> (coq_Tree paths, coq_Tree_iso) weq

type coq_Upw_underlying = (pr1hSet, hProptoType) total2

val isaset_Upw_underlying : coq_Tree -> pr1hSet -> coq_Upw_underlying isaset

val coq_Upw : coq_Tree -> pr1hSet -> hSet

val coq_Upw_E : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> hProp

val coq_Upw_to_PointedGraph : coq_Tree -> pr1hSet -> coq_PointedGraph

val coq_Upw_reflexive : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType

val coq_Upw_transitive :
  coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType

val coq_Upw_rooted : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType

val coq_Upw_to_TRRGraph : coq_Tree -> pr1hSet -> coq_TRRGraph

val isatree_Upw : coq_Tree -> pr1hSet -> isatree

val coq_Up : coq_Tree -> pr1hSet -> coq_Tree

type isrigid = coq_Tree paths iscontr

val isaprop_isrigid : coq_Tree -> isrigid isaprop

type issuperrigid = (isrigid, pr1hSet -> isrigid) dirprod

val isaprop_issuperrigid : coq_Tree -> issuperrigid isaprop

val isWellFoundedUp : coq_Tree -> hProp

val hasLargest : 'a1 hrel -> hProp

val isWellFoundedDown : coq_Tree -> hProp

type coq_Tree_isWellFounded = (hProptoType, hProptoType) dirprod

val isaprop_Tree_isWellFounded : coq_Tree -> coq_Tree_isWellFounded isaprop

type ispreZFS = (coq_Tree_isWellFounded, issuperrigid) dirprod

val isaprop_ispreZFS : coq_Tree -> ispreZFS isaprop

type preZFS = (coq_Tree, ispreZFS) total2

val coq_Ve : preZFS -> hSet

val coq_Ed : preZFS -> pr1hSet -> pr1hSet -> hProp

val root : preZFS -> pr1hSet

val preZFS_isrigid : preZFS -> preZFS paths iscontr

val isaset_preZFS : preZFS isaset

type preZFS_iso = coq_Tree_iso

val preZFS_univalence : preZFS -> preZFS -> (preZFS paths, preZFS_iso) weq

val preZFS_Branch : preZFS -> pr1hSet -> coq_Tree

val preZFS_Branch_hsubtype_tohsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype

val hsubtype_to_preZFS_Branch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype

val coq_Branch_to_subtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype paths

val fromBranch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
  hProptoType

val toBranch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType

val preZFS_Branch_isWellFounded : preZFS -> pr1hSet -> coq_Tree_isWellFounded

val iscontrauto_Tree_TRRGraph :
  coq_Tree -> isrigid -> coq_TRRGraph paths iscontr

val coq_Up_to_Up : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val coq_Up_to_Up_inv : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val isweq_Up_to_Up :
  coq_Tree -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq

val isTRRGhomo_Up_to_Up : coq_Tree -> pr1hSet -> pr1hSet -> isTRRGhomo

val coq_UpUpid : coq_Tree -> pr1hSet -> pr1hSet -> coq_TRRGraph paths

val preZFS_Branch_issuperrigid : preZFS -> pr1hSet -> issuperrigid

val coq_Branch : preZFS -> pr1hSet -> preZFS

type hasuniquerepbranch = pr1hSet -> pr1hSet -> preZFS paths -> pr1hSet paths

val isaprop_hasuniquerepbranch : preZFS -> hasuniquerepbranch isaprop

type coq_ZFS = (preZFS, hasuniquerepbranch) total2

val pr1ZFS : coq_ZFS -> preZFS

type coq_ZFS_iso = preZFS_iso

val coq_ZFS_univalence :
  coq_ZFS -> coq_ZFS -> (coq_ZFS paths, coq_ZFS_iso) weq

val isaset_ZFS : coq_ZFS isaset

val coq_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val coq_Branch_of_Branch_to_Branch_inv :
  preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val isweq_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq

val isTRRGhomo_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> isTRRGhomo

val coq_Branch_of_Branch_eq_Branch :
  preZFS -> pr1hSet -> pr1hSet -> preZFS paths

val coq_ZFS_Branch_is_ZFS : coq_ZFS -> pr1hSet -> hasuniquerepbranch

val coq_ZFS_Branch : coq_ZFS -> pr1hSet -> coq_ZFS

val coq_Root : coq_ZFS -> pr1hSet

val isapoint : coq_ZFS -> pr1hSet -> hProp

val isaprop_isapoint : coq_ZFS -> pr1hSet -> hProptoType isaprop

type coq_ZFS_elementof =
  (pr1hSet, (hProptoType, coq_ZFS paths) dirprod) total2

val isaprop_ZFS_elementof : coq_ZFS -> coq_ZFS -> coq_ZFS_elementof isaprop
val nat_dist : nat -> nat -> nat

module Discern :
 sig
  type nat_discern = __

  val coq_Unnamed_thm : nat -> nat -> nat_discern -> nat_discern

  val nat_discern_inj : nat -> nat -> nat_discern -> nat_discern

  val nat_discern_isaprop : nat -> nat -> nat_discern isaprop

  val nat_discern_unit : nat -> coq_UU paths

  val nat_discern_iscontr : nat -> nat_discern iscontr

  val helper_A : nat -> nat -> nat paths -> nat_discern

  val helper_B : nat -> nat -> nat_discern -> nat paths

  val coq_Unnamed_thm0 : nat -> nat -> nat_discern -> nat paths paths

  val helper_C : nat -> nat -> nat paths -> nat_discern

  val apSC : nat -> nat -> nat paths -> nat_discern paths

  val helper_D : nat -> nat -> (nat_discern, nat paths) isweq

  val coq_E : nat -> nat -> (nat_discern, nat paths) weq

  val nat_dist_anti : nat -> nat -> nat paths -> nat paths
 end
