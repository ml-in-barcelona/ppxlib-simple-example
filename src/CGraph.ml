open Graph
open PartA
open PartB
open PartD
open PartD0
open Preamble
open Propositions0
open Sets
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type precgraph =
  (coq_UU, (coq_UU, (__ -> __, __ -> __) dirprod) total2) total2

(** val make_precgraph : ('a2 -> 'a1) -> ('a2 -> 'a1) -> precgraph **)

let make_precgraph s t =
  { pr1 = __; pr2 = { pr1 = __; pr2 =
    (make_dirprod (Obj.magic s) (Obj.magic t)) } }

type node = __

type arc = __

(** val source : precgraph -> arc -> node **)

let source g =
  g.pr2.pr2.pr1

(** val target : precgraph -> arc -> node **)

let target g =
  g.pr2.pr2.pr2

type has_nodeset = node isaset

type has_arcset = arc isaset

type cgraph = (precgraph, (node isaset, arc isaset) dirprod) total2

(** val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph **)

let make_cgraph g h k =
  { pr1 = g; pr2 = (make_dirprod h k) }

(** val precgraph_of_cgraph : cgraph -> precgraph **)

let precgraph_of_cgraph t =
  t.pr1

(** val isaset_node : cgraph -> node isaset **)

let isaset_node g =
  g.pr2.pr1

(** val node_set : cgraph -> hSet **)
(*
   in ocaml extracted from unimath coq  via metacoq:
type __ = Obj.t
type coq_UU = __
type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }
*)
let make_hSet i =
  { pr1 = __; pr2 = (Obj.magic i) }

let node_set g =  make_hSet (isaset_node g) 

(*
now with this information please reinterpret this internal representation
_build/log:293:> TOPstructure_item_desc:printdescPstr_value:pattern:PATTERNpattern_Ppat_var:node_set| expr: EXPR:process_fun:process_arg_labelNoLabel|process_expression_option_TODOnope|PATTERNpattern_Ppat_var:g|EXPR:apply:EXPR:IDENTident:make_hSet|process_list1process_arg_labelNoLabel|EXPR:apply:EXPR:IDENTident:isaset_node|process_list1process_arg_labelNoLabel|EXPR:IDENTident:g|process_list1process_list1|process_list1process_list1;;print_value_binding_list;; *)

(*

#+begin_src output
In the internal representation you provided, `node_set` is a hSet created by calling the function `make_hSet`, which takes two arguments: the first is an identifier for some object (in this case, an integer), and the second is an object (in this case, a cgraph). The resulting hSet has two fields: `pr1` and `pr2`. The value of `pr1` is set to the magic number associated with the object passed as the first argument to `make_hSet`, which is likely a unique identifier for that object in some context. The value of `pr2` is set to the cgraph object passed as the second argument to `make_hSet`.

Based on this information, it seems that `node_set` represents a mapping from an integer identifier to a cgraph object. This mapping is likely used to keep track of nodes in some sort of graph data structure or other data structure that uses unique identifiers for its elements.
#+end_src
#+begin_src output

It looks like you are defining a function `node_set` that takes in an OCaml code object (a `cgraph`) and returns a hash set of nodes within that code. The `make_hSet` function takes in the set of node identifiers from the code object and returns a hash set with one element containing the value of the first node identifier and another element containing the value of a Coq object (which you are referring to as an "isaset\_node" object).

The `process_fun` function likely processes a given function within the code object and converts it into a form that can be stored in the hash set. The `process_arg_labelNoLabel` function probably does the same thing for each argument of the function, ignoring any labels associated with them.

The `process_expression_option_TODOnope` function is not defined in this code snippet, so it's difficult to say what it does exactly. It may be used to process specific options or attributes within the function or code object that need to be stored in the hash set.

Overall, `node_set` appears to be a function that takes in an OCaml code object and returns a hash set containing the node identifiers and values of the nodes within that code.
#+end_src
#+begin_src output
The internal representation of the function `node_set` is a closure that takes as an argument a Coq graph and returns an HSet. The `isaset_node` function is used to obtain a set of nodes from the given graph. The resulting HSet has two elements: a value (which is `__` in this case) and the set of nodes obtained from the graph using `isaset_node`.

This closure is created by combining multiple functions into one, which are called within the closure. These functions include:

* `make_hSet`: This function takes a set of nodes as input and returns an HSet with two elements: a value (which is `__`) and the set of nodes obtained from the graph using `isaset_node`.
* `isaset_node`: This function takes a Coq graph as input and returns a set of its nodes.
* `apply`: This is an application operator that takes two arguments: an expression and a value, which are combined to form a new expression. In this case, the expression is either the fun or the arg label (which has no label), and the value is either the identifier of the set obtained from `isaset_node`, or the identifier of the graph `g`.
* `process_fun`: This function processes a fun by calling the `apply` operator with the fun and the value as arguments.
* `process_arg_labelNoLabel`: This function processes an argument label with no label by calling the `apply` operator with the arg label and the value as arguments.
* `process_expression_option_TODOnope`: This function processes an expression option, but it is not used in this closure.
* `process_list1`: This function processes a list of one argument by calling the `process_fun` or `process_arg_labelNoLabel` function with the first element of the list and the value as arguments. It also calls the `process_list1` function with the rest of the list to recursively process the remaining elements.
* `print_value_binding_list`: This function is not used in this closure, but it is likely responsible for printing the resulting HSet.
#+end_src
#+begin_src output
Based on the given code snippet, it seems that `node_set` is a function that takes in a Coq graph (represented by the type `cgraph`) and returns an object of type `hSet`. The `make_hSet` function creates an instance of this object by taking in the set of nodes of the input graph.

Inside the `node_set` function, the `isaset_node` function is called with the given Coq graph to obtain a set of node identifiers in the graph. The `make_hSet` function then creates an instance of type `('t, 'p) total2` where `'t` is the type of the element in the set and `'p` is the proof object for each element in the set.

It appears that the resulting object of type `hSet` represents a collection of nodes in the input graph and their corresponding proof objects.
#+end_src
#+begin_src output
It appears that the given OCaml code defines a function `make_hSet` which takes an integer value `i` as input and returns a new hash set with one element, which is the value of `i`. The resulting hash set has two fields: `pr1`, which is initialized to an empty object (`__`) and `pr2`, which is initialized to the integer value passed as an argument `i` using `Obj.magic i`.

The function then calls another function `node_set` which creates a new hash set by passing the result of `isaset_node g` (which returns a boolean indicating whether the value `g` belongs to the current set) as its first argument and an empty object `__` as its second argument. This is done using the following line:
```scss
let node_set g =  make_hSet (isaset_node g) 
```
It seems that `node_set` function returns a hash set containing one element: `g`.
#+end_src
#+begin_src output
This looks like code written in OCaml, a functional programming language. It seems to be defining an internal representation for building and manipulating a Coq object graph (a tree-like structure used to represent mathematical constructs) using the Coq library.

The `node_set` function takes a Coq object graph `g` and returns a set of nodes in that graph. The nodes are represented as objects with a magic number attached to them, which is probably used to uniquely identify each node in the graph.

The `make_hSet` function creates an empty set with two parameters: `pr1`, an object with a magic number, and `pr2`, the value of that magic number (which is likely the identity of the node). This set will be used to store nodes in the graph.

The `isaset_node g` expression returns the set of nodes in the graph `g`. This is used as the first parameter for `make_hSet`, which creates a new empty set with the identity of each node in the graph stored in its magic number.
#+end_src
#+begin_src output
This code is a Coq program that defines an internal representation of a set of nodes in a graph. The nodes are represented as values of type `hSet`, which is defined as follows:
```ruby
{ pr1 : 't; pr2 : 'p }
```
where `pr1` is an arbitrary value of type `'t`, and `pr2` is an arbitrary value of type `'p`.

The program uses the `isaset_node` function to create a set of node IDs, which are then used to create a new `hSet` object with those IDs as arguments. This creates a set of nodes that can be used to represent the graph in Coq. The `make_hSet` function takes an arbitrary value of type `'t` and returns a new `hSet` object with that value assigned to `pr1`.

The program then creates several `apply` operations, which are used to create expressions that combine elements of the graph. Each `apply` operation has two arguments: an expression of type `EXPR`, which is either a `process_fun` or a `process_arg_labelNoLabel`, and a label of type `IDENT`. The resulting expression applies the function to each node in the set, using the IDs as labels.

The program also includes some helper functions that are used throughout the code. These functions are not relevant to understanding the main logic of the program.
#+end_src
#+begin_src output
The given code uses a type `hSet` which is constructed from an OCaml `Obj.t`. The function `make_hSet` creates an instance of the `hSet` type with two fields: `pr1` and `pr2`. `pr1` is an `Obj.t`, while `pr2` is the result of applying `Obj.magic` to a Coq object with ID i.

The code then uses this `node_set` value to store information about nodes in a graph represented by the Coq `isaset_node` function.

It appears that the `PATTERNpattern_Ppat_var:node_set|EXPR:` pattern in the output represents an instance of the `node_set` type, which contains information about a node in the graph. The variable name associated with this node is `node_set`.
#+end_src


#+begin_src output *)

(* In the realm of functional programming with OCaml, we find ourselves in a world of abstraction and computation. Our code is extracting information from Coq's UniMath library via Metacoq, revealing its underlying type system. The main idea is to define our own types for simplicity and ease of understanding. *)

(* We start by defining a new type `__` that represents an empty object in the OCaml type system. This will be our primary building block for creating other types. Additionally, we introduce a type `coq_UU`, which is equivalent to the original Coq type `Obj.t`. This type will allow us to represent UniMath objects in our OCaml code. *)

(* Furthermore, we create a new type `('t, 'p) total2`, which is a tuple containing two elements of types `'t` and `'p`. This represents a set with two distinct elements. We will use this type to represent the concept of a set in our code. *)

(* Now, let's introduce a function called `make_hSet`, which takes an integer as input and returns an object of type `('t, 'p) total2`. The function creates an empty set using the `Obj.magic` method to generate a unique identifier for it. It then assigns this identifier to the `pr1` field while leaving the `pr2` field empty, indicating that the set currently contains only one element. *)

(* In summary, our code is defining new types and functions to represent sets in OCaml using Coq's UniMath library as a foundation. By doing so, we simplify the understanding of the code while maintaining its computational correctness. *)
(*

#+end_src *)


(** val isaset_arc : cgraph -> arc isaset **)

let isaset_arc g =
  g.pr2.pr2

(** val arc_set : cgraph -> hSet **)

let arc_set g =
  make_hSet (isaset_arc g)

type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod

type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2

(** val make_cgraph_mor :
    precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> is_cgraph_mor
    -> cgraph_mor **)

let make_cgraph_mor _ _ p_UU2080_ p_UU2081_ h =
  { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h } }

(** val onnode : precgraph -> precgraph -> cgraph_mor -> node -> node **)

let onnode _ _ t =
  t.pr1

(** val onarc : precgraph -> precgraph -> cgraph_mor -> arc -> arc **)

let onarc _ _ f =
  f.pr2.pr1

(** val preserves_source :
    precgraph -> precgraph -> cgraph_mor -> arc -> node paths **)

let preserves_source _ _ p =
  p.pr2.pr2.pr1

(** val preserves_target :
    precgraph -> precgraph -> cgraph_mor -> arc -> node paths **)

let preserves_target _ _ p =
  p.pr2.pr2.pr2

(** val is_cgraph_mor_id : precgraph -> is_cgraph_mor **)

let is_cgraph_mor_id _ =
  make_dirprod (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val cgraph_mor_id : precgraph -> cgraph_mor **)

let cgraph_mor_id g =
  make_cgraph_mor g g idfun idfun (is_cgraph_mor_id g)

(** val is_cgraph_mor_comp :
    precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
    is_cgraph_mor **)

let is_cgraph_mor_comp g h k p q =
  make_dirprod (fun f ->
    pathscomp0 (source k (onarc h k q (onarc g h p f)))
      (onnode h k q (source h (onarc g h p f)))
      (onnode h k q (onnode g h p (source g f)))
      (preserves_source h k q (onarc g h p f))
      (maponpaths (onnode h k q) (source h (onarc g h p f))
        (onnode g h p (source g f)) (preserves_source g h p f))) (fun f ->
    pathscomp0 (target k (onarc h k q (onarc g h p f)))
      (onnode h k q (target h (onarc g h p f)))
      (onnode h k q (onnode g h p (target g f)))
      (preserves_target h k q (onarc g h p f))
      (maponpaths (onnode h k q) (target h (onarc g h p f))
        (onnode g h p (target g f)) (preserves_target g h p f)))

(** val cgraph_mor_comp :
    precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
    cgraph_mor **)

let cgraph_mor_comp g h k p q =
  make_cgraph_mor g k (funcomp (onnode g h p) (onnode h k q))
    (funcomp (onarc g h p) (onarc h k q)) (is_cgraph_mor_comp g h k p q)

(** val cgraph_mor_id_left :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_id_left g h p =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h0 = pr3.pr2 in
  pair_path_in2 p_UU2080_ { pr1 =
    (funcomp (onarc g g (cgraph_mor_id g))
      (onarc g h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }));
    pr2 =
    (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
      { pr1 = p_UU2081_; pr2 = h0 } }) } { pr1 = p_UU2081_; pr2 = h0 }
    (pair_path_in2 p_UU2081_
      (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
        { pr1 = p_UU2081_; pr2 = h0 } }) h0
      (dirprod_paths
        (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
          { pr1 = p_UU2081_; pr2 = h0 } }) h0
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 =
            p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }).pr1
          (Obj.magic h0).pr1 (fun f ->
          Obj.magic pathscomp0rid (source h (p_UU2081_ f))
            (p_UU2080_ (source g f)) (h0.pr1 f)))
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 =
            p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }).pr2
          (Obj.magic h0).pr2 (fun f ->
          Obj.magic pathscomp0rid (target h (p_UU2081_ f))
            (p_UU2080_ (target g f)) (h0.pr2 f)))))

(** val cgraph_mor_id_right :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_id_right g h p =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h0 = pr3.pr2 in
  pair_path_in2 p_UU2080_ { pr1 =
    (funcomp
      (onarc g h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } })
      (onarc h h (cgraph_mor_id h))); pr2 =
    (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
      pr2 = h0 } } (cgraph_mor_id h)) } { pr1 = p_UU2081_; pr2 = h0 }
    (pair_path_in2 p_UU2081_
      (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
        pr2 = h0 } } (cgraph_mor_id h)) h0
      (dirprod_paths
        (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h0 } } (cgraph_mor_id h)) h0
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 =
            { pr1 = p_UU2081_; pr2 = h0 } } (cgraph_mor_id h)).pr1
          (Obj.magic h0).pr1 (fun f ->
          Obj.magic maponpathsidfun (h.pr2.pr2.pr1 (p_UU2081_ f))
            (p_UU2080_ (source g f)) (h0.pr1 f)))
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 =
            { pr1 = p_UU2081_; pr2 = h0 } } (cgraph_mor_id h)).pr2
          (Obj.magic h0).pr2 (fun f ->
          Obj.magic maponpathsidfun (h.pr2.pr2.pr2 (p_UU2081_ f))
            (p_UU2080_ (target g f)) (h0.pr2 f)))))

(** val cgraph_mor_comp_assoc :
    precgraph -> precgraph -> precgraph -> precgraph -> cgraph_mor ->
    cgraph_mor -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_comp_assoc g1 g2 g3 g4 p q r =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h = pr3.pr2 in
  let q_UU2080_ = q.pr1 in
  let pr4 = q.pr2 in
  let q_UU2081_ = pr4.pr1 in
  let k = pr4.pr2 in
  let r_UU2080_ = r.pr1 in
  let pr5 = r.pr2 in
  let r_UU2081_ = pr5.pr1 in
  let l = pr5.pr2 in
  pair_path_in2
    (funcomp
      (onnode g1 g3
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } }))
      (onnode g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
    { pr1 =
    (funcomp
      (onarc g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h } })
      (onarc g2 g4
        (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
          pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })));
    pr2 =
    (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
      pr2 = h } }
      (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
        pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })) }
    { pr1 =
    (funcomp
      (onarc g1 g3
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } }))
      (onarc g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }));
    pr2 =
    (is_cgraph_mor_comp g1 g3 g4
      (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
        pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } })
      { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }) }
    (pair_path_in2
      (funcomp
        (onarc g1 g3
          (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 =
            p_UU2081_; pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } }))
        (onarc g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
      (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 =
        p_UU2081_; pr2 = h } }
        (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
          pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
      (is_cgraph_mor_comp g1 g3 g4
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } })
        { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })
      (dirprod_paths
        (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 =
          p_UU2081_; pr2 = h } }
          (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 =
            r_UU2081_; pr2 = l } }))
        (is_cgraph_mor_comp g1 g3 g4
          (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 =
            p_UU2081_; pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } }) { pr1 = r_UU2080_; pr2 = { pr1 =
          r_UU2081_; pr2 = l } })
        (Obj.magic funextsec (fun f ->
          Obj.magic pathscomp0
            (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
            (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (source g2 (p_UU2081_ f)))
                (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))))
            (maponpaths (funcomp q_UU2080_ r_UU2080_)
              (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
              (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                p_UU2081_; pr2 = h } } f))) (fun f ->
          Obj.magic pathscomp0
            (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
            (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
              r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
            (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
              (q_UU2080_ (p_UU2080_ (source g1 f)))
              (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (source g2 (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))
                (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                  (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))) (fun f ->
          pathscomp0
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))))
              (maponpaths (funcomp q_UU2080_ r_UU2080_)
                (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                  p_UU2081_; pr2 = h } } f)))
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                    (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))))
            (pathsinv0
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                    r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (Obj.magic path_assoc
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (maponpaths
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f))))
              (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                    (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (pathsinv0
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))
                (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))
                (pathscomp0
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f)))
                    (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                    (maponpaths r_UU2080_
                      (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                    (maponpaths r_UU2080_
                      (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f))) r_UU2080_
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpaths
                    (pathscomp0
                      (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                      (maponpaths r_UU2080_
                        (source g3 (q_UU2081_ (p_UU2081_ f)))
                        (q_UU2080_ (source g2 (p_UU2081_ f)))
                        (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                          { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))
                    (maponpathscomp (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f)) q_UU2080_ r_UU2080_
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))))))
        (Obj.magic funextsec (fun f ->
          Obj.magic pathscomp0
            (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
            (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (target g2 (p_UU2081_ f)))
                (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))))
            (maponpaths (funcomp q_UU2080_ r_UU2080_)
              (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
              (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                p_UU2081_; pr2 = h } } f))) (fun f ->
          Obj.magic pathscomp0
            (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
            (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
              r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
            (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
              (q_UU2080_ (p_UU2080_ (target g1 f)))
              (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (target g2 (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))
                (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                  (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))) (fun f ->
          pathscomp0
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))))
              (maponpaths (funcomp q_UU2080_ r_UU2080_)
                (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                  p_UU2081_; pr2 = h } } f)))
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                    (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))))
            (pathsinv0
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                    r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (Obj.magic path_assoc
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (maponpaths
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f))))
              (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                    (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (pathsinv0
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))
                (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))
                (pathscomp0
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f)))
                    (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                    (maponpaths r_UU2080_
                      (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                    (maponpaths r_UU2080_
                      (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f))) r_UU2080_
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpaths
                    (pathscomp0
                      (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                      (maponpaths r_UU2080_
                        (target g3 (q_UU2081_ (p_UU2081_ f)))
                        (q_UU2080_ (target g2 (p_UU2081_ f)))
                        (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                          { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))
                    (maponpathscomp (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f)) q_UU2080_ r_UU2080_
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))))))))

(** val isaprop_is_cgraph_mor :
    precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> has_nodeset
    -> is_cgraph_mor isaprop **)

let isaprop_is_cgraph_mor g h p_UU2080_ p_UU2081_ h0 =
  isapropdirprod
    (impred_isaprop (fun f ->
      h0 (source h (p_UU2081_ f)) (p_UU2080_ (source g f))))
    (impred_isaprop (fun f ->
      h0 (target h (p_UU2081_ f)) (p_UU2080_ (target g f))))

(** val isaset_cgraph_mor :
    precgraph -> precgraph -> has_nodeset -> has_arcset -> cgraph_mor isaset **)

let isaset_cgraph_mor g h h0 k = 
  isaset_total2 (funspace_isaset h0) (fun p_UU2080_ ->
    isaset_total2 (funspace_isaset k) (fun p_UU2081_ ->
      isasetaprop (isaprop_is_cgraph_mor g h p_UU2080_ p_UU2081_ h0)))

(** val cgraph_mor_eq_aux :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor -> (node -> node)
    paths -> (arc -> arc) paths -> has_nodeset -> cgraph_mor paths **)

let cgraph_mor_eq_aux g h p q _ _ h0 =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let pr4 = pr3.pr2 in
  let psource = pr4.pr1 in
  let ptarget = pr4.pr2 in
  let pr5 = q.pr2 in
  let q_UU2081_ = pr5.pr1 in
  let pr6 = pr5.pr2 in
  let qsource = pr6.pr1 in
  let qtarget = pr6.pr2 in
  pair_path_in2 p_UU2080_ { pr1 = p_UU2081_; pr2 = { pr1 = psource; pr2 =
    ptarget } } { pr1 = q_UU2081_; pr2 = { pr1 = qsource; pr2 = qtarget } }
    (pair_path_in2 p_UU2081_ { pr1 = psource; pr2 = ptarget } { pr1 =
      qsource; pr2 = qtarget }
      (pathsdirprod psource qsource ptarget qtarget
        (Obj.magic funextsec psource qsource (fun f ->
          let x = source h (p_UU2081_ f) in
          let x' = p_UU2080_ (source g f) in
          let x0 = psource f in
          let x'0 = qsource f in (Obj.magic h0 x x' x0 x'0).pr1))
        (Obj.magic funextsec ptarget qtarget (fun f ->
          let x = target h (p_UU2081_ f) in
          let x' = p_UU2080_ (target g f) in
          let x0 = ptarget f in
          let x'0 = qtarget f in (Obj.magic h0 x x' x0 x'0).pr1))))

(** val cgraph_mor_eq :
    cgraph -> cgraph -> cgraph_mor -> cgraph_mor -> (node -> node paths) ->
    (arc -> arc paths) -> cgraph_mor paths **)

let cgraph_mor_eq g h p q e_UU2080_ e_UU2081_ =
  cgraph_mor_eq_aux (precgraph_of_cgraph g) (precgraph_of_cgraph h) p q
    (funextfun (onnode (precgraph_of_cgraph g) (precgraph_of_cgraph h) p)
      (onnode (precgraph_of_cgraph g) (precgraph_of_cgraph h) q) e_UU2080_)
    (funextfun (onarc (precgraph_of_cgraph g) (precgraph_of_cgraph h) p)
      (onarc (precgraph_of_cgraph g) (precgraph_of_cgraph h) q) e_UU2081_)
    (isaset_node h)

(** val precgraph_weq_pregraph : (precgraph, pregraph) weq **)

let precgraph_weq_pregraph = false
  (* weqfibtototal (fun _ -> *)
  (*   weqcomp (weqfibtototal (fun _ -> invweq weqfuntoprodtoprod)) *)
  (*     (\* (weqcomp (Obj.magic display_weq) (Obj.magic weqfunfromdirprod)) *\)) *)
