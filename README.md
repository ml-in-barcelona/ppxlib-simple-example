# ppxlib-simple-example

A simple ppx to examplify the initial setup of [ppxlib](https://github.com/ocaml-ppx/ppxlib/), part of the talk [**The needed introduction to writing a ppx**](https://youtu.be/dMoRMqQ6GLs?t=4184) given at [Reason STHLM Meetup](https://www.meetup.com/es-ES/ReasonSTHLM/)..

It uses [`opam`](https://opam.ocaml.org)
- OCaml 5.2.0
- dune 3.12
- ppxlib 0.27

## Installation

```bash
make install
```

## Building

```bash
make build # Builds the project, once
make dev # Watch the filesystem and re-builds the project on each change
```

## Testing

```bash
make test # Runs snapshot tests
make test-watch # Watch the filesystem and re-runs the tests on each change
make test-update # Updates the snapshot tests
```

## Usage

Users of your ppx need to add the ppx name to their dune stanza:

```lisp
(preprocess
  (pps ppx-simple-example))
```

And then you can use it in your code:

```ocaml
print_endline [%yay]
(* Transforms to *)
print_endline "Hello future compiler engineer!"
```
