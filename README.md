# ppxlib-simple-example

A simple ppx to examplify the initial setup of Ppxlib, part of the talk "**The needed introduction to writing a ppx**" given at [Reason STHLM Meetup](https://www.meetup.com/es-ES/ReasonSTHLM/): **[Video](https://youtu.be/dMoRMqQ6GLs?t=4184)**.

- OCaml 4.14
- dune 3.4.1
- ppxlib 0.27

## Installation

Needs `esy` installed globally in your system, if you don't have it install it with npm: `npm install -g esy`.

```bash
esy # Installs the dependencies and builds the project
```

## Testing

```bash
esy test # Runs alcotest tests
```

## Usage

Users of your ppx need to add this to their dune for your executable to be executed as ppx (or inside bsconfig if targeting ReScript).

```lisp
(preprocess
  (pps simple-ppx))
```

```ocaml
print_endline [%yay];
// Transforms to
print_endline("r3p14ccd 70 r4nd0m 5tr1n9");
```
