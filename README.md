# ppxlib-simple-example

A simple ppx to examplify the initial setup of Ppxlib, part of the talk "**The needed introduction to writing a ppx**" given at [Reason STHLM Meetup](https://www.meetup.com/es-ES/ReasonSTHLM/): **[Video](https://youtu.be/dMoRMqQ6GLs?t=4184)**.

## Installation

Needs `esy` installed globally in your system, if you don't have it install it with npm: `npm install -g esy`.

```bash
esy # Installs the dependencies and builds the project
```

## Testing

```bash
esy test # Runs snapshot tests
```

## Editor

It depends on OCaml Language Server installed, so check their docs for more info: https://github.com/ocaml/ocaml-lsp.

## Usage

Users of your ppx need to add this to their dune for your executable to be executed as ppx (or inside bsconfig if targeting ReScript).

```lisp
(preprocess
  (pps simple-ppx))
```

```reason
print_endline([%yay]);
// Transforms to
print_endline("🎉");
```