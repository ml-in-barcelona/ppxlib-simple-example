# ppxlib-simple-example

A simple ppx to examplify the initial setup of [ppxlib](https://github.com/ocaml-ppx/ppxlib/), part of the talk [**The needed introduction to writing a ppx**](https://youtu.be/dMoRMqQ6GLs?t=4184) given at [Reason STHLM Meetup](https://www.meetup.com/es-ES/ReasonSTHLM/)..

It uses [`esy`](https://esy.sh) since it's a little easier to install sandboxes enviroments than opam.

- OCaml 4.14
- dune 3.4.1
- ppxlib 0.27

## Installation

```bash
opam install .
```

## Building

```bash
dune build
```

## Testing

```bash
dune test
```


