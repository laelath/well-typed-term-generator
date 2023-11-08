
A well-typed program generator framework written in OCaml.

This repo is under heavy development to create a cohesive interface for writing generators for new languages.

Dependencies:
* OCaml
* Dune

Opam Dependencies:
* `unionFind`


to build:
```
dune build
```


to run:
```
dune exec -- gen_haskell -n 1000 -size 15
```
