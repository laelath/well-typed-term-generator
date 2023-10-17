
A well-typed program generator framework written in OCaml.



Required:
```
ocaml
dune
utop (opam install utop)
```


to build:
```
dune build
```


to run:
```
dune exec -- gen_haskell -n 1000 -size 15
```


to debug:
```
dune utop
...
let Debug.debug_mode := true;;
let p = Generate.generate_fp (Generators.main (fun x -> 1.)) 100 Type.FlatTyInt in PrettyPrinter.pretty_print p;;
```
