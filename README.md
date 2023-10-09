
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
mkdir log
dune exec -- gen_haskell -type palka -n 1000 -size 100 > log/things1.hs 2> log/log1.txt
dune exec -- gen_haskell -type not_useless -n 1000 -size 100 > log/things2.hs 2> log/log2.txt
```


to debug:
```
dune utop
...
let Debug.debug_mode := true;;
let p = Generate.generate_fp Generators.main 100 Exp.TyInt in PrettyPrinter.pretty_print p;;
```
