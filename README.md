

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
dune exec -- gen_haskell -n 1000 -size 100 > things.hs 2> log
```


to debug:
```
dune utop
...
let debug_mode := true;;
let p = Generate.generate_fp Generators.main 100 Exp.TyInt in PrettyPrinter.pretty_print p;;
```




notes:
When calling `ghc`, use `-Wno-overlapping-patterns`.
