

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
let p = NotUseless.generate_fp 100 Exp.TyInt in PrettyPrinter.pretty_print p;;
let p = NotUseless.generate_fp 100 Exp.TyInt in HaskellPrinter.print p;;
```


notes:
When calling `ghc`, use `-Wno-overlapping-patterns`.
