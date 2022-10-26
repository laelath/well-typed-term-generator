

Required:
```
opam install utop
dune
ocaml
```


to build:

```
dune build
```


```
dune utop
...
let p = NotUseless.generate_fp 100 Exp.TyInt in PrettyPrinter.pretty_print p;;
let p = NotUseless.generate_fp 100 Exp.TyInt in HaskellPrinter.print p;;
```