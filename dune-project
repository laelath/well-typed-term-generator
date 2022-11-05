(lang dune 3.4)
(name not_useless)

(package
 (name not_useless)
 (depends ocaml dune))

(package
 (name gen_haskell)
 (depends not_useless))
