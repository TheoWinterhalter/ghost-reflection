# ghost-reflection

## Building syntax

This requires installing AutoSubst 2 OCaml which can only be run with Coq 8.13.
You can just run `make` in the `theories/autosubst` directory. It will generate
`AST.v` (which is also versioned because it's an annoying step).

To avoid running into errors, just checkout AutoSubst 2 Ocaml's coq8.13 branch
and run
```
dune build
dune install
```

We also change slightly the imports to the file so that it works.
