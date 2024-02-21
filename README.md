# Formalisation of the "Dependent Ghosts Have a Reflection For Free" paper

## Building the syntax (optional)

We build the syntax of our type theories using [Autosubst 2 OCaml].
When we prepared this supplementary material there was no Coq 8.18 version for
this package so we provide instead the generated file directly in this
repository.

**Note: The generated files include comments that are not anonymised. They are
however unrelated to the current submission and thus do not breach anonymity.**

In the event you would like to build the syntax files, you can checkout the
`coq-8.13` branch of [Autosubst 2 OCaml] and run
```
dune build
dune install
```

Once installed, you can run `make` in the `theories/autosubst` directory. It
will generate `GAST.v`, `CCAST.v`, `unscoped.v` and `core.v`.

## Building the project

We use Coq 8.18 and Equations 1.3.
You can get Coq and Equations using [opam] as follows:

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin add coq 8.18.0
opam install coq-equations
```

Running `make` at the root of the project is enough to build everything.
It should compile without warnings or errors. The `Param` module takes a while
to build.



[Autosubst 2 OCaml]: https://github.com/uds-psl/autosubst-ocaml
[opam]: https://opam.ocaml.org/
