# Formalisation of the "Dependent Ghosts Have a Reflection For Free" submission

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

## Browsing the files

The formalisation can be found in the `theories` folder.
The library is explained in `doc/index.md`.
An HTML version of the formalisation can be found in the `doc/coqdoc` folder.

### Statistics

The formalisation (excluding Autosubst generated files) spans little under
18,000 lines of code. Autosubsts generates a little over 11,000 lines.

## Assumptions

You will find only two axioms in the whole development. Both are found in the
`Model` file. The first one assumes injectivity of the `ctyval` constructor of
CC. This is a very natural assumption to make as we know it holds for Coq.
The second is injectivity of Π-types for GTT. Sadly, our model is insufficient
to derive it but we conjecture it holds as it concerns a conversion that is
very close to that of CC which enjoys the property.

The only part of the development which may use those axioms is the admissible
rules and the GRTT to GTT translation which uses those rules. We also conjecture
it could be done without, albeit with longer proofs.

We provide a file `Assumptions.v` with reference to all lemmas of the
submissions. It uses `Print Assumptions` on all of them which has the effect
of printing the list of axioms used for each one.
You may run `make clean-assumptions` and then `make` again if you wish to only
check assumptions (after the project has been fully built).





[Autosubst 2 OCaml]: https://github.com/uds-psl/autosubst-ocaml
[opam]: https://opam.ocaml.org/
