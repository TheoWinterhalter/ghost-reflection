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

## Browsing the files

The formalisation can be found in the `theories` folder. We will now go over
all the files it contains.

### Utility

General tactics, lemmas and notations are defined in `Util.v`.

### Syntax

We define the syntax for two languages: the Calculus of Constructions (CC)
and our own Ghost Type Theory (GTT). `BasicAST.v` contains the notion of mode
and of universe levels. `autosubst/CCAST.sig` and `autosubst/GAST.sig` are used
to generate the `autosubst/CCAST.v` and `autosubst/GAST.v` files.
`autosubst/core.v`, `autosubst/unscoped.v` and `SubstNotations.v` contain the
Autosubst library and some notations.

`ContextDecl.v` defines contexts for both theories.

### Ghost Type Theory

| Module            | Description                                |
| :---------------- | :----------------------------------------- |
| `CastRemoval`     | Operation which removes casts from a term. |
| `Scoping`         | Definition of scoping (checks modes)       |
| `TermMode`        | Syntactic computation of mode              |
| `Univ`            | Utility on universes (successor, max…)     |
| `TermNotations`   | Some shorthands for implication and so on… |
| `Typing`          | Conversion and typing judgements           |
| `BasicMetaTheory` | Meta-theory like substitution and validity |

### Calculus of Constructions

| Module         | Description               |
| :------------- | :------------------------ |
| `CScoping`     | Scoping                   |
| `CTyping`      | Typing                    |
| `CCMetaTheory` | Substitution and the like |

### Model

| Module        | Description                                                   |
| :------------ | :------------------------------------------------------------ |
| `Erasure`     | Erasure translation                                           |
| `Revival`     | Revival translation                                           |
| `Param`       | Parametricity translation                                     |
| `Model`       | Consequences of the model                                     |
| `Admissible`  | Simpler typing rules for GTT, assuming injectivity of Π-types |
| `FreeTheorem` | Proof-of-concept free theorem for GTT                         |

### GRTT (theory with reflection of equality)

| Module           | Description                     |
| :--------------- | :------------------------------ |
| `RTyping`        | Typing for GRTT                 |
| `Potential`      | Notion of potential translation |
| `ElimReflection` | Translation from GRTT to GTT    |

### Inductive types

We handle booleans directly in the syntax of GTT and CC, but for natural numbers
and vectors we opted for a different approach: we build the terms directly in
Coq as it is much easier to do. This demonstrates the feasibility of adding them
to the development.

| Module           | Description                         |
| :--------------- | :---------------------------------- |
| `TransNat`       | Erasure and parametricity for `nat` |
| `TransVec`       | Erasure and parametricity for `vec` |

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

The suspicious reader may use `Print Assumptions` on our main theorems to verify
that we do not require any hidden axioms.





[Autosubst 2 OCaml]: https://github.com/uds-psl/autosubst-ocaml
[opam]: https://opam.ocaml.org/
