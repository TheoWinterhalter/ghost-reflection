Formalisation of the "Dependent Ghosts Have a Reflection For Free" paper
========================================================================

### Utility

General tactics, lemmas and notations are defined in
[Util](coqdoc/GhostTT.Util.html).

### Syntax

We define the syntax for two languages: the Calculus of Constructions (CC)
and our own Ghost Type Theory (GTT). [BasicAST] contains the notion of mode
and of universe levels. `autosubst/CCAST.sig` and `autosubst/GAST.sig` are used
to generate the [autosubst/CCAST] and [autosubst/GAST] modules.
[autosubst/core], [autosubst/unscoped] and [SubstNotations] contain the
Autosubst library and some notations.

[ContextDecl] defines contexts for both theories.

[BasicAST]: coqdoc/GhostTT.BasicAST.html
[autosubst/CCAST]: coqdoc/GhostTT.autosubst.CCAST.html
[autosubst/GAST]: coqdoc/GhostTT.autosubst.GAST.html
[autosubst/core]: coqdoc/GhostTT.autosubst.core.html
[autosubst/unscoped]: coqdoc/GhostTT.autosubst.unscoped.html
[SubstNotations]: coqdoc/GhostTT.SubstNotations.html
[ContextDecl]: coqdoc/GhostTT.ContextDecl.html

### Ghost Type Theory

| Module            | Description                                |
| :---------------- | :----------------------------------------- |
| [CastRemoval]     | Operation which removes casts from a term. |
| [Scoping]         | Definition of scoping (checks modes)       |
| [TermMode]        | Syntactic computation of mode              |
| [Univ]            | Utility on universes (successor, max…)     |
| [TermNotations]   | Some shorthands for implication and so on… |
| [Typing]          | Conversion and typing judgements           |
| [BasicMetaTheory] | Meta-theory like substitution and validity |

[CastRemoval]: coqdoc/GhostTT.CastRemoval.html
[Scoping]: coqdoc/GhostTT.Scoping.html
[TermMode]: coqdoc/GhostTT.TermMode.html
[Univ]: coqdoc/GhostTT.Univ.html
[TermNotations]: coqdoc/GhostTT.TermNotations.html
[Typing]: coqdoc/GhostTT.Typing.html
[BasicMetaTheory]: coqdoc/GhostTT.BasicMetaTheory.html

### Calculus of Constructions

| Module         | Description               |
| :------------- | :------------------------ |
| [CScoping]     | Scoping                   |
| [CTyping]      | Typing                    |
| [CCMetaTheory] | Substitution and the like |

[CScoping]: coqdoc/GhostTT.CScoping.html
[CTyping]: coqdoc/GhostTT.CTyping.html
[CCMetaTheory]: coqdoc/GhostTT.CCMetaTheory.html

### Model

| Module        | Description                                                   |
| :------------ | :------------------------------------------------------------ |
| [Erasure]     | Erasure translation                                           |
| [Revival]     | Revival translation                                           |
| [Param]       | Parametricity translation                                     |
| [Model]       | Consequences of the model                                     |
| [Admissible]  | Simpler typing rules for GTT, assuming injectivity of Π-types |
| [FreeTheorem] | Proof-of-concept free theorem for GTT                         |

[Erasure]: coqdoc/GhostTT.Erasure.html
[Revival]: coqdoc/GhostTT.Revival.html
[Param]: coqdoc/GhostTT.Param.html
[Model]: coqdoc/GhostTT.Model.html
[Admissible]: coqdoc/GhostTT.Admissible.html
[FreeTheorem]: coqdoc/GhostTT.FreeTheorem.html

### GRTT (theory with reflection of equality)

| Module           | Description                     |
| :--------------- | :------------------------------ |
| [RTyping]        | Typing for GRTT                 |
| [Potential]      | Notion of potential translation |
| [ElimReflection] | Translation from GRTT to GTT    |

[RTyping]: coqdoc/GhostTT.RTyping.html
[Potential]: coqdoc/GhostTT.Potential.html
[ElimReflection]: coqdoc/GhostTT.ElimReflection.html

### Inductive types

We handle booleans directly in the syntax of GTT and CC, but for natural numbers
and vectors we opted for a different approach: we build the terms directly in
Coq as it is much easier to do. We then assume constants in CC with
exactly the types we inhabit in `TransNat` and `TransVec`.

| Module           | Description                         |
| :--------------- | :---------------------------------- |
| [TransNat]       | Erasure and parametricity for `nat` |
| [TransVec]       | Erasure and parametricity for `vec` |

[TransNat]: coqdoc/GhostTT.TransNat.html
[TransVec]: coqdoc/GhostTT.TransVec.html
