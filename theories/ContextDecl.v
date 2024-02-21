From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST CCAST.
From GhostTT Require Import BasicAST.

Set Primitive Projections.

(** Contexts store for each variable its type and mode.

  The mode is redundant information already contained in the type, but we only
  establish that later. Storing this information is useful to perform syntactic
  transformations: typically conversion and the syntactic model.

**)

Notation decl := (mode * term)%type.

Notation context := (list decl).

Notation scope := (list mode).

Definition sc (Γ : context) : scope :=
  map fst Γ.

Notation "'∙'" :=
  (@nil decl).

Notation "Γ ,, d" :=
  (@cons decl d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@app decl Δ Γ) (at level 25, Δ at next level, left associativity).

(** Flex declartions for CC

  Variable handling is going to become much more complicated because erasure
  removes some variables, while parametricity adds some in a non-uniform way
  so computing offsets and weakenings will be painful arithmetic.
  We propose to use flexible contexts that instead of one declaration per
  position can have zero or one.

  We could also consider having a final translation to get rid of those but
  we argue that it is not necessary.

 **)

Notation cdecl := (cmode * cterm)%type.

Notation ccontext := (list (option cdecl)).

Notation cscope := (list (option cmode)).

Definition csc (Γ : ccontext) : cscope :=
  map (option_map fst) Γ.

(* TODO MOVE *)
Definition option_bind {A B} (o : option A) (f : A → option B) :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition whenSome {A} (P : A → Prop) (o : option A) :=
  match o with
  | Some x => P x
  | None => True
  end.
