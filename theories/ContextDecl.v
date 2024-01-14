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
  I propose to use flexible contexts that instead of one declaration per
  position will have zero, one or two. A variable in the target will thus be
  a position in the context, plus a role corresponding to how the variable is
  used, be it as a regular or a parametricity variable.

  This idea should work for all kinds of translations and is particularly suited
  to combination of several translations like we do here.

  TODO: Mention this idea of flexible variables in the paper.

  We can also consider having a final translation to get rid of those but
  this will be much nicer probably, we separate matters nicely.
  I would argue though that we don't really need it.

 **)

Notation cdecl := (cmode * cterm)%type.

(* Flex declaration *)
Record flex decl := {
  freg : option decl ;
  fprm : option decl
}.

Arguments freg {decl}.
Arguments fprm {decl}.

Definition map_flex {d d'} (f : d → d') (c : flex d) : flex d' := {|
  freg := option_map f c.(freg) ;
  fprm := option_map f c.(fprm)
|}.

Notation ccontext := (list (flex cdecl)).

Notation cscope := (list (flex cmode)).

Definition csc (Γ : ccontext) : cscope :=
  map (map_flex fst) Γ.

Definition fget {d} (r : role) (decl : flex d) : option d :=
  match r with
  | reg => decl.(freg)
  | prm => decl.(fprm)
  end.

(* TODO MOVE *)
Definition option_bind {A B} (o : option A) (f : A → option B) :=
  match o with
  | Some x => f x
  | None => None
  end.

  Definition skip {A} : flex A := {|
    freg := None ;
    fprm := None
  |}.

Definition mreg m : flex cmode := {|
  freg := Some m ;
  fprm := None
|}.

Definition dreg m A : flex cdecl := {|
  freg := Some (m, A) ;
  fprm := None
|}.

(** A bit out of place, but useful definitions for flex variables **)

Definition cvar (r : role) (x : nat) :=
  cvar_proj r (_cvar x).
