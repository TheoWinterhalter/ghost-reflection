(** GAST support for rasimpl **)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import core unscoped GAST CCAST RAsimpl.
From Coq Require Import Setoid Morphisms Relation_Definitions.
Import ListNotations.

(* GAST *)
#[export] Hint Unfold
  VarInstance_term Ren_term Up_term_term Up_term up_term Subst_term
  upRen_term_term up_term_term
  : asimpl_unfold.
