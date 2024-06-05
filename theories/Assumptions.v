(** This file checks assumptions of all the lemmas of the submission **)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory Admissible RTyping
  Potential Model FreeTheorem ElimReflection.

(* Lemma 2.1 *)
Print Assumptions BasicMetaTheory.scoping_subst.

(* Lemma 2.2 *)
Print Assumptions BasicMetaTheory.scoping_castrm.

(* Lemma 2.3 *)
Print Assumptions BasicMetaTheory.castrm_subst.

(* Lemma 2.4 *)
Print Assumptions BasicMetaTheory.conv_md.

(* Lemma 2.5 *)
Print Assumptions BasicMetaTheory.typing_subst.

(* Lemma 2.6 *)
Print Assumptions BasicMetaTheory.validity.

(* Lemma 3.1 *)
Print Assumptions Erasure.erase_subst.

(* Lemma 3.2 *)
Print Assumptions Erasure.erase_castrm.

(* Lemma 3.3 *)
Print Assumptions Erasure.erase_typing.
Print Assumptions Erasure.erase_conv.
Print Assumptions Erasure.erase_context.

(* Lemma 3.4 *)
Print Assumptions Revival.type_to_rev.

(* Lemma 3.5 *)
Print Assumptions Revival.revive_subst.

(* Lemma 3.6 *)
Print Assumptions Revival.revive_castrm.

(* Lemma 3.7 *)
Print Assumptions Revival.revive_typing.
Print Assumptions Revival.revive_conv.
Print Assumptions Revival.revive_context.

(* Lemma 3.8 *)
Print Assumptions Param.typing_rev_sub_param.
Print Assumptions Param.typing_er_sub_param.

(* Lemma 3.9 *)
Print Assumptions Param.param_subst.

(* Lemma 3.10 *)
Print Assumptions Param.param_scoping.

(* Lemma 3.11 *)
Print Assumptions Param.param_castrm.

(* Lemma 3.12 *)
Print Assumptions Param.param_typing.
Print Assumptions Param.param_conv.
Print Assumptions Param.param_context.

(* Theorem 4.1 *)
Print Assumptions Model.relative_consistency.

(* Lemma 4.4 *)
Print Assumptions Model.mode_coherence.

(* Free theorem *)
Print Assumptions FreeTheorem.constant_free_theorem.

(* Lemma 6.1 *)
Print Assumptions Potential.tr_choice.

(* Lemma 6.2 *)
Print Assumptions Potential.tr_sort_eq.
Print Assumptions Potential.tr_bot_eq.

(* Theorem 6.3 *)
Print Assumptions ElimReflection.elim_reflection.
Print Assumptions ElimReflection.elim_ctx.

(* Theorem 6.4 *)
Print Assumptions ElimReflection.conservativity.

(* Theorem 6.5 *)
Print Assumptions ElimReflection.consistency.
