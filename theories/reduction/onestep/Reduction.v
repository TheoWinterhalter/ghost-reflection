(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST.
From GhostTT Require Import SubstNotations Typing.
From GhostTT.reduction Require Export Notations Utils.
From GhostTT.reduction.wrapping Require Export Core Notations.

Set Default Goal Selector "!".

(* ------------------------------------------------------------------------- *)
Inductive reduction : term → term → Prop :=

  (* Computation rules *)

  | red_beta :
      ∀ mx A t u, 
      app (lam mx A t) u ↣ t <[ u ·· ]

  | red_reveal_hide :
      ∀ t P p, 
      reveal (hide t) P p ↣ app p t

  | red_if_true :
      ∀ m P t f, tif m ttrue P t f ↣ t

  | red_if_false :
      ∀ m P t f, tif m tfalse P t f ↣ f

  | red_nat_elim_zero :
      ∀ m P z s, tnat_elim m tzero P z s ↣ z

  | red_nat_elim_succ :
      ∀ m P z s n,
      tnat_elim m (tsucc n) P z s ↣ app (app s n) (tnat_elim m n P z s)

  | red_vec_elim_nil :
      ∀ m A B P z s,
      tvec_elim m A (hide tzero) (tvnil B) P z s ↣ z

  | red_vec_elim_cons :
      ∀ m A a n n0 v P z s,
      tvec_elim m A n0 (tvcons a n v) P z s ↣
      app (app (app (app s a) (glength A n v)) v) (tvec_elim m A n v P z s)

  | red_Prop :
      ∀ i, Sort ℙ i ↣ Sort ℙ 0

  | red_Pi :
      ∀ i j m mx A B,
      Pi i j m mx A B ↣ Pi (red_lvl mx i) (red_lvl m j) m mx A B

  | red_subterm : ∀ u u' C,
      u ↣ u' →
      C[□/u] ↣ C[□/u']

      where "u ↣ v" := (reduction u v).

(* ------------------------------------------------------------------------- *)
