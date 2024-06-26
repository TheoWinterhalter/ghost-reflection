(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping.
From GhostTT Require Export Univ TermNotations Typing.
From GhostTT.reduction Require Export Notations Utils.

Import ListNotations.
Set Default Goal Selector "!".


Inductive box_term_1 : Set := 
  | Box_Pi_1 : level → level → mode → mode → term → box_term_1
  | Box_lam_1 : mode → term → box_term_1
  | Box_app_1 : term → box_term_1
  | Box_app_2 : term → box_term_1
  | Box_Erased : box_term_1
  | Box_hide : box_term_1
  | Box_reveal_1 : term → term → box_term_1
  | Box_reveal_2 : term → term → box_term_1
  | Box_reveal_3 : term → term → box_term_1
  | Box_Reveal_1 : term → box_term_1
  | Box_Reveal_2 : term → box_term_1
  | Box_toRev_1 : term → term → box_term_1
  | Box_toRev_2 : term → term → box_term_1
  | Box_toRev_3 : term → term → box_term_1
  | Box_fromRev_1 : term → term → box_term_1
  | Box_fromRev_2 : term → term → box_term_1
  | Box_fromRev_3 : term → term → box_term_1
  | Box_gheq_1 : term → term → box_term_1
  | Box_gheq_2 : term → term → box_term_1
  | Box_gheq_3 : term → term → box_term_1
  | Box_ghrefl_1 : term → box_term_1
  | Box_ghrefl_2 : term → box_term_1
  | Box_ghcast_1 : term → term → term → term → term → box_term_1
  | Box_ghcast_2 : term → term → term → term → term → box_term_1
  | Box_ghcast_3 : term → term → term → term → term → box_term_1
  | Box_ghcast_4 : term → term → term → term → term → box_term_1
  | Box_ghcast_5 : term → term → term → term → term → box_term_1
  | Box_ghcast_6 : term → term → term → term → term → box_term_1
  | Box_tif_1 : mode → term → term → term → box_term_1
  | Box_tif_2 : mode → term → term → term → box_term_1
  | Box_tif_3 : mode → term → term → term → box_term_1
  | Box_tif_4 : mode → term → term → term → box_term_1
  | Box_tsucc : box_term_1
  | Box_tnat_elim_1 : mode → term → term → term → box_term_1
  | Box_tnat_elim_2 : mode → term → term → term → box_term_1
  | Box_tnat_elim_3 : mode → term → term → term → box_term_1
  | Box_tnat_elim_4 : mode → term → term → term → box_term_1
  | Box_tvec_1 : term → box_term_1
  | Box_tvec_2 : term → box_term_1
  | Box_tvnil : box_term_1
  | Box_tvcons_1 : term → term → box_term_1
  | Box_tvcons_2 : term → term → box_term_1
  | Box_tvcons_3 : term → term → box_term_1
  | Box_tvec_elim_1 : mode → term → term → term → term → term → box_term_1
  | Box_tvec_elim_2 : mode → term → term → term → term → term → box_term_1
  | Box_tvec_elim_3 : mode → term → term → term → term → term → box_term_1
  | Box_tvec_elim_4 : mode → term → term → term → term → term → box_term_1
  | Box_tvec_elim_5 : mode → term → term → term → term → term → box_term_1
  | Box_tvec_elim_6 : mode → term → term → term → term → term → box_term_1
  | Box_bot_elim_1 : mode → term → box_term_1
  | Box_bot_elim_2 : mode → term → box_term_1.

Inductive box_term_2 : Set :=
  | Box_Pi_2 : level → level → mode → mode → term → box_term_2
  | Box_lam_2 : mode → term → box_term_2.

Inductive box_term : Set :=
  | Box_1 : box_term_1 → box_term
  | Box_2 : box_term_2 → box_term.

Definition eval_box_term (C : box_term) (t0: term) : term :=
  match C with 
  | Box_1 (Box_Pi_1 i j m mx B) => Pi i j m mx t0 B
  | Box_2 (Box_Pi_2 i j m mx A) => Pi i j m mx A t0
  | Box_1 (Box_lam_1 m t) => lam m t0 t
  | Box_2 (Box_lam_2 m A) => lam m A t0
  | Box_1 (Box_app_1 v) => app t0 v
  | Box_1 (Box_app_2 u) => app u t0
  | Box_1 (Box_Erased) => Erased t0
  | Box_1 (Box_hide) => hide t0
  | Box_1 (Box_reveal_1 P p) => reveal t0 P p
  | Box_1 (Box_reveal_2 t p) => reveal t t0 p
  | Box_1 (Box_reveal_3 t P) => reveal t P t0
  | Box_1 (Box_Reveal_1 p) => Reveal t0 p
  | Box_1 (Box_Reveal_2 t) => Reveal t t0
  | Box_1 (Box_toRev_1 p u) => toRev t0 p u
  | Box_1 (Box_toRev_2 t u) => toRev t t0 u
  | Box_1 (Box_toRev_3 t p) => toRev t p t0
  | Box_1 (Box_fromRev_1 p u) => fromRev t0 p u
  | Box_1 (Box_fromRev_2 t u) => fromRev t t0 u
  | Box_1 (Box_fromRev_3 t p) => fromRev t p t0
  | Box_1 (Box_gheq_1 u V) => gheq t0 u V
  | Box_1 (Box_gheq_2 a V) => gheq a t0 V
  | Box_1 (Box_gheq_3 a u) => gheq a u t0
  | Box_1 (Box_ghrefl_1 u) => ghrefl t0 u
  | Box_1 (Box_ghrefl_2 A) => ghrefl A t0
  | Box_1 (Box_ghcast_1 u v e P t) => ghcast t0 u v e P t
  | Box_1 (Box_ghcast_2 A v e P t) => ghcast A t0 v e P t
  | Box_1 (Box_ghcast_3 A u e P t) => ghcast A u t0 e P t
  | Box_1 (Box_ghcast_4 A u v P t) => ghcast A u v t0 P t
  | Box_1 (Box_ghcast_5 A u v e t) => ghcast A u v e t0 t
  | Box_1 (Box_ghcast_6 A u v e P) => ghcast A u v e P t0
  | Box_1 (Box_tif_1 m P t f) => tif m t0 P t f
  | Box_1 (Box_tif_2 m b t f) => tif m b t0 t f
  | Box_1 (Box_tif_3 m b P f) => tif m b P t0 f
  | Box_1 (Box_tif_4 m b P t) => tif m b P t t0
  | Box_1 (Box_tsucc) => tsucc t0
  | Box_1 (Box_tnat_elim_1 m P z s) => tnat_elim m t0 P z s
  | Box_1 (Box_tnat_elim_2 m n z s) => tnat_elim m n t0 z s
  | Box_1 (Box_tnat_elim_3 m n P s) => tnat_elim m n P t0 s
  | Box_1 (Box_tnat_elim_4 m n P z) => tnat_elim m n P z t0
  | Box_1 (Box_tvec_1 n) => tvec t0 n
  | Box_1 (Box_tvec_2 A) => tvec A t0
  | Box_1 (Box_tvnil) => tvnil t0
  | Box_1 (Box_tvcons_1 n v) => tvcons t0 n v
  | Box_1 (Box_tvcons_2 a v) => tvcons a t0 v
  | Box_1 (Box_tvcons_3 a n) => tvcons a n t0
  | Box_1 (Box_tvec_elim_1 m n v P z s) => tvec_elim m t0 n v P z s 
  | Box_1 (Box_tvec_elim_2 m A v P z s) => tvec_elim m A t0 v P z s 
  | Box_1 (Box_tvec_elim_3 m A n P z s) => tvec_elim m A n t0 P z s 
  | Box_1 (Box_tvec_elim_4 m A n v z s) => tvec_elim m A n v t0 z s 
  | Box_1 (Box_tvec_elim_5 m A n v P s) => tvec_elim m A n v P t0 s 
  | Box_1 (Box_tvec_elim_6 m A n v P z) => tvec_elim m A n v P z t0 
  | Box_1 (Box_bot_elim_1 m p) => bot_elim m t0 p
  | Box_1 (Box_bot_elim_2 m A) => bot_elim m A t0
  end.

Definition context_box_term (Γ: context) (C : box_term) : context :=
  match C with 
  | Box_1 _ => Γ
  | Box_2 (Box_Pi_2 i j m mx A) => (Γ,, (mx,A))
  | Box_2 (Box_lam_2 m A) => (Γ,, (m,A))
  end.

Definition scope_box_term (Γ: scope) (C : box_term) : scope :=
  match C with 
  | Box_1 _ => Γ
  | Box_2 (Box_Pi_2 i j m mx A) => mx::Γ
  | Box_2 (Box_lam_2 m A) => m::Γ
  end.

Notation "□¹_term" := box_term_1.
Notation "□²_term" := box_term_2.
Notation "□_term" := box_term.
Notation "C □ t" := (eval_box_term C t) (at level 70).
Notation "C □¹ t" := (eval_box_term (Box_1 C) t) (at level 70).
Notation "C □² t" := (eval_box_term (Box_2 C) t) (at level 70).

Notation "[ Γ ] □ C" := (context_box_term Γ C) (at level 70).
Notation "[| Γ |] □ C" := (scope_box_term Γ C) (at level 70).

Notation "Γ □ C ⊢ t : A" := (typing (context_box_term Γ C) t A) 
  (at level 80, t, A at next level, format "Γ □ C ⊢ t : A", only printing).
Notation "Γ □ C ⊢ t ∷ m" := (scoping (sc (context_box_term Γ C)) t m) 
  (at level 80, t, m at next level, format "Γ □ C ⊢ t ∷ m", only printing).
Notation "Γ □ C ⊨ t ∷ m" := (scoping (scope_box_term Γ C) t m) 
  (at level 80, t, m at next level, format "Γ □ C ⊨ t ∷ m", only printing).

