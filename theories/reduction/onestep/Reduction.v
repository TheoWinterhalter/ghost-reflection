(* Definition of reduction rules which corresponds to the congruence relation *)
(* and proof that the system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT Require Export Univ TermNotations Typing.
From GhostTT.reduction Require Export Notations.

Import ListNotations.
Set Default Goal Selector "!".

(* ------------------------------------------------------------------------- *)
Section Rewriting.
  (** rewriting rules **)

  Definition mode_eq : ∀ (x y : mode), { x = y } + { x ≠ y }.
  Proof.
    decide equality.
  Defined.

  Definition red_lvl (m : mode) (i : level) : level :=
    if mode_eq m ℙ then 0 else i.

  Inductive reduction (Γ : scope) : term → term → Prop :=

    (* Computation rules *)

    | red_beta :
        ∀ mx A t t' u u', 
        (mx::Γ) ⊨ t ⤖ t' →
        md Γ u = mx →
        Γ ⊨ u ⤖ u' →
        Γ ⊨ app (lam mx A t) u ⤖ t' <[ u' ·· ]

    | red_reveal_hide :
        ∀ t P p t' p',
        Γ ⊨ t ↣ t' →
        Γ ⊨ p ↣ p' →
        In (md Γ p) [ℙ;𝔾] →
        Γ ⊨ reveal (hide t) P p ↣ app p' t'

    | red_if_true :
        ∀ m P t f t',
        Γ ⊨ t ↣ t' →
        md Γ t = m →
        Γ ⊨ tif m ttrue P t f ↣ t'

    | red_if_false :
        ∀ m P t f f',
        Γ ⊨ f ↣ f' →
        md Γ f = m →
        Γ ⊨ tif m tfalse P t f ↣ f'

    | red_nat_elim_zero :
        ∀ m P z s z',
        Γ ⊨ z ↣ z' →
        md Γ z = m →
        Γ ⊨ tnat_elim m tzero P z s ↣ z'

    | red_nat_elim_succ :
        ∀ m P z s n P' z' s' n',
        Γ ⊨ n ↣ n' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ z ↣ z' →
        Γ ⊨ s ↣ s' →
        md Γ s = m →
        Γ ⊨ tnat_elim m (tsucc n) P z s ↣ app (app s' n') (tnat_elim m n' P' z' s')

    | red_vec_elim_nil :
        ∀ m A B P z s z',
        Γ ⊨ z ↣ z' →
        md Γ z = m →
        Γ ⊨ tvec_elim m A (hide tzero) (tvnil B) P z s ↣ z'

    | red_vec_elim_cons :
        ∀ m A a n n0 v P z s A' a' n' v' P' z' s',
        Γ ⊨ A ↣ A' → 
        Γ ⊨ a ↣ a' →
        Γ ⊨ n ↣ n' →
        Γ ⊨ v ↣ v' → 
        Γ ⊨ P ↣ P' → 
        Γ ⊨ z ↣ z' → 
        Γ ⊨ s ↣ s' →
        md Γ s = m →
        Γ ⊨ tvec_elim m A n0 (tvcons a n v) P z s ↣
        app (app (app (app s' a') (glength A' n' v')) v') (tvec_elim m A' n' v' P' z' s')

        (* Congruence rules *)

        (* A rule to quotient away all levels of Prop, making it impredicatime *)
    | red_Prop :
        ∀ i, Γ ⊨ Sort ℙ i ↣ Sort ℙ 0

    | red_Pi :
        ∀ i j m mx A A' B B',
        Γ ⊨ A ↣ A' →
        (mx::Γ) ⊨ B ↣ B' →
        Γ ⊨ Pi i j m mx A B ↣ Pi (red_lvl mx i) (red_lvl m j) m mx A' B'

    | red_Pi' : (* needed for red_subst *)
        ∀ i j m mx A A' B B',
        Γ ⊨ A ↣ A' →
        (mx::Γ) ⊨ B ↣ B' →
        Γ ⊨ Pi i j m mx A B ↣ Pi i j m mx A' B'

    | red_lam :
        ∀ mx A A' t t',
        Γ ⊨ A ↣ A' →
        (mx::Γ) ⊨ t ↣ t' →
        Γ ⊨ lam mx A t ↣ lam mx A' t'

    | red_app :
        ∀ u u' v v',
        Γ ⊨ u ↣ u' →
        Γ ⊨ v ↣ v' →
        Γ ⊨ app u v ↣ app u' v'

    | red_Erased :
        ∀ A A',
        Γ ⊨ A ↣ A' →
        Γ ⊨ Erased A ↣ Erased A'

    | red_hide :
        ∀ u u',
        Γ ⊨ u ↣ u' →
        Γ ⊨ hide u ↣ hide u'

    | red_reveal :
        ∀ t t' P P' p p',
        Γ ⊨ t ↣ t' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ p ↣ p' →
        Γ ⊨ reveal t P p ↣ reveal t' P' p'

    | red_Reveal :
        ∀ t t' p p',
        Γ ⊨ t ↣ t' →
        Γ ⊨ p ↣ p' →
        Γ ⊨ Reveal t p ↣ Reveal t' p'

    | red_gheq :
        ∀ A A' u u' v v',
        Γ ⊨ A ↣ A' →
        Γ ⊨ u ↣ u' →
        Γ ⊨ v ↣ v' →
        Γ ⊨ gheq A u v ↣ gheq A' u' v'

    | red_if :
        ∀ m b b' P P' t t' f f',
        Γ ⊨ b ↣ b' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ t ↣ t' →
        Γ ⊨ f ↣ f' →
        Γ ⊨ tif m b P t f ↣ tif m b' P' t' f'

    | red_succ :
        ∀ n n',
        Γ ⊨ n ↣ n' →
        Γ ⊨ tsucc n ↣ tsucc n'

    | red_nat_elim :
        ∀ m n n' P P' z z' s s',
        Γ ⊨ n ↣ n' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ z ↣ z' →
        Γ ⊨ s ↣ s' →
        Γ ⊨ tnat_elim m n P z s ↣ tnat_elim m n' P' z' s'

    | red_vec :
        ∀ A A' n n',
        Γ ⊨ A ↣ A' →
        Γ ⊨ n ↣ n' →
        Γ ⊨ tvec A n ↣ tvec A' n'

    | red_vnil :
        ∀ A A',
        Γ ⊨ A ↣ A' →
        Γ ⊨ tvnil A ↣ tvnil A'

    | red_vcons :
        ∀ a a' n n' v v',
        Γ ⊨ a ↣ a' →
        Γ ⊨ n ↣ n' →
        Γ ⊨ v ↣ v' →
        Γ ⊨ tvcons a n v ↣ tvcons a' n' v'

    | red_vec_elim :
        ∀ m A A' n n' v v' P P' z z' s s',
        Γ ⊨ A ↣ A' →
        Γ ⊨ n ↣ n' →
        Γ ⊨ v ↣ v' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ z ↣ z' →
        Γ ⊨ s ↣ s' →
        Γ ⊨ tvec_elim m A n v P z s ↣ tvec_elim m A' n' v' P' z' s'

    | red_bot_elim :
        ∀ m A A' p p',
        Γ ⊨ A ↣ A' →
        Γ ⊨ p ↣ p' →
        Γ ⊨ bot_elim m A p ↣ bot_elim m A' p'

        (* Structural rule *)

    | red_refl :
        ∀ u,
        Γ ⊨ u ↣ u

        (* Proof irrelevance *)

    | red_irr :
        ∀ p,
        md Γ p = ℙ →
        Γ ⊨ p ↣ ⋆

    | red_toRev : 
        ∀ t t' p p' u u',
        Γ ⊨ t ↣ t' →
        Γ ⊨ p ↣ p' →
        Γ ⊨ u ↣ u' →
        Γ ⊨ toRev t p u ↣ toRev t' p' u'

    | red_fromRev :
        ∀ t t' p p' u u',
        Γ ⊨ t ↣ t' →
        Γ ⊨ p ↣ p' →
        Γ ⊨ u ↣ u' →
        Γ ⊨ fromRev t p u ↣ fromRev t' p' u'

    | red_ghrefl :
        ∀ A A' u u',
        Γ ⊨ A ↣ A' →
        Γ ⊨ u ↣ u' →
        Γ ⊨ ghrefl A u ↣ ghrefl A' u'

    | red_ghcast :
        ∀ A A' u u' v v' e e' P P' t t',
        Γ ⊨ A ↣ A' →
        Γ ⊨ u ↣ u' →
        Γ ⊨ v ↣ v' →
        Γ ⊨ e ↣ e' →
        Γ ⊨ P ↣ P' →
        Γ ⊨ t ↣ t' →
        Γ ⊨ ghcast A u v e P t ↣ ghcast A' u' v' e' P' t'


        where "Γ ⊨ u ↣ v" := (reduction Γ u v).


End Rewriting.
Notation "Γ ⊨ u ↣ v" := (reduction Γ u v).

(* ------------------------------------------------------------------------- *)
(** rewriting automation **)
Create HintDb gtt_red discriminated.

Hint Resolve red_beta red_reveal_hide red_if_true red_if_false red_nat_elim_zero
  red_nat_elim_succ red_vec_elim_nil red_vec_elim_cons red_Prop red_Pi
  red_lam red_app red_Erased red_hide red_reveal red_Reveal red_gheq
  red_if red_succ red_nat_elim red_vec red_vnil red_vcons red_vec_elim
  red_bot_elim red_refl red_irr
  red_Pi' red_toRev red_fromRev red_ghrefl red_ghcast
  : gtt_red.

Ltac gred :=
  unshelve typeclasses eauto with gtt_scope gtt_red shelvedb ; shelve_unifiable.
(** end rewriting automation **)
