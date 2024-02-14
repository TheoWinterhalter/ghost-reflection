(*** Consequences of the model ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival Param.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Injectivity of type formers and constructors in CC

  We assume that the target enjoys injectivity of constructors of inductive
  types and of type formers. We will only state what we need though.
  We take them as axioms to avoid having to develop the full meta-theory of
  CC, which would defeat the purpose of using it as a model.

**)

Axiom ctyval_inj :
  ∀ Γ mk mk' A A' a a',
    Γ ⊢ᶜ ctyval mk A a ≡ ctyval mk' A' a' →
    mk = mk' ∧
    Γ ⊢ᶜ A ≡ A' ∧
    Γ ⊢ᶜ a ≡ a'.

(** Deduced injectivity in GTT **)

(** Injectivity of sort modes **)

Lemma sort_mode_inj :
  ∀ Γ m m' i i',
    Γ ⊢ Sort m i ≡ Sort m' i' →
    m = m'.
Proof.
  intros Γ m m' i i' h.
  eapply erase_conv in h as he. cbn in he.
  destruct m, m'. all: try reflexivity. all: exfalso. all: cbn in he.
  all: solve [ eapply ctyval_inj in he ; intuition discriminate ].
Qed.

(** Relative consistency **)

Definition cc_consistency :=
  ¬ (∃ t, [] ⊢ᶜ t : cbot).

Definition gtt_consistency :=
  ¬ (∃ t, [] ⊢ t : bot).

Theorem relative_consistency :
  cc_consistency →
  gtt_consistency.
Proof.
  intros hcons. intros [t ht].
  eapply hcons.
  apply param_typing in ht as htp.
  cbn in htp. unfold ptype in htp. cbn - [mode_inb] in htp.
  eapply validity in ht as h. 2: constructor.
  destruct h as [hs [i h]].
  ttinv h h'. cbn in h'.
  eapply sort_mode_inj in h'.
  remember (md [] t) as m eqn:em in *. clear em. subst.
  cbn in htp.
  eexists. eassumption.
Qed.
