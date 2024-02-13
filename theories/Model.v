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

(** Type former discrimination in the target

  We assume that the target is able to distinguish the various type formers.
  For instance an arrow type can't be convertible to unit.

**)

Inductive ctf_head :=
| chSort (m : cmode) (i : level)
| chPi
| chunit
| chtop
| chbot
| chty
| chsquash
| chteq.

Definition chead (t : cterm) : option ctf_head :=
  match t with
  | cSort m i => Some (chSort m i)
  | cPi mx A B => Some chPi
  | cunit => Some chunit
  | ctop => Some chtop
  | cbot => Some chbot
  | cty i => Some chty
  | squash _ => Some chsquash
  | teq _ _ _ => Some chteq
  | _ => None
  end.

Definition cc_tf_discr :=
  ∀ Γ A B hA hB,
    chead A = Some hA →
    chead B = Some hB →
    Γ ⊢ᶜ A ≡ B →
    hA = hB.

(** Relative consistency **)

Definition cc_consistency :=
  ¬ (∃ t, [] ⊢ᶜ t : cbot).

Definition gtt_consistency :=
  ¬ (∃ t, [] ⊢ t : bot).

Theorem relative_consistency :
  cc_tf_discr →
  cc_consistency →
  gtt_consistency.
Proof.
  intros hdiscr hcons.
  intros [t ht].
  eapply hcons.
  apply param_typing in ht as htp.
  cbn in htp. unfold ptype in htp. cbn - [mode_inb] in htp.
  eapply validity in ht as h. 2: constructor.
  destruct h as [hs [i h]].
  ttinv h h'. cbn in h'.
  apply erase_conv in h'. cbn in h'.
  remember (md [] t) as m eqn:em in *.
  destruct (isProp m) eqn:e.
  2:{
    eapply ccong_El in h'.
    eapply cconv_trans in h'. 2:{ apply cconv_sym. constructor. }
    apply cconv_sym in h'.
    eapply cconv_trans in h'. 2:{ apply cconv_sym. constructor. }
    eapply hdiscr in h'. 2,3: reflexivity.
    discriminate.
  }
  clear em. mode_eqs. cbn in htp.
  eexists. eassumption.
Qed.
