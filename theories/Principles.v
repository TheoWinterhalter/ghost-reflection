(*** Testing principles obtained from parametricity ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl
  Scoping TermMode CastRemoval Typing BasicMetaTheory CTyping CCMetaTheory
  Admissible Erasure Revival Param Model.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** f : erased bool → bool has to be the constant function

  But do we get that from parametricity?
  It seems what we get for such an f is
  ∀ (b : ebool) (bP : pbool b), pbool ⟦ f ⟧ε

  This looks promising, maybe I should define some form of boolean equality?
  Like bool_eq b b' := if b then (if b' then True else False) else False.
  Maybe with True := False → False.

**)

Transparent close ignore epm_lift rpm_lift.

Eval lazy in  ⟦ [] | Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool ⟧p.

Definition cst_ty :=
  Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool.

Lemma erase_bool :
  ∀ f,
    [] ⊢ᶜ capp ⟦ [] | cst_ty ⟧p f ≡
    cPi cType ebool (cPi cProp (capp pbool (cvar 0)) (capp pbool (S ⋅ S ⋅ f))).
Proof.
  intros f.
  cbn. unfold pmPiNP. cbn. eapply cconv_trans. 1: constructor.
  cbn. econv.
Qed.

Lemma constant_bool :
  ∀ f,
    [] ⊢ f : Erased tbool ⇒[ 0 | 0 / mGhost | mType ] tbool →
    True.
Proof.
  intros f hf.
  eapply mode_coherence in hf as hm. 2: constructor.
  2:{ econstructor. all: repeat constructor. }
  eapply param_typing in hf as hfP.
  unfold ptype in hfP. remd in hfP. simpl relm in hfP. cbn match in hfP.
  eapply ctype_conv in hfP.
  2: eapply erase_bool.
  2:{ ertype. all: admit. }
Abort.

Definition bool_eq b b' :=
  tif mProp b (lam mType tbool (Sort mType 0) (Sort mProp 0))
    (* then *) (
      tif mProp b' (lam mType tbool (Sort mType 0) (Sort mProp 0))
        (* then *) top
        (* else *) bot
    )
    (* else *) bot.

Lemma constant_bool :
  ∑ prf,
    [] ⊢ᶜ prf : ⟦ [] |
      Pi 0 0 mProp mType cst_ty (
        bool_eq (app (var 0) ttrue) (app (var 0) tfalse)
      )
    ⟧p.
Proof.
  (* cbn - [cst_ty].
  eexists. eapply ctype_conv.
  2:{
    apply cconv_sym. eapply ccong_pPi.
    - cbn. eapply cconv_trans. 1: constructor.
      constructor.
    - apply erase_bool.
    -
  } *)
  cbn.
  eexists. eapply ctype_conv.
  2:{
    apply cconv_sym. eapply ccong_pPi.
    - eapply cconv_trans. 1: constructor.
      constructor.
    - unfold pmPiNP. econstructor.
      + eapply cconv_trans. 1: constructor. constructor.
      + cbn. eapply ccong_pPi.
        * constructor.
        * constructor.
        * econv.
    - econstructor.
      + econv.
      + eapply ccong_plam. 1: constructor. all: econv.
      + econstructor.
        * econv.
        * eapply ccong_plam. 1: constructor. all: econv.
        * econv.
        * econv.
      + econv.
  }
  2: admit.
  (*
    ∀ (b : ebool) (bP : pbool b)
  *)
  eapply type_plam. 1,2: ertype.
  1:{
    eapply ccmeta_conv.
    - ertype. eapply ccmeta_conv. 1: ertype.
      reflexivity.
    - cbn. reflexivity.
  }
Abort.
