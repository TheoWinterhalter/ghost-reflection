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

(** Uniqueness of typing

  We show a restricted form of uniqueness ignoring universe levels.
  This way we do not rely on the absence of cumulativity.

  In order to do this, we build a function which puts all universes to 0.

**)

Fixpoint urm (t : term) : term :=
  match t with
  | var x => var x
  | Sort m i => Sort m 0
  | Pi i j m mx A B => Pi 0 0 m mx (urm A) (urm B)
  | lam mx A B t => lam mx (urm A) (urm B) (urm t)
  | app u v => app (urm u) (urm v)
  | Erased A => Erased (urm A)
  | hide t => hide (urm t)
  | reveal t P p => reveal (urm t) (urm P) (urm p)
  | Reveal t P => Reveal (urm t) (urm P)
  | toRev t p u => toRev (urm t) (urm p) (urm u)
  | fromRev t p u => fromRev (urm t) (urm p) (urm u)
  | gheq A u v => gheq (urm A) (urm u) (urm v)
  | ghrefl A u => ghrefl (urm A) (urm u)
  | ghcast A u v e P t => ghcast (urm A) (urm u) (urm v) (urm e) (urm P) (urm t)
  | bot => bot
  | bot_elim m A p => bot_elim m (urm A) (urm p)
  end.

Notation "Γ ⊢ u ≈ v" :=
  (Γ ⊢ ε| urm u | ≡ ε| urm v |)
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≈  v").

Lemma urm_ren :
  ∀ t ρ,
    urm (ρ ⋅ t) = ρ ⋅ (urm t).
Proof.
  intros t ρ.
  induction t in ρ |- *.
  all: solve [ cbn ; f_equal ; eauto ].
Qed.

Lemma urm_subst :
  ∀ t σ,
    urm (t <[ σ ]) = (urm t) <[ σ >> urm ].
Proof.
  intros t σ.
  induction t in σ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. apply ext_term.
    intros []. 1: reflexivity.
    cbn. ssimpl. rewrite urm_ren. reflexivity.
  - cbn. f_equal. 1:eauto.
    + rewrite IHt2. apply ext_term.
      intros []. 1: reflexivity.
      cbn. ssimpl. rewrite urm_ren. reflexivity.
    + rewrite IHt3. apply ext_term.
      intros []. 1: reflexivity.
      cbn. ssimpl. rewrite urm_ren. reflexivity.
Qed.

Lemma urm_scoping :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (urm t) m.
Proof.
  intros Γ t m h.
  induction h. all: solve [ econstructor ; eauto ].
Qed.

Definition urm_ctx (Γ : context) :=
  map (λ '(m, A), (m, urm A)) Γ.

Lemma sc_urm_ctx :
  ∀ Γ,
    sc (urm_ctx Γ) = sc Γ.
Proof.
  intros Γ.
  unfold sc, urm_ctx. rewrite map_map.
  apply map_ext. intros [m A]. reflexivity.
Qed.

Lemma urm_cscoping :
  ∀ Γ t m,
    cscoping Γ t m →
    cscoping (urm_ctx Γ) (urm t) m.
Proof.
  intros Γ t m h. rewrite sc_urm_ctx.
  apply urm_scoping. assumption.
Qed.

Lemma conv_urm :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    urm_ctx Γ ⊢ urm u ≡ urm v.
Proof.
  intros Γ u v h.
  induction h.
  all: try solve [ cbn ; econstructor ; eauto using urm_cscoping ].
  - cbn. rewrite urm_subst. eapply conv_trans.
    1:{
      eapply conv_beta.
      all: try eapply urm_cscoping ; eauto.
      all: eapply urm_scoping. all: rewrite sc_urm_ctx. all: eassumption.
    }
    ssimpl. apply conv_refl.
  - cbn. constructor. all: eauto.
    all: unfold ueq. all: eauto.
Qed.

Ltac unitac h1 h2 :=
  let h1' := fresh h1 in
  let h2' := fresh h2 in
  ttinv h1 h1' ; ttinv h2 h2' ;
  destruct_exists h1' ;
  destruct_exists h2' ;
  intuition subst ;
  eapply conv_trans ; [
    eapply conv_sym ; eassumption
  | idtac
  ].

Lemma type_unique :
  ∀ Γ t A B,
    Γ ⊢ t : A →
    Γ ⊢ t : B →
    Γ ⊢ A ≈ B.
Proof.
  intros Γ t A B hA hB.
  induction t in Γ, A, B, hA, hB |- *.
  all: try unitac hA hB. all: try assumption.
  - ttinv hA hA'. ttinv hB hB'.
    destruct_exists hA'.
    destruct_exists hB'.
    intuition subst.
    eapply conv_trans. 1: eapply conv_sym.
    (* Maybe the definition of ≈ is not the best one here. *)

  (* - eapply meta_conv_trans_l. 2: eassumption.
    f_equal. congruence.
  - repeat scoping_fun.
    eapply IHt2 in H7. 2: eassumption.
    eapply conv_trans. 2: eassumption.
    cbn.
    constructor.
    + apply conv_refl.
    + apply conv_refl.
    + eapply IHt1 in H6. 2: exact H5. assumption.
    + *) (* eapply conv_sym. assumption.
  - repeat scoping_fun.
    eapply conv_trans. 2: eassumption.
    eapply conv_subst.
    + apply styping_one. all: eauto.
    + (* Without injectivity of Π I'm kinda stuck here. *)
      (* Another solution is of course to also annotate application but come on
        it sounds really bad and I'm not sure I can recover from this.
      *)
      admit.
  - eapply conv_trans. 2: eassumption.
    (* eapply IHt. all: auto. *)
    (* Another problem arises here with respect to sorts! *)
    (* I know Type_i ≡ Type_j but not Ghost_i ≡ Ghost_j *)
    (* What would be a reasonable option? *)
    (* Once again, it seems uniqueness may be out of reach, let's postpone *)
    admit.
  - eapply conv_trans. 2: eassumption.
    constructor. eapply IHt. all: auto.
  - eapply conv_trans. 2: eassumption.
    constructor. 1: apply conv_refl.
    eapply IHt1 in H19. 2: eassumption.
    (* Missing injectivity of gheq too. Once again, we could add arguements *)
    admit. *)
Abort.
