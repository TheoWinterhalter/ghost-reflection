(*Triangle property via a function rho used in the proof that the multistep reduction system is confluent *)
From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CastRemoval TermMode Scoping BasicMetaTheory.
From GhostTT.reduction.multisteps Require Import Properties.

Set Default Goal Selector "!".

From Equations Require Import Equations.
Derive NoConfusion Subterm for term.

Section views_terms.

  (* term_view_app *)
  Local Definition discr_term_lam (t : term) : Prop :=
    match t with 
    | lam _ _ _ => False
    | _ => True
    end.
  Inductive term_view_app_i : term → term → Type :=
    | term_lam m A t u: term_view_app_i (lam m A t) u
    | term_not_lam t u: discr_term_lam t → term_view_app_i t u.

  Equations term_view_app (t u: term) : term_view_app_i t u :=
  term_view_app (lam m A t) u := term_lam m A t u;
  term_view_app t u := term_not_lam t u I.


  (* term_view_hide *)
  Local Definition discr_term_hide (t : term) : Prop :=
    match t with 
    | hide _ => False
    | _ => True
    end.
  Inductive term_view_reveal_i : term → term → term → Type :=
    | term_hide t P p: term_view_reveal_i (hide t) P p
    | term_not_hide t P p: discr_term_hide t → term_view_reveal_i t P p.

  Equations term_view_reveal (t P p : term) : term_view_reveal_i t P p :=
  term_view_reveal (hide t) P p := term_hide t P p ;
  term_view_reveal t P p := term_not_hide t P p I.


  (* term_view_if *)
  Local Definition discr_term_true_false (t : term) : Prop :=
    match t with 
    | ttrue | tfalse => False
    | _ => True
    end.
  Inductive term_view_if_i : term → term → term → term → Type :=
    | term_true P t f: term_view_if_i ttrue P t f
    | term_false P t f: term_view_if_i tfalse P t f
    | term_not_true_not_false b P t f: discr_term_true_false b → term_view_if_i b P t f.

  Equations term_view_if (b P t f : term) : term_view_if_i b P t f :=
  term_view_if ttrue P t f := term_true P t f ;
  term_view_if tfalse P t f := term_false P t f ;
  term_view_if b P t f := term_not_true_not_false b P t f I.


  (* term_view_nat_elim *)
  Local Definition discr_term_zero_succ (t : term) : Prop :=
    match t with 
    | tzero | tsucc _ => False
    | _ => True
    end. 
  Inductive term_view_nat_elim_i : term → term → term → term → Type :=
    | term_zero P z s: term_view_nat_elim_i tzero P z s
    | term_succ n P z s: term_view_nat_elim_i (tsucc n) P z s
    | term_not_zero_not_succ n P z s: discr_term_zero_succ n → term_view_nat_elim_i n P z s.

  Equations term_view_nat_elim (n P z s : term) : term_view_nat_elim_i n P z s :=
  term_view_nat_elim tzero P z s := term_zero P z s;
  term_view_nat_elim (tsucc n) P z s := term_succ n P z s ;
  term_view_nat_elim n P z s := term_not_zero_not_succ n P z s I.


  (* term_view_vec_elim *)
  Local Definition discr_term_vnil_vcons (t : term) : Prop :=
    match t with 
    | tvnil _ | tvcons _ _ _ => False
    | _ => True
    end. 
  Local Definition discr_term_hide_zero (t : term) : Prop :=
    match t with 
    | hide tzero => False
    | _ => True
    end.
  Local Definition discr_term_for_vec_elim (n t : term) : Prop := discr_term_vnil_vcons t ∨ discr_term_hide_zero n.
  Inductive term_view_vec_elim_i : term → term → term → term → term → term → Type :=
    | term_vnil A B P z s: term_view_vec_elim_i A (hide tzero) (tvnil B) P z s
    | term_vcons A n1 a n0 v P z s: term_view_vec_elim_i A n1 (tvcons a n0 v) P z s
    | term_other_vec_elim A n v P z s: discr_term_for_vec_elim n v → term_view_vec_elim_i A n v P z s.
  Inductive sub_term_view_vec_elim_i : term → Type :=
    | sub_term_hide_zero : sub_term_view_vec_elim_i (hide tzero)
    | sub_term_not_hide t : discr_term_hide_zero t → sub_term_view_vec_elim_i t.

  Equations sub_term_view_vec_elim n : sub_term_view_vec_elim_i n :=
  sub_term_view_vec_elim (hide tzero) := sub_term_hide_zero;
  sub_term_view_vec_elim n := sub_term_not_hide n I.

  Equations term_view_vec_elim (A n v P z s : term) : term_view_vec_elim_i A n v P z s :=
  term_view_vec_elim A n (tvnil B) P z s with sub_term_view_vec_elim n := {
    | sub_term_hide_zero := term_vnil A B P z s;
    | sub_term_not_hide n Hn := term_other_vec_elim A n (tvnil B) P z s (or_intror Hn)};
    term_view_vec_elim A n1 (tvcons a n0 v) P z s := term_vcons A n1 a n0 v P z s ;
    term_view_vec_elim A n v P z s := term_other_vec_elim A n v P z s (or_introl I).

End views_terms.


(* ------------------------------------------------------------------------- *)
Section Rho.

  (* ------------------------------------------------------------------------- *)
  (** Definition of rho **)

  Equations ρ (Γ : scope) (t : term) : term 
  by wf t term_subterm :=

  (* cast *)
  ρ Γ (ghcast A u v e P t) := 
  if mode_eq (md Γ t) ℙ then ⋆ 
  else ghcast (ρ Γ A) (ρ Γ u) (ρ Γ v) (ρ Γ e) (ρ Γ P) (ρ Γ t);
  (* some cases when t ∷ ℙ *)
  ρ Γ (var n) := 
  if mode_eq (md Γ (var n)) ℙ then ⋆ else var n;
  ρ Γ (toRev _ _ _) := ⋆;
  ρ Γ (fromRev _ _ _) := ⋆;
  ρ Γ (ghrefl _ _) := ⋆;

  (* Beta reduction and app *)
  ρ Γ (app t u) with (term_view_app t u) := {
    | (term_lam mx A t1 u):=
        if mode_eq (md Γ (lam mx A t1)) ℙ then ⋆
        else if mode_eq (md Γ u) mx then
        (ρ (mx::Γ) t1) <[ (ρ Γ u)··]
        else app (ρ Γ (lam mx A t1)) (ρ Γ u);
    | (term_not_lam t u Ht) :=
        if mode_eq (md Γ t) ℙ then ⋆
        else app (ρ Γ t) (ρ Γ u)};

        (* Reveal hide and reveal *)
        ρ Γ (reveal t P p) with (term_view_reveal t P p):= {
    | term_hide t P p :=
        if mode_eq (md Γ (reveal (hide t) P p)) ℙ then ⋆
        else app (ρ Γ p) (ρ Γ t);
    | term_not_hide t P p Ht :=
        if mode_eq (md Γ (reveal t P p)) ℙ then ⋆
        else reveal (ρ Γ t) (ρ Γ P) (ρ Γ p)};

        (* Sort ℙ i *)
        ρ Γ (Sort m i) := Sort m (red_lvl m i);

        (* Cases where context changes *)
        (* red _Pi_ℙ_ℙ *)
        ρ Γ (Pi i j m mx A B) :=
        Pi (red_lvl mx i) (red_lvl m j) m mx (ρ Γ A) (ρ (mx::Γ) B);
        (* red_lam *)
        ρ Γ (lam mx A t) :=
        if mode_eq (md (mx::Γ) t) ℙ then ⋆
        else lam mx (ρ Γ A) (ρ (mx::Γ) t);

        (* One variable recursive cases *)
        (* Erased *)
        ρ Γ (Erased t) := Erased (ρ Γ t);
        (* hide *)
        ρ Γ (hide t) := hide (ρ Γ t);
        (* tsucc *)
        ρ Γ (tsucc n) := tsucc (ρ Γ n);
        (* tvnil *)
        ρ Γ (tvnil A) := tvnil (ρ Γ A);

        (* Two variables recursive cases *)
        (* Reveal *)
        ρ Γ (Reveal t P) := Reveal (ρ Γ t) (ρ Γ P);
        (* vec *)
        ρ Γ (tvec A n) := tvec (ρ Γ A) (ρ Γ n);
        (* bot_elim *)
        ρ Γ (bot_elim m A p) :=
        if mode_eq m ℙ then ⋆
        else bot_elim m (ρ Γ A) (ρ Γ p);

        (* Three variables recursive cases *)
        (* vcons *)
        ρ Γ (tvcons a n v) := tvcons (ρ Γ a) (ρ Γ n) (ρ Γ v);
        (* gheq *)
        ρ Γ (gheq A u v) := gheq (ρ Γ A) (ρ Γ u) (ρ Γ v);

        (* Four variables recursive cases *)
        (* if *)
        ρ Γ (tif m b P t f) with term_view_if b P t f := {
    | term_true P t f := 
        if mode_eq m ℙ then ⋆ 
        else if mode_eq (md Γ t) m then ρ Γ t
        else tif m ttrue (ρ Γ P) (ρ Γ t) (ρ Γ f);
    | term_false P t f := 
        if mode_eq m ℙ then ⋆
        else if mode_eq (md Γ f) m then ρ Γ f
        else tif m tfalse (ρ Γ P) (ρ Γ t) (ρ Γ f);
    | term_not_true_not_false b P t f Hb :=
        if mode_eq m ℙ then ⋆
        else tif m (ρ Γ b) (ρ Γ P) (ρ Γ t) (ρ Γ f)};
        (* nat_elim *)
        ρ Γ (tnat_elim m n P z s) with term_view_nat_elim n P z s := {
    | term_zero P z s := 
        if mode_eq m ℙ then ⋆ 
        else if mode_eq (md Γ z) m then ρ Γ z
        else tnat_elim m tzero (ρ Γ P) (ρ Γ z) (ρ Γ s);
    | term_succ n P z s := 
        if mode_eq m ℙ then ⋆
        else if mode_eq (md Γ s) m then 
          let n' := (ρ Γ n) in let s' := (ρ Γ s) in
          app (app s' n') (tnat_elim m n' (ρ Γ P) (ρ Γ z) s')
        else tnat_elim m (tsucc (ρ Γ n)) (ρ Γ P) (ρ Γ z) (ρ Γ s);
    | term_not_zero_not_succ n P z s Hn := 
        if mode_eq m ℙ then ⋆
        else tnat_elim m (ρ Γ n) (ρ Γ P) (ρ Γ z) (ρ Γ s)};

        (* Six variables recursive cases *)
        (* vec_elim *)
        ρ Γ (tvec_elim m A n0 v P z s) with term_view_vec_elim A n0 v P z s := {
    | term_vnil A B P z s :=
        if mode_eq m ℙ then ⋆
        else if mode_eq (md Γ z) m then ρ Γ z
        else tvec_elim m (ρ Γ A) (hide tzero) (tvnil (ρ Γ B)) (ρ Γ P) (ρ Γ z) (ρ Γ s);
    | term_vcons A n0 a n v P z s := 
        if mode_eq m ℙ then ⋆
        else if mode_eq (md Γ s) m then
          let A' := ρ Γ A in let n' := ρ Γ n in
          let v' := ρ Γ v in let s' := ρ Γ s in
          app (app (app (app s' (ρ Γ a)) (glength A' n' v')) v') (tvec_elim m A' n' v' (ρ Γ P) (ρ Γ z) s')
        else tvec_elim m (ρ Γ A) (ρ Γ n0) (tvcons (ρ Γ a) (ρ Γ n) (ρ Γ v)) (ρ Γ P) (ρ Γ z) (ρ Γ s);
    | term_other_vec_elim A n0 v P z s Hvn :=
        if mode_eq m ℙ then ⋆
        else tvec_elim m (ρ Γ A) (ρ Γ n0) (ρ Γ v) (ρ Γ P) (ρ Γ z) (ρ Γ s)};

        (* zero variables recursive cases *)
        ρ Γ tbool := tbool;
        ρ Γ ttrue := ttrue;
        ρ Γ tfalse := tfalse;
        ρ Γ tnat := tnat;
        ρ Γ tzero := tzero;
        ρ Γ bot := bot.

End Rho.
(* ------------------------------------------------------------------------- *)
(** properties of ρ **)

Lemma ρ_of_ℙ (Γ : scope) (p : term) :
  md Γ p = ℙ → ρ Γ p = ⋆.
Proof.
  intro prf_p.
  induction p.
  all: try reflexivity.
  all: simp ρ.
  all: try solve [inversion prf_p].
  8: case term_view_vec_elim in *; simp ρ.
  7: case term_view_nat_elim in *; simp ρ.
  6: case term_view_if in *; simp ρ.
  4: case term_view_reveal in *; simp ρ.
  3: case term_view_app in *; simp ρ.
  all: case (mode_eq _ _); [reflexivity |contradiction ].
Qed. 

Theorem rho_one_step : ∀ Γ t, Γ ⊨ t ⇶ ρ Γ t.
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: simp ρ.
  all: try case (mode_eq _ _) as [ e | ne ]; gred.
  all: try reflexivity.
  - unfold red_lvl. 
    case (mode_eq _ _) as [ e | ne ]; subst; gred.
  - case term_view_app as [m A t | ]; simp ρ.
    1: assert ( Γ⊨lam m A t⇶ρ Γ (lam m A t)) as red_lam; eauto.
    1: simp ρ in red_lam.
    all: case (mode_eq _ _) as [ e | ne ]; gred.
    all: case (mode_eq _ _) as [ e' | ne' ]; gred.
    red_lam_inv_auto A' t' e red_A' red_t'. 
    noconf e.
    assumption.
  - case term_view_reveal as [t P p | ]; simp ρ.
    all: case (mode_eq _ _) as [ e | ne ]; gred.
    * assert (Γ⊨hide t⇶ρ Γ (hide t)) as H; eauto.
      simp ρ in H.
      red_hide_inv_auto t' e. 
      noconf e.
      assumption.
    * cbn in ne. case (md _ _) in *.
      all: try contradiction.
      right; left. reflexivity.
  - case term_view_if as [ | | ]; simp ρ.
    all: repeat case (mode_eq _ _) as [ | ].
    all: try solve [gred].
    all: apply red_if; gred.
  - case term_view_nat_elim as [ |n | ]; simp ρ.
    all: repeat case (mode_eq _ _) as [ | ]; cbn.
    3: eapply red_nat_elim; gred.
    all: gred.
    assert (Γ⊨tsucc n⇶ρ Γ (tsucc n)) as H; eauto.
    simp ρ in H.
    red_succ_inv_auto n' e'.
    noconf e'.
    assumption.
  - case term_view_vec_elim as [ | A n a n0 v| ]; simp ρ.
    all:repeat case (mode_eq _ _) as [ | ]; cbn.
    3: eapply red_vec_elim; gred.
    all: try solve [gred].
    assert (Γ⊨tvcons a n0 v⇶ρ Γ (tvcons a n0 v)) as H; eauto.
    simp ρ in H.
    red_conv_inv_auto a' n' v' e' red_a' red_n' red_v'.
    cbn; gred.
    all: congruence.
Qed.

Lemma reduction_triangle (Γ : scope) (t u : term) :
  Γ ⊨ t ⇶ u → Γ ⊨ u ⇶ (ρ Γ t).
Proof.
  intros red_t.
  induction red_t in t, Γ, u, red_t |- *.
  all: simp ρ.
  all: try solve [gred; try case (mode_eq _ _); eauto using rho_one_step; gred].
  all: try solve [rewrite ρ_of_ℙ; gred].
  all: try solve [repeat case (mode_eq _ _) as [ | ];
      try contradiction; solve [cbn; gred; cbn; erewrite <- red_md; eauto; congruence]].
  (* red_beta*)
  - repeat (case (mode_eq _ _) as [ | ]); gred.
    * cbn in *. erewrite <- md_subst'; eauto.
      + erewrite <- red_md; eassumption.
      + intro n; destruct n; cbn; eauto.
        erewrite <- red_md; eassumption.
    * eapply red_subst; eauto.
      + intro n0; destruct n0; cbn; eauto.
        erewrite <- red_md; eassumption.
      + intro n0; destruct n0; cbn; gred.
    * exfalso; eauto.
      (* red_reveal_hide *)
  - case (mode_eq _ _) as [ | ]; gred.
        erewrite <- red_md; gred.
    (* red_vec_elim_cons *)
  - repeat case (mode_eq _ _) as [ | ].
    * gred; cbn. erewrite <- red_md; eauto; congruence.
    * cbn; gred. 
      + eapply red_ren; eauto.
        intro n0'; destruct n0'; eauto.
      + eapply (red_ren _ (𝕋::_)); cbn; eauto.
        eapply red_ren; eauto.
        all: intro n0'; destruct n0'; eauto.
    * contradiction.
      (* red_app *)
  - case term_view_app as [ mx0 A u v | u v d] in *.
    all: simp ρ in *.
    all: repeat case (mode_eq _ _) as [ | ]; gred.
    * cbn. erewrite <- red_md; eauto. cbn. assumption.
    * red_lam_inv_auto A' t' e' red_A red_u.
      match goal with H: _ ⊨ lam _ _ _ ⇶ _ |- _ => 
          eapply red_lam_inv in H; eauto;
          [ destruct H as [A'' [t'' [ Hu'' [red_A' red_u']]]] | ] end.
      + apply sym_eq in Hu''; inversion Hu''; subst. 
        gred. symmetry; apply red_md. assumption.
      + cbn. erewrite <- red_md; eauto.
    * cbn; erewrite <- red_md; eauto. 
      (* red_reveal *)
  - case term_view_reveal as [t | ].
    all: simp ρ in *.
    all: repeat case (mode_eq _ _) as [ | ]; gred.
    1,3: cbn in *; erewrite <- red_md; eauto. 
    red_hide_inv_auto t0' e.
    gred; eauto using red_md.
    * red_hide_inv_auto t0 e.
      noconf e.
      assumption.
    * cbn in *. erewrite <- red_md; eauto.
      right; left. case (md _ _) in *; try contradiction.
      reflexivity.
    (* red_if *)
  - simp ρ in *.
    case term_view_if as [ | | ] in *.
    all: simp ρ in *.
    all: repeat case (mode_eq _ _) as [ | ]; gred.
    all: red_basic_inv.
    all: try (cbn in *; match goal with H: _ = ℙ |- _ =>
        inversion H end).
    all: gred; symmetry; eauto using red_md.
    (* red_nat_elim *)
  - simp ρ in *.
    case term_view_nat_elim as [ |n| n] in *.
    all: simp ρ in *.
    all: repeat case (mode_eq _ _) as [ | ]; cbn; gred.
    * red_basic_inv.
      all: try (cbn in *; match goal with H: _ = ℙ |- _ =>
          inversion H end).
          gred; symmetry; eauto using red_md.
    * red_succ_inv_auto n'' e'.
      cbn; gred.
      + red_succ_inv_auto n' e''.
        noconf e''.
        assumption.
      + erewrite <- red_md; eauto.
        (* red_vec_elim *)
  - case term_view_vec_elim as [ |A n v P z s| ] in *.
    all: simp ρ in *.
    all: repeat case (mode_eq _ _) as [ | ]; cbn; gred.
    * red_hide_inv_auto zero' e'.
      red_basic_inv.
      all: try (cbn in *; match goal with H: _ = ℙ |- _ =>
          inversion H end).
      red_nil_inv_auto A0 e'.
      eapply red_vec_elim_nil; eauto.
      erewrite <- red_md; eauto.
    * red_conv_inv_auto a1 n1 v1 e' red_a1 red_n1 red_v1.
      red_conv_inv_auto a2 n2 v2 e' red_a2 red_n2 red_v2.
      noconf e'.
      gred; erewrite <- red_md; eauto.
Qed.
