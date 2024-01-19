From Coq Require Import Utf8 List.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

Ltac forall_iff_impl T :=
  lazymatch eval cbn beta in T with
  | forall x : ?A, @?T' x =>
    let y := fresh x in
    refine (forall y, _) ;
    forall_iff_impl (@T' x)
  | ?P ↔ ?Q => exact (P → Q)
  | _ => fail "not a quantified ↔"
  end.

Ltac wlog_iff_using tac :=
  lazymatch goal with
  | |- ?G =>
    let G' := fresh in
    unshelve refine (let G' : Prop := _ in _) ; [ forall_iff_impl G |] ;
    let h := fresh in
    assert (h : G') ; [
      subst G'
    | subst G' ; intros ; split ; eauto ; apply h ; clear h ; tac
    ]
  end.

Ltac wlog_iff :=
  wlog_iff_using firstorder.

Create HintDb shelvedb.

Hint Extern 10000 => shelve : shelvedb.
