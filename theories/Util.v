From Coq Require Import Utf8 List Bool.
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

Ltac destruct_if e :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn: e
  end.

Ltac destruct_if' :=
  let e := fresh "e" in
  destruct_if e.

Ltac destruct_ifs :=
  repeat destruct_if'.

Ltac destruct_bool b :=
  lazymatch b with
  | negb ?b => destruct_bool b
  | ?b && ?c => destruct_bool b
  | _ => let e := fresh "e" in destruct b eqn: e
  end.

Ltac d_if :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct_bool b
  end.
