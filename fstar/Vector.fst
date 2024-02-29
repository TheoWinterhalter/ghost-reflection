module Vector

open FStar.Ghost

noeq
type vec a : n:erased nat -> Type =
| Vnil : vec a 0
| Vcons : x:a -> #n:erased nat -> v:vec a n -> vec a (n+1)

let rec rev #a #n #m (v : vec a n) (acc : vec a m) : vec a (n + m) =
  match v with
  | Vnil -> acc
  | Vcons x v -> rev v (Vcons x acc)

let rec app #a #n #m (v : vec a n) (w : vec a m) : vec a (n + m) =
  match v with
  | Vnil -> w
  | Vcons x v -> Vcons x (app v w)

let rec app_assoc #a #n #m #k (u : vec a n) (v : vec a m) (w : vec a k) :
  Lemma (u `app` (v `app` w) == (u `app` v) `app` w)
= match u with
  | Vnil -> ()
  | Vcons x u -> app_assoc u v w

let rec rev_spec #a #n (v : vec a n) : vec a n =
  match v with
  | Vnil -> Vnil
  | Vcons x v -> rev_spec v `app` Vcons x Vnil

let rec rev_spec_rev #a #n #m (v : vec a n) (acc : vec a m) :
  Lemma (rev v acc == rev_spec v `app` acc)
= match v with
  | Vnil -> ()
  | Vcons x v ->
    app_assoc (rev_spec v) (Vcons x Vnil) acc ;
    rev_spec_rev v (Vcons x acc)

let head #a (#n:nat) (v : vec a (n+1)) : a =
  match v with
  | Vcons x v -> x

let tail #a (#n:nat) (v : vec a (n+1)) : vec a n =
  match v with
  | Vcons x v -> v

let rec vnth #a #n (v : vec a n) (m:nat { m < n }) : a =
  match v with
  | Vcons x v ->
    if m = 0 then x else vnth v (m-1)
