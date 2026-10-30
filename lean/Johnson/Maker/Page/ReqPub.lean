-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/ReqPub.lean: the bytes of the item `request` in a proof file's first chain
query, as a function of the typed instance: the first half of a value for the function `reqX` by
which a page spells a request (the whole value: `HoldsPub.req2`, Johnson/Maker/Page/ReqBoth.lean),
and what is asked of the type of instances so that the premise on it is a law.



The first chain of a proof file takes the request as two strings: the item (`Proof.requestItem`,
OnBytes/Proof/RequestItem.lean) and the request file's bytes. This file speaks of the item alone.
The verifier program forms it from the
parameter file, the scale file and the request's file. It does not read the reply: "The word of the
reply is 0". The compiled verifier's first query holds the early part of the typed instance, and
the page spells the first chain's statement from it through a function into two strings. The premise
on these comes down to one equation, `reqX (L.early x) = (request, words)`, with the type of
instances, `early` and `reqX` as letters; a constant function is a value of such a `reqX`. Here the
first half of a `reqX` is written, under the name `HoldsPub.reqX`. Definitions and proofs.

Main names:
  `itemPub u`: the item, as a function of the public input of a proof file's reading (`ProofPub`,
    OnBytes/TieK/Good.lean); no bytes where the program forms none. `itemPub_eq`.
  `SameAsk u v`: two public inputs have the same parameter file, scale file and request's file.
    `itemPub_congr`: then they have the same item.
  `HoldsPub X early`: how an instance holds the public input: a map `pub`, and ONE law: `early`
    keeps what the item is made of.
  `HoldsPub.reqX`: the first half of the value: the item of the instance's public input.
  `reqX_early`: THE EQUATION's FIRST HALF: at an instance that holds u, where the program forms the
    item: `reqX (early x) = item`.
  `reqX_apart`: instances whose public inputs have different items have different bytes. That two
    public inputs with different items exist is not shown here.
  `wipe`, `holdsSelf`: the record is met: the public input itself as the type of instances, `early`
    wiping the reply: a toy of the TYPE, no description's type of instances.
  `holdsBytes`, `holdsBytes_at`: the record is met at three fixed public files by every type of
    instances with two functions into bytes, the request's file and the reply's, if `early` keeps
    the first; there `hx` comes to the three pins (the public input's three public files are the
    fixed ones) and two equations: the instance's two files are the public input's.
What is asked, by name: hx: the instance holds the public input u. hi: the program forms the item.

To be minded: the record asks ONE law, and a constant `pub` meets it. So where H is a letter, hx
pins nothing of the instance: a caller is to take a written H whose `pub` reads the instance
(`holdsBytes`), fixed before the call, and to name the instance (Johnson/Maker/Page/ReqIns.lean:
`req_of_ins`).

Limits: hx is the weight: that the typed instance of a call holds that call's files is shown of no
description's instance here; `holdsSelf` and `holdsBytes` are values of the record, not a
description's. The two equations of `holdsBytes_at` are shown of no type of instances here. Where
the program forms no item, `itemPub` is the empty string; the statements here stand under hi, where
it forms one. The premise on the page's two strings itself is not stated here. That two requests
have two items is claimed nowhere: the request's file enters the item through a digest of the
second hash function.
Nothing on the first chain's block. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.TieK.Good
import OnBytes.Proof.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes
open OnBytes.TieK (ProofPub)

/-! ## The item, as a function of the public input -/

/-- The value of the statement's item `request` at a public input; no bytes where the program forms
none. -/
def itemPub (u : ProofPub) : ByteArray :=
  (Proof.requestItem u.pol u.KL u.request).getD ByteArray.empty

theorem itemPub_eq {u : ProofPub} {item : ByteArray}
    (h : Proof.requestItem u.pol u.KL u.request = some item) : itemPub u = item := by
  unfold itemPub
  rw [h]
  rfl

/-- The same parameter file, scale file and request's file. -/
def SameAsk (u v : ProofPub) : Prop := u.pol = v.pol ∧ u.KL = v.KL ∧ u.request = v.request

theorem itemPub_congr {u v : ProofPub} (h : SameAsk u v) : itemPub u = itemPub v := by
  unfold itemPub
  rw [h.1, h.2.1, h.2.2]

/-! ## How an instance holds the public input -/

/-- How an instance holds the public input of a proof file's reading. The one law: the early part of
an instance holds the same parameter file, scale file and request's file. -/
structure HoldsPub (X : Type) (early : X → X) where
  pub : X → ProofPub
  early_same : ∀ x, SameAsk (pub (early x)) (pub x)

variable {X : Type} {early : X → X}

/-- **The first half of the value of the letter `reqX`**: the item of the instance's public
input. -/
def HoldsPub.reqX (H : HoldsPub X early) (x : X) : ByteArray := itemPub (H.pub x)

/-- **The equation's first half.** -/
theorem reqX_early (H : HoldsPub X early) (x : X) (u : ProofPub) (item : ByteArray)
    (hx : H.pub x = u) (hi : Proof.requestItem u.pol u.KL u.request = some item) :
    H.reqX (early x) = item := by
  unfold HoldsPub.reqX
  rw [itemPub_congr (H.early_same x), hx]
  exact itemPub_eq hi

/-- Instances whose public inputs have different items have different bytes. -/
theorem reqX_apart (H : HoldsPub X early) (x x' : X) (a b : ByteArray)
    (ha : Proof.requestItem (H.pub x).pol (H.pub x).KL (H.pub x).request = some a)
    (hb : Proof.requestItem (H.pub x').pol (H.pub x').KL (H.pub x').request = some b)
    (hab : a ≠ b) : H.reqX x ≠ H.reqX x' := by
  unfold HoldsPub.reqX
  rw [itemPub_eq ha, itemPub_eq hb]
  exact hab

/-! ## The record is met -/

/-- The reply wiped. -/
def wipe (u : ProofPub) : ProofPub := { u with y := ByteArray.empty }

/-- The public input itself as the type of instances. -/
def holdsSelf : HoldsPub ProofPub wipe := ⟨id, fun _ => ⟨rfl, rfl, rfl⟩⟩

section Bytes
variable (pol lay KL : ByteArray) (reqB repB : X → ByteArray)

/-- At three fixed public files: an instance gives the bytes of a request's file and of a reply's
file, and the early part of an instance gives the same request's file. -/
def holdsBytes (he : ∀ x, reqB (early x) = reqB x) : HoldsPub X early :=
  ⟨fun x => ⟨pol, lay, KL, reqB x, repB x⟩, fun x => ⟨rfl, rfl, he x⟩⟩

/-- **What `hx` comes to there**: an instance holds a public input at these three files if its two
files' bytes are that input's. -/
theorem holdsBytes_at (he : ∀ x, reqB (early x) = reqB x) (x : X) (u : ProofPub) (h1 : u.pol = pol)
    (h2 : u.lay = lay) (h3 : u.KL = KL) (hr : reqB x = u.request) (hy : repB x = u.y) :
    (holdsBytes pol lay KL reqB repB he).pub x = u := by
  obtain ⟨p, l, k, r, y⟩ := u
  simp only at h1 h2 h3 hr hy
  subst h1 h2 h3
  show (⟨p, l, k, reqB x, repB x⟩ : ProofPub) = ⟨p, l, k, r, y⟩
  rw [hr, hy]

end Bytes

end Johnson.Session
