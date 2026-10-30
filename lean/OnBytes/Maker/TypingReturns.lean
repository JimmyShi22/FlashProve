-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingReturns.lean: the typing of a stretch's plain parts returns at what a reader has
read.

`plainsT` (OnBytes/Maker/TypingT.lean) types the plain parts of a stretch from the rounds as read.
It returns nothing if the numbers of rounds differ or a round's values are not of the kinds that the
round's data name. A reader reads each round's message as the description's items. So where the
data's items are the description's, round by round, the typing returns.

Main definitions.
  `ItemsAs ds rs`: the rounds' data and the description's rounds have, member by member, the same
    items.
  `ValsAs f rs ros`: each round's values are its message read whole as the round's items.
Main theorems. `plainsT_some`: under `ItemsAs` and `ValsAs`. `valsAs_of_trace`: the library's record
of a reader's output (`Run.TraceL`, Run/PageIs.lean) gives `ValsAs`. `itemsAs_dropLast`,
`valsAs_dropLast`: both are kept where the last round is dropped on both sides.

What is not said. That a reading has `ValsAs`. That data made from a dry run have `ItemsAs` with the
description under which the file was read.


-/
import OnBytes.Maker.TypingT
import Run.PageIsTopProofs

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ

/-- The rounds' data and the description's rounds have the same items, member by member. -/
def ItemsAs (ds : List RDT) (rs : List Fmt.Round) : Prop :=
  List.Forall₂ (fun d r => d.items = r.items) ds rs

/-- Each round's values are its message, read whole as the round's items. -/
def ValsAs (f : Fmt.Fld) (rs : List Fmt.Round) (ros : List Fmt.RoundOut) : Prop :=
  List.Forall₂ (fun r ro => Fmt.whole (Fmt.readItems f r.items) ro.msg = some ro.vals) rs ros

/-- **The typing of the plain parts returns at a reader's output.** -/
theorem plainsT_some (C : CK) (f : Fmt.Fld) :
    ∀ (ds : List RDT) (rs : List Fmt.Round) (ros : List Fmt.RoundOut), ItemsAs ds rs →
      ValsAs f rs ros → ∃ pl, plainsT C ds ros = some pl
  | [], [], [], _, _ => ⟨(), rfl⟩
  | d :: ds, r :: rs, ro :: ros, hi, hv => by
    cases hi with
    | cons hd hi' =>
      cases hv with
      | cons hv hv' =>
        rw [← hd] at hv
        obtain ⟨p, hp⟩ := ofGots_whole f d.items ro.msg ro.vals hv
        obtain ⟨pl, hpl⟩ := plainsT_some C f ds rs ros hi' hv'
        refine Option.isSome_iff_exists.1 ?_
        simp only [plainsT, hp, hpl, Option.isSome_some]

/-- The library's record of a reader's output gives it. -/
theorem valsAs_of_trace (h : HId) (P : Fmt.Plan) :
    ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (c : Fmt.Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → ValsAs P.field rs ros
  | [], [], _, _, _ => .nil
  | _ :: rs, _ :: ros, _, _, t => .cons t.2.1 (valsAs_of_trace h P rs ros _ _ t.2.2.2.2.2)
  | [], _ :: _, _, _, t => t.elim
  | _ :: _, [], _, _, t => t.elim

/-- A relation member by member is kept where the last member is dropped on both sides. -/
theorem forall₂_dropLast {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁.dropLast l₂.dropLast
  | _, _, .nil => .nil
  | [_], [_], .cons _ .nil => .nil
  | _ :: _ :: _, _ :: _ :: _, .cons h t => .cons h (forall₂_dropLast t)

theorem itemsAs_dropLast {ds : List RDT} {rs : List Fmt.Round} (h : ItemsAs ds rs) :
    ItemsAs ds.dropLast rs.dropLast := forall₂_dropLast h

theorem valsAs_dropLast {f : Fmt.Fld} {rs : List Fmt.Round} {ros : List Fmt.RoundOut}
    (h : ValsAs f rs ros) : ValsAs f rs.dropLast ros.dropLast := forall₂_dropLast h

end OnBytes.Maker
