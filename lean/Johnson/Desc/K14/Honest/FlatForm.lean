-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/FlatForm.lean: the form of the shared chain's flat list: it begins with the
front sub-protocol and the eight sub-protocols of the linear claim's shared rounds.

In a proof file's IOP as written in Lean the shared chain is carried to the file's type of claims
(Johnson/Desc/Block.lean: Chain.retype): its members are the kind's sub-protocols carried, not the
kind's sub-protocols. The library writes the carried chain's flat list out
(Johnson/Desc/K14/Law/SharedFlat.lean). This file says what of a member is left by the carrying, in
one relation, and that list's form in one proposition, for whoever speaks of a member by its number.

Main names:
  Like x b            x has b's declared rounds, stated oracle messages, place and decide function
  like_retype, like_frontOf   a carried sub-protocol; the front sub-protocol as the carried chain
                      holds it
  FlatOf xs c b1 … b8   xs begins with the front sub-protocol and the eight, each as Like says
  flatOf_carried      **the carried chain's flat list is such a list**
  FlatOf.at0, …, at8  the members by their numbers

What is not claimed. Nothing on what stands behind the eight in the list. That the IOP as written in
Lean makes the eight (a premise). Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Law.SharedFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open VerifiableInference.Desc (Block)
open Desc.K14.Law (frontOf flat_retype_all)

variable {Cl : Type}

/-- x is b in four fields of a sub-protocol: the declared rounds, the stated oracle messages, the
place and the decide function: all that the format's step reads. (The type of claims, the fields
before, claims and after, the name and the test on the plan may differ.) -/
structure Like (x : Block St Cl) (b : Block St Unit) : Prop where
  rounds : x.rounds = b.rounds
  oracles : x.oracles = b.oracles
  place : x.place = b.place
  decide : x.decide = b.decide

/-- A sub-protocol carried to another type of claims is like itself. -/
theorem like_retype (b : Block St Unit) : Like (b.retype (Cl' := Cl)) b := ⟨rfl, rfl, rfl, rfl⟩

/-- The front sub-protocol, as the carried chain holds it, is like the front sub-protocol. -/
theorem like_frontOf (c : OnBytes.Model.Verify.Chains) :
    Like (frontOf (Cl' := Cl) c) (frontBlock c) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **xs begins with the shared chain's front sub-protocol and the eight b1, …, b8**, each as Like
says. -/
def FlatOf (xs : List (Block St Cl)) (c : OnBytes.Model.Verify.Chains)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) : Prop :=
  ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 tl, xs = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl ∧
    Like x0 (frontBlock c) ∧ Like x1 b1 ∧ Like x2 b2 ∧ Like x3 b3 ∧ Like x4 b4 ∧ Like x5 b5 ∧
    Like x6 b6 ∧ Like x7 b7 ∧ Like x8 b8

/-- **The flat list of the shared chain, carried to another type of claims, is such a list**: the
form in which a proof file's IOP as written in Lean holds it (Johnson/Desc/K14/Law/SharedFlat.lean:
flat_retype_all, shared_flat_pure). -/
theorem flatOf_carried (c : OnBytes.Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    FlatOf ((chainOf c P tests last).retype (Cl' := Cl)).blocksInOrder c b1 b2 b3 b4 b5 b6 b7 b8 := by
  rw [flat_retype_all c P b1 b2 b3 b4 b5 b6 b7 b8 tests last hb]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, like_frontOf c, like_retype b1, like_retype b2,
    like_retype b3, like_retype b4, like_retype b5, like_retype b6, like_retype b7, like_retype b8⟩

variable {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains}
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- The member number 0 is the front sub-protocol. -/
theorem FlatOf.at0 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[0]? = some blk) : Like blk (frontBlock c) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x0 = blk := Option.some.inj h
  exact l0

/-- The member number 1 is b1. -/
theorem FlatOf.at1 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[1]? = some blk) : Like blk b1 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x1 = blk := Option.some.inj h
  exact l1

/-- The member number 2 is b2. -/
theorem FlatOf.at2 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[2]? = some blk) : Like blk b2 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x2 = blk := Option.some.inj h
  exact l2

/-- The member number 3 is b3. -/
theorem FlatOf.at3 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[3]? = some blk) : Like blk b3 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x3 = blk := Option.some.inj h
  exact l3

/-- The member number 4 is b4. -/
theorem FlatOf.at4 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[4]? = some blk) : Like blk b4 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x4 = blk := Option.some.inj h
  exact l4

/-- The member number 5 is b5. -/
theorem FlatOf.at5 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[5]? = some blk) : Like blk b5 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x5 = blk := Option.some.inj h
  exact l5

/-- The member number 6 is b6. -/
theorem FlatOf.at6 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[6]? = some blk) : Like blk b6 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x6 = blk := Option.some.inj h
  exact l6

/-- The member number 7 is b7. -/
theorem FlatOf.at7 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[7]? = some blk) : Like blk b7 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x7 = blk := Option.some.inj h
  exact l7

/-- The member number 8 is b8. -/
theorem FlatOf.at8 (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) {blk : Block St Cl}
    (h : xs[8]? = some blk) : Like blk b8 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain rfl : x8 = blk := Option.some.inj h
  exact l8

end Desc.K14.Honest

#print axioms Desc.K14.Honest.like_retype
#print axioms Desc.K14.Honest.like_frontOf
#print axioms Desc.K14.Honest.flatOf_carried
#print axioms Desc.K14.Honest.FlatOf.at0
#print axioms Desc.K14.Honest.FlatOf.at1
#print axioms Desc.K14.Honest.FlatOf.at2
#print axioms Desc.K14.Honest.FlatOf.at3
#print axioms Desc.K14.Honest.FlatOf.at4
#print axioms Desc.K14.Honest.FlatOf.at5
#print axioms Desc.K14.Honest.FlatOf.at6
#print axioms Desc.K14.Honest.FlatOf.at7
#print axioms Desc.K14.Honest.FlatOf.at8
