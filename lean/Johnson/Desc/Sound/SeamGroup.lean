-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamGroup.lean: **GroupFacts (Johnson/Desc/Sound/SeamMembers.lean) IS PAID AT THE SHARED CHAIN's TWO PROXIMITY TESTS**: from the one X at the border · a yes of the seat's decision · "the record's codes are the plan's" · three tests on the plan (johOk · the block's own test ·
"early"). Statements; each proof is calls of what lies.
  seat_yes        a yes of a seat's decision is a yes of the kind's decision at the record behind the door in.
  codes_fixed     the data's codes are the record's: codes_made (Johnson/Desc/K12/Law/TieMade.lean) and closeLedgers_codes (OnBytes/Slice/BlkStLaws.lean).
  **group_nine | group_ten**   at whatever the record behind the door in fixes: GroupFacts cs (fun s => r s.st) t a G0 Ly D ∧ the data have two members.
By: yes_facts (K12/Coin/YesFacts.lean) · found_nine | found_ten (K12/Coin/MembersFound.lean) · sits_nine | sits_ten (K12/Coin/MemberSits.lean).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamMembers
import Johnson.Desc.K12.Coin.YesFacts
import Johnson.Desc.K12.Coin.MembersFound
import Johnson.Desc.K12.Law.TieMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open H2K.First (Plain made_of)
open H2K.Pub (johOk)

/-- A yes of a seat's decision is a yes of the kind's, behind the door in. -/
theorem seat_yes (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) Seat.leave).decide d rs
      gs = .ok d') (t : T12) (ht : Seat.enter g mask d = .ok t) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs = .ok t' := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t₀, ht₀, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', _⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain rfl : t₀ = t := Except.ok.inj (ht₀.symm.trans ht)
  exact ⟨t', ht'⟩

/-- The data's codes are the record's. -/
theorem codes_fixed (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) : D.st.codes = t.st.codes := by
  have h := H2K.Pin.codes_made (made_of π _ a Ly D (hf.2.2.2 default))
  rw [← h]
  exact closeLedgers_codes _ _

section
variable (cs : Codes) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (π : P12)
  (r : Fmt.M1.Stage → ℕ) (hj : johOk π r = true) (he : π.early = true)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
include hj he hp

/-- **AT THE TEST ON G_u.** -/
theorem group_nine (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : sharedX P sentU layU layO 9 d = true) (hc : d.st.codes = cs) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    GroupFacts cs (fun s => r s.st) t a G0 Ly D ∧ D.mems.length = 2 := by
  obtain ⟨t', ht'⟩ := seat_yes _ _ π d d' rs gs hd t ht
  obtain ⟨y1, y2, y3, y4⟩ := yes_facts π r (fun s => r s.st) (fun _ => rfl) hj he hp t t' rs gs ht' a
    rest G0 Ly D hf
  obtain ⟨f1, f2⟩ := found_nine P sentU layU layO d hU hO hX π t ht a rest G0 Ly D hf
  have h2 := (sits_nine P sentU layU layO 0 0 d hU hO hX π t ht a rest G0 Ly D hf).1
  refine ⟨⟨?_, y1, y2, y3, y4, f1, f2⟩, h2⟩
  rw [codes_fixed π t a rest G0 Ly D hf]
  cases ht
  exact hc

/-- **AT THE TEST ON G_omega.** -/
theorem group_ten (hO : 1 < (withOmega P.S).size) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : sharedX P sentU layU layO 10 d = true) (hc : d.st.codes = cs) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    GroupFacts cs (fun s => r s.st) t a G0 Ly D ∧ D.mems.length = 2 := by
  obtain ⟨t', ht'⟩ := seat_yes _ _ π d d' rs gs hd t ht
  obtain ⟨y1, y2, y3, y4⟩ := yes_facts π r (fun s => r s.st) (fun _ => rfl) hj he hp t t' rs gs ht' a
    rest G0 Ly D hf
  obtain ⟨f1, f2⟩ := found_ten P sentU layU layO d hO hX π t ht a rest G0 Ly D hf
  have h2 := (sits_ten P sentU layU layO 0 0 d hO hX π t ht a rest G0 Ly D hf).1
  refine ⟨⟨?_, y1, y2, y3, y4, f1, f2⟩, h2⟩
  rw [codes_fixed π t a rest G0 Ly D hf]
  cases ht
  exact hc

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seat_yes
#print axioms Desc.K14.Law.Fence.codes_fixed
#print axioms Desc.K14.Law.Fence.group_nine
#print axioms Desc.K14.Law.Fence.group_ten
