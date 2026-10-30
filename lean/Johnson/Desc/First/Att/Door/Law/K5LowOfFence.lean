-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LowOfFence.lean: kind K5 (an attention segment's own rounds): THREE FIELDS OF K5Rest (K5AtMgPaid.lean: low · lowI · low0: "the sampled tenants that the law touches sit in trees below the piece's base") FROM ONE TEST ON THE TABLE's NUMBERS, fenceFit
(Johnson/Desc/First/FenceFit.lean), at the full written lists, at numbers that are filled off what the sub-protocols tell (Numbers.withTold), general in the numbers beneath.

Why. seated_fenced (Johnson/Desc/Sound/PieceSeated.lean) ends in the field low, to the letter, under five premises. At numbers of the form N₀.withTold ps told the test bookFit says yes by that filling's make (bookFit_withTold, Johnson/Desc/First/BookFitTold.lean; the list of places has no repeat:
ProofFile.Law.flatPlaces_nodup). What is left: the piece's four facts · the sub-protocols' own tests on the plan · fenceFit. And the fields lowI | low0 are low at two of its members: at each of the kind's twelve borders the pins that are open are JUST the index masks' and the segment's first sending's: a decision by the kernel.

Main names:
  `OFullK k`: the items open at border k of the full written lists. `pinsOf`: its pins with a sample.
  `k5PinsB n`, `k5PinsB_full`: **at the borders 14 (2 g + 1) + 4, g < 12, the open pins are [pinI, pin (2 g + 1) 0]**: by the kernel.
    `k5Pins_bite` | `k5Pins_bite'`: a corollary of k5PinsB_full (given that theorem it cannot fail)
    and one negative test: at border 18 the list is not [pinI, pin 3 0]; at border 0 it is not [pinI, pin 1 0]. (NO negative test: "k5PinsB 13": it is TRUE: border 354 lies in the chain's tail, where the open pins are [pinI, pin 25 0].)
  `pinI_open`, `pin0_open`: the two memberships.
  **`low_of_fence`**: PieceMore … (14 (2 g + 1) + 4) q · blocksOk bs · fenceFit (N₀.withTold PFullK (toldOf bs)) LFullK PFullK ⊢ low ∧ lowI ∧ low0 at bs := q.base.
  `low_iff`: at these borders low says no more than lowI and low0 together.
Is it empty here? fenceFit IS SHOWN AT NOTHING HERE. It has content (it ties the plan's seats to the description's telling: FenceFitTold.lean's head). No test of the verifier's value asks it.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.PieceSeated
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.Desc.First.Att.Door.Law.K05KindR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound

/-- The items that are open at border k of the full written lists. -/
abbrev OFullK (k : ℕ) : List Item := (openSets LFullK PFullK (start LFullK))[k]?.getD []

/-- The pins with a sample among a list of items. -/
def pinsOf (O : List Item) : List Item :=
  O.filter fun i => match i with
    | .pin _ _ => true
    | .pinKept _ => true
    | .pinI => true
    | .pinV => true
    | _ => false

/-- The test: in front of the kind's sub-protocol of the groups below n the open pins are just two. -/
def k5PinsB (n : Nat) : Bool :=
  (List.range n).all fun g => decide (pinsOf (OFullK (14 * (2 * g + 1) + 4)) = [.pinI, .pin (2 * g + 1) 0])

set_option maxRecDepth 100000 in
theorem k5PinsB_full : k5PinsB 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A corollary of k5PinsB_full at g = 0, no negative test (given that theorem it cannot fail):
in front of group 0's sub-protocol the list is not [pinI, pin 3 0]. -/
theorem k5Pins_bite : decide (pinsOf (OFullK 18) = [.pinI, .pin 3 0]) = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test: the list is not [pinI, pin 1 0] at every border: not at the first. -/
theorem k5Pins_bite' : decide (pinsOf (OFullK 0) = [.pinI, .pin 1 0]) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem pFullK_length : PFullK.length = 358 := by decide +kernel

theorem k5_pins {g : ℕ} (hg : g < 12) : pinsOf (OFullK (14 * (2 * g + 1) + 4)) = [.pinI, .pin (2 * g + 1) 0] :=
  of_decide_eq_true (List.all_eq_true.1 k5PinsB_full g (List.mem_range.2 hg))

theorem pinI_open {g : ℕ} (hg : g < 12) : Item.pinI ∈ OFullK (14 * (2 * g + 1) + 4) :=
  (List.mem_filter.1 (show Item.pinI ∈ pinsOf (OFullK (14 * (2 * g + 1) + 4)) by rw [k5_pins hg]; exact List.mem_cons_self)).1

theorem pin0_open {g : ℕ} (hg : g < 12) : Item.pin (2 * g + 1) 0 ∈ OFullK (14 * (2 * g + 1) + 4) :=
  (List.mem_filter.1 (show Item.pin (2 * g + 1) 0 ∈ pinsOf (OFullK (14 * (2 * g + 1) + 4)) by
    rw [k5_pins hg]; exact List.mem_cons_of_mem _ List.mem_cons_self)).1

/-- A sampled tenant of an open pin is a tenant of one of the pins. -/
theorem sampled_of_pins (N : Numbers) (O : List Item) (t : ℕ × ℕ) (h : t ∈ sampledIn N O) : t ∈ sampledIn N (pinsOf O) := by
  obtain ⟨i, hi, ht⟩ := List.mem_flatMap.1 h
  refine List.mem_flatMap.2 ⟨i, List.mem_filter.2 ⟨hi, ?_⟩, ht⟩
  cases i <;> first | rfl | exact absurd ht (List.not_mem_nil)

/-- **At the kind's borders the field low says what lowI and low0 say together.** -/
theorem low_iff (N : Numbers) {g : ℕ} (hg : g < 12) (b : ℕ) :
    (∀ t ∈ sampledIn N (OFullK (14 * (2 * g + 1) + 4)), t.1 < b) ↔ N.index.1 < b ∧ ∀ t ∈ N.sent (2 * g + 1) 0, t.1 < b := by
  constructor
  · intro h
    exact ⟨h _ (List.mem_flatMap.2 ⟨_, pinI_open hg, List.mem_singleton.2 rfl⟩),
      fun t ht => h t (List.mem_flatMap.2 ⟨_, pin0_open hg, ht⟩)⟩
  · rintro ⟨h1, h2⟩ t ht
    have h3 := sampled_of_pins N _ t ht
    rw [k5_pins hg] at h3
    obtain ⟨i, hi, hti⟩ := List.mem_flatMap.1 h3
    rcases List.mem_cons.1 hi with rfl | hi
    · obtain rfl : t = N.index := List.mem_singleton.1 hti
      exact h1
    · obtain rfl : i = .pin (2 * g + 1) 0 := List.mem_singleton.1 hi
      exact h2 t hti

section
variable {C : CK} {Fr : Frame} {P S Cl W : Type} {num : Fmt.TreeSource → ℕ} {bs : List (Block S Cl)} {q : Piece C Fr (P × S) Cl W}

/-- **THREE FIELDS FROM ONE TEST.** -/
theorem low_of_fence (N₀ : Numbers) {g : ℕ} (hg : g < 12) (h : PieceMore num 0 (bs.map held) (14 * (2 * g + 1) + 4) q)
    (hb : blocksOk bs = true) (hf : fenceFit (N₀.withTold PFullK (toldOf bs)) LFullK PFullK = true) :
    (∀ t ∈ sampledIn (N₀.withTold PFullK (toldOf bs)) (OFullK (14 * (2 * g + 1) + 4)), t.1 < q.base) ∧
      (N₀.withTold PFullK (toldOf bs)).index.1 < q.base ∧
      ∀ t ∈ (N₀.withTold PFullK (toldOf bs)).sent (2 * g + 1) 0, t.1 < q.base := by
  have hl := seated_fenced h hb (N₀.withTold PFullK (toldOf bs)) LFullK PFullK
    (bookFit_withTold N₀ PFullK (toldOf bs) (ProofFile.Law.flatPlaces_nodup LFullK true)) hf (by rw [pFullK_length]; omega)
  exact ⟨hl, (low_iff _ hg _).1 hl⟩

end

end H2K5.Door

#print axioms H2K5.Door.k5PinsB_full
#print axioms H2K5.Door.k5Pins_bite
#print axioms H2K5.Door.k5Pins_bite'
#print axioms H2K5.Door.low_iff
#print axioms H2K5.Door.low_of_fence
