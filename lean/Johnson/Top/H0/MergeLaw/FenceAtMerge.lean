-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FenceAtMerge.lean: THE FENCE IN FRONT OF THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11), at the written list of places at the full size: every member that sits
at the index masks' tenant, or at a tenant of the output head's first sending, lies in a tree that
was sent in front of sub-protocol number 346. FROM ONE PREMISE, in the letters in which it lies
proved elsewhere: "every tenant whose pin is open at border 346 lies in a tree below base".

  fenced_of_low      a member that sits at a tenant of a tree below base is fenced at base
  mem_sampled_index, mem_sampled_sent   where the pin of the index masks' message (of segment m's
                     moment t) is open, its tenant is (its tenants are) among the sampled tenants of
                     that border
  openAtMerge        the items that are open at border 346, by the table of joints' own function
  openAtMerge_pins   A CLOSED FACT, by Lean's kernel: the pin of the index masks' message and the pin
                     of segment 24's moment 0 are open there
  openAtMerge_rings  the test can fail: no pin of a segment 25 is open there
  fence_at_merge     THE FENCE

Limits. The premise low is shown nowhere here. N, base and ms are letters. That sub-protocol number
346 is the merge is not said here. No soundness statement.

-/
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.Sound (Mem SitsAt Fenced linksFull)
open VerifiableInference.Desc.First (Item Numbers openSets start flatPlacesOf sampledIn)

/-- A member that sits at a tenant of a tree below base is fenced at base. -/
theorem fenced_of_low {base : Nat} {L : List (Nat × Nat)} (low : ∀ p ∈ L, p.1 < base)
    (ms : List Mem) : ∀ p ∈ L, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x] := by
  intro p hp x _ hs y hy
  obtain rfl := List.mem_singleton.1 hy
  have e : (y.1.seat y.2).1 = p.1 := congrArg Prod.fst hs
  rw [e]
  exact low p hp

theorem mem_sampled_index (N : Numbers) {O : List Item} (h : Item.pinI ∈ O) :
    N.index ∈ sampledIn N O := by
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨_, h, List.mem_singleton.2 rfl⟩

theorem mem_sampled_sent (N : Numbers) {O : List Item} {m t : Nat} (h : Item.pin m t ∈ O)
    {x : Nat × Nat} (hx : x ∈ N.sent m t) : x ∈ sampledIn N O := by
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨_, h, hx⟩

/-- The items that are open at border 346 of the written list at the full size. -/
def openAtMerge : List Item :=
  (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []

/-- **A closed fact**: the two pins are open there. -/
theorem openAtMerge_pins :
    (openAtMerge.contains Item.pinI && openAtMerge.contains (Item.pin 24 0)) = true := by
  decide +kernel

/-- The test can fail. -/
theorem openAtMerge_rings : openAtMerge.contains (Item.pin 25 0) = false := by
  decide +kernel

/-- **THE FENCE.** -/
theorem fence_at_merge (N : Numbers) (base : Nat)
    (low : ∀ x ∈ sampledIn N
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []),
      x.1 < base) (ms : List Mem) :
    ∀ p ∈ N.index :: N.sent 24 0, ∀ x ∈ ms, SitsAt x p.1 p.2 → Fenced base [x] := by
  have h := openAtMerge_pins
  rw [Bool.and_eq_true] at h
  have hI : Item.pinI ∈ openAtMerge := List.contains_iff_mem.1 h.1
  have hP : Item.pin 24 0 ∈ openAtMerge := List.contains_iff_mem.1 h.2
  refine fenced_of_low (fun p hp => low p ?_) ms
  rcases List.mem_cons.1 hp with rfl | hp
  · exact mem_sampled_index N hI
  · exact mem_sampled_sent N hP hp

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.fenced_of_low
#print axioms VerifiableInference.Desc.First.MergeLaw.openAtMerge_pins
#print axioms VerifiableInference.Desc.First.MergeLaw.openAtMerge_rings
#print axioms VerifiableInference.Desc.First.MergeLaw.fence_at_merge
