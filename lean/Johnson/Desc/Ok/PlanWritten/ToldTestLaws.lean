-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/ToldTestLaws.lean: what an accept and a reject of the test of
ToldTest.lean say; that its written numbers are those of PlaceNums.lean; negative tests. Statements
and proofs; three definitions of placeholders for the negative tests.

  `toldPinned_eq`      an accept at the full size's key: the equation at each of the 25 pairs
  `toldPinned_other`   at another key: accept
  `toldPinned_no`      WHAT A REJECT SAYS: the key is the full size's, and at one of the 25 pairs
                       the number told is another
  `told_of_pinnedAt`   the form to call, at a scan P with the full size's key
  `cuts_are_n0`        the written pairs are (14 l + 2, n0At l) for l = 1 … 23, (339, n0At 24) and
                       (353, n0At 25): by Lean's kernel
  `told_n0`            so, at an accept: `toldBefore F.first.blocksInOrder k = n0At l` at these 25 (l, k)
  `teller`, `patternAt`, `honestList`: placeholders: a sub-protocol that tells n messages and does
                       nothing else; a list of 358 that tells, in front of the last switch, as
                       the full size's first chain does
  `pinned_self`        the test accepts `honestList`
  `plant_more`, `plant_less`, `plant_moved`: negative tests: one message more, one fewer, one
                       teller moved behind a switch: reject
  `plant_other_key`    at another key the first of these is accepted
Limits. Those of ToldTest.lean. That a verifier asks the test is not said here. `honestList` is made
up to the pattern that an evaluation at the stored full-size files showed (three tellers in each
link; from number 353 on, where that chain tells 14 more, it tells nothing); it is no IOP. Nothing
on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.ToldTest
import Johnson.Top.H0.K2Hears.PlaceNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open VerifiableInference.Desc
open VerifiableInference.Desc.First.K2 (n0At)

variable {S Cl : Type}

/-- **An accept at the full size's key.** -/
theorem toldPinned_eq {bs : List (Block S Cl)} (h : toldPinned fullKey bs = true) :
    ∀ x ∈ switchCuts, toldBefore bs x.1 = x.2 := by
  unfold toldPinned at h
  rw [if_pos rfl] at h
  intro x hx
  exact eq_of_beq (List.all_eq_true.1 h x hx)

theorem toldPinned_other {key : Nat × Nat × Nat} (bs : List (Block S Cl)) (hk : key ≠ fullKey) :
    toldPinned key bs = true := by
  unfold toldPinned
  rw [if_neg hk]

/-- **What a reject says.** -/
theorem toldPinned_no {key : Nat × Nat × Nat} {bs : List (Block S Cl)}
    (h : toldPinned key bs = false) :
    key = fullKey ∧ ∃ x ∈ switchCuts, toldBefore bs x.1 ≠ x.2 := by
  by_cases hk : key = fullKey
  · refine ⟨hk, ?_⟩
    unfold toldPinned at h
    rw [if_pos hk] at h
    obtain ⟨x, hx, hn⟩ := List.all_eq_false.1 h
    exact ⟨x, hx, fun e => hn (by rw [e]; exact beq_self_eq_true _)⟩
  · rw [toldPinned_other bs hk] at h
    cases h

/-- **The form to call.** -/
theorem told_of_pinnedAt {Xi : Type} {P : OnBytes.Model.PolScan} {F : FileDescription Xi}
    (h : toldPinnedAt P F = true) (hk : keyOfScan P = fullKey) :
    ∀ x ∈ switchCuts, toldBefore F.first.blocksInOrder x.1 = x.2 := by
  unfold toldPinnedAt at h
  rw [hk] at h
  exact toldPinned_eq h

set_option maxRecDepth 1000000 in
/-- **The written pairs are PlaceNums.lean's numbers at the 25 switches.** -/
theorem cuts_are_n0 : switchCuts =
    (List.range' 1 23).map (fun l => (14 * l + 2, n0At l)) ++ [(339, n0At 24), (353, n0At 25)] := by
  decide +kernel

/-- **At an accept the messages told in front of the switch into group l are `n0At l`.** -/
theorem told_n0 {Xi : Type} {P : OnBytes.Model.PolScan} {F : FileDescription Xi}
    (h : toldPinnedAt P F = true) (hk : keyOfScan P = fullKey) :
    (∀ l, 1 ≤ l → l ≤ 23 → toldBefore F.first.blocksInOrder (14 * l + 2) = n0At l) ∧
      toldBefore F.first.blocksInOrder 339 = n0At 24 ∧ toldBefore F.first.blocksInOrder 353 = n0At 25 := by
  have H := told_of_pinnedAt h hk
  rw [cuts_are_n0] at H
  refine ⟨fun l h1 h2 => ?_, ?_, ?_⟩
  · exact H (14 * l + 2, n0At l) (List.mem_append_left _ (List.mem_map.2
      ⟨l, by rw [List.mem_range'_1]; omega, rfl⟩))
  · exact H (339, n0At 24) (List.mem_append_right _ (by simp))
  · exact H (353, n0At 25) (List.mem_append_right _ (by simp))

/-! ### Negative tests -/

/-- A placeholder: a sub-protocol that tells n messages in one tree, and does nothing else. -/
def teller (n : Nat) : Block Unit Unit :=
  { roundlessBlock "placeholder" 1 none 0 (fun s => .ok s) with
    oracles := [[{ logLength := 0, words := 0
                   tenants := List.replicate n
                     { main := 0, mask := 0, degree := 0, sampled := false, groups := [] } }]] }

/-- What the sub-protocol number i of the full size's first chain tells, by the pattern of three
tellers in each link. -/
def patternAt (i : Nat) : Nat :=
  if i < 338 then
    (if i % 14 = 2 then (if i = 2 ∨ (i / 14) % 2 = 1 then 5 else 6)
      else if i % 14 = 5 ∨ i % 14 = 7 then 1 else 0)
  else if i = 339 then 4 else if i = 342 ∨ i = 344 then 1 else 0

/-- A placeholder list of 358 that tells by that pattern. -/
def honestList : List (Block Unit Unit) := (List.range 358).map fun i => teller (patternAt i)

set_option maxRecDepth 1000000 in
theorem pinned_self : toldPinned fullKey honestList = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One message more, at the first teller: reject. -/
theorem plant_more : toldPinned fullKey (honestList.set 2 (teller 6)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One message fewer, in the last link but one: reject. -/
theorem plant_less : toldPinned fullKey (honestList.set 329 (teller 0)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A teller moved from in front of the second switch to behind it: reject. -/
theorem plant_moved :
    toldPinned fullKey ((honestList.set 21 (teller 0)).set 31 (teller 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem plant_other_key :
    toldPinned (48, 5120, 202049) (honestList.set 2 (teller 6)) = true := by decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.toldPinned_eq
#print axioms VerifiableInference.PlanWritten.toldPinned_other
#print axioms VerifiableInference.PlanWritten.toldPinned_no
#print axioms VerifiableInference.PlanWritten.told_of_pinnedAt
#print axioms VerifiableInference.PlanWritten.cuts_are_n0
#print axioms VerifiableInference.PlanWritten.told_n0
#print axioms VerifiableInference.PlanWritten.pinned_self
#print axioms VerifiableInference.PlanWritten.plant_more
#print axioms VerifiableInference.PlanWritten.plant_less
#print axioms VerifiableInference.PlanWritten.plant_moved
#print axioms VerifiableInference.PlanWritten.plant_other_key
