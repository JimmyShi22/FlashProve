-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PlacesAtFlat.lean: THE SMALLNESS TEST: THE PLACES OF A SEGMENT's BATCHING AND OF THE
MEMBER WITHOUT A ROUND BEHIND IT (`batchPlace`, `quietPlace`,
Johnson/Desc/ProofFile/Honest/K8/Falls.lean) HELD AGAINST THE PROOF FILE's DESCRIPTION's OWN LIST:
EACH STANDS AT ONE NUMBER OF THE FIRST CHAIN's FLAT LIST, AND NOWHERE ELSE. LEMMAS; NONE OF THE
LIBRARY's GOALS. No prover.

  `onlyAt ps a i`   a test with code: a stands in ps at number i and nowhere else; `onlyAt_gives`,
      `onlyAt_there`
  `placesB`, `placesB_full`   the test at the written list of the full size's places (flatPlacesOf
      linksFull true), at all 25 segments and both places: it says yes: a closed evaluation by
      Lean's kernel
  **`batch_place`**, **`quiet_place`**   in the goals' scope, at l < 25, o := 1 at the head's
      segment, else 0, K := 14 l + 9, or 347 at the head's: a member of the flat list that bears
      batchPlace l o stands at number K; one that bears quietPlace l o at K + 1
  `batch_there`, `quiet_there`   and the members at these numbers bear these places
By: LPFK9.blockPlaces_full (Johnson/LPFK9R/SubsFull.lean): in the goals' scope the flat list's
places are the written list.
Limits. The full size. The first chain.
-/
import Johnson.LPFK9R.SubsFull
import Johnson.Desc.ProofFile.Honest.K8.Falls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (linksFull)
open ProofFile.Honest.K8 (batchPlace quietPlace)

/-- a stands in ps at number i and nowhere else. -/
def onlyAt (ps : List Place) (a : Place) (i : Nat) : Bool :=
  ((ps.zipIdx.filter fun x => x.1 == a).map (·.2)) == [i]

theorem onlyAt_gives {ps : List Place} {a : Place} {i : Nat} (h : onlyAt ps a i = true) {n : Nat}
    (hn : ps[n]? = some a) : n = i := by
  have hm : (a, n) ∈ ps.zipIdx := List.mem_zipIdx_iff_getElem?.2 hn
  have h2 : n ∈ (ps.zipIdx.filter fun x => x.1 == a).map (·.2) :=
    List.mem_map.2 ⟨(a, n), List.mem_filter.2 ⟨hm, by simp⟩, rfl⟩
  unfold onlyAt at h
  rw [eq_of_beq h] at h2
  simpa using h2

theorem onlyAt_there {ps : List Place} {a : Place} {i : Nat} (h : onlyAt ps a i = true) :
    ps[i]? = some a := by
  unfold onlyAt at h
  have h2 : i ∈ (ps.zipIdx.filter fun x => x.1 == a).map (·.2) := by
    rw [eq_of_beq h]
    simp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h2
  obtain ⟨h3, h4⟩ := List.mem_filter.1 hx
  obtain ⟨y, n⟩ := x
  have e : y = a := by simpa using h4
  rw [← e]
  exact List.mem_zipIdx_iff_getElem?.1 h3

/-- The test at the written list, at all 25 segments and both places. -/
def placesB : Bool :=
  (List.range 25).all fun l =>
    onlyAt (flatPlacesOf linksFull true) (batchPlace l (if l = 24 then 1 else 0))
        (14 * l + (if l = 24 then 11 else 9)) &&
      onlyAt (flatPlacesOf linksFull true) (quietPlace l (if l = 24 then 1 else 0))
        (14 * l + (if l = 24 then 11 else 9) + 1)

set_option maxRecDepth 1000000 in
theorem placesB_full : placesB = true := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

theorem place_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (n : ℕ) :
    (flatPlacesOf linksFull true)[n]? = (c.blocksInOrder[n]?).map (·.place) := by
  rw [← LPFK9.blockPlaces_full hS hR O]
  show (c.blocksInOrder.map (·.place))[n]? = _
  rw [List.getElem?_map]

/-- **The batching's place stands at the batching's number alone.** -/
theorem batch_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) {n : ℕ}
    (h : (c.blocksInOrder[n]?).map (·.place) = some (batchPlace l (if l = 24 then 1 else 0))) :
    n = 14 * l + (if l = 24 then 11 else 9) := by
  have hB := List.all_eq_true.1 placesB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at hB
  exact onlyAt_gives hB.1 ((place_at hS hR O n).trans h)

/-- **The place of the member without a round stands at the next number alone.** -/
theorem quiet_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) {n : ℕ}
    (h : (c.blocksInOrder[n]?).map (·.place) = some (quietPlace l (if l = 24 then 1 else 0))) :
    n = 14 * l + (if l = 24 then 11 else 9) + 1 := by
  have hB := List.all_eq_true.1 placesB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at hB
  exact onlyAt_gives hB.2 ((place_at hS hR O n).trans h)

theorem batch_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    (c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]?).map (·.place) =
      some (batchPlace l (if l = 24 then 1 else 0)) := by
  have hB := List.all_eq_true.1 placesB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at hB
  exact (place_at hS hR O _).symm.trans (onlyAt_there hB.1)

theorem quiet_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    (c.blocksInOrder[14 * l + (if l = 24 then 11 else 9) + 1]?).map (·.place) =
      some (quietPlace l (if l = 24 then 1 else 0)) := by
  have hB := List.all_eq_true.1 placesB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at hB
  exact (place_at hS hR O _).symm.trans (onlyAt_there hB.2)

end

end P1K8

#print axioms P1K8.placesB_full
#print axioms P1K8.batch_place
#print axioms P1K8.quiet_place
#print axioms P1K8.batch_there
#print axioms P1K8.quiet_there
#print axioms P1K8.onlyAt
#print axioms P1K8.onlyAt_gives
#print axioms P1K8.onlyAt_there
#print axioms P1K8.placesB
#print axioms P1K8.place_at
