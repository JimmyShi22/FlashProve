-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanRestAtCut.lean:
"PlanAt's rest" (PlanRest, PlanParts.lean: the fields mems, seats, one, pad, row, fits) AT
THE WRITTEN VALUES, at all fifty later places of the kind K1; with the bases' numerals and the
closed half (iv) of the field told. Closed facts by Lean's kernel, each with a negative test, and
the sentences that follow from them. A law file; no running text imports it. The letters.
placeL l d, baseL3 l d := 3 * l + moment + 1 (MemsAtPlan.lean). P5T.N0Full (PlanSeatsFull.lean): the
core of the table's numbers off the written seats. countsFull: the two counts at the 359 borders
(Johnson/HB/LLHARD/ToldCounts.lean). NC, psF (Johnson/Desc/AtSeats/CandidateAtCut.lean). laidFull
(Johnson/Desc/AtSeats/TreesOpened.lean).
  later_seats: laterSeatsB P5T.N0Full (placeL l d) l moment (baseL3 l d) = true at all fifty: IT
      READS NO "told": of the numbers their field sent alone; later_seats_rejects: with the two
      moments exchanged, and one tree further, it rejects at every segment
  later_seats_of: so at every N with N.sent = P5T.N0Full.sent
  bases_counts, bases_NC: the number of trees in front of each of the fifty is baseL3 l d: in
      countsFull, and in NC.treesAt; bases_two: 0 at the opening, 82 at W's sending; bases_rejects
  seats_of_later: the field seats from the test, over letters
  seats_at: the field seats of PlanRest, its own text (seatOfMsg written out): each tenant of
      N0Full.sent l moment is the seat, behind baseL3 l d trees, of a message of the place that has
      an OOD sample
  laid_fifty, laid_two: (iv) of the field told: laidFull[base + n]? is the depth and the width of
      the place's own layout's tree n: at the fifty, at the opening, at W's sending; laid_rejects
  rest_at: the six fields together at placeL l d, from the code tables' equation, RadAt and fits

What is not claimed. RadAt and fits at any place: NO PAYER. That a computed place is placeL l d
(LikeFull, gp = ⟨1, 0⟩: another file's, in scope, under the door's pin). That the data's number of
trees in front is baseL3. AN EXAMPLE OF THE TOP IT IS NOT: it shows that these tests accept
TOGETHER at the written values. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.CandidateAtCut
import Johnson.Desc.AtSeats.MemsAtPlan
import Johnson.Desc.AtSeats.TreesOpened
import Johnson.Desc.K1.Law.HeldAtLater
import Johnson.Desc.K1.Law.PlanOwn
import Johnson.HB.LLHARD.ToldCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem SeatFits msOf)
open VerifiableInference.Desc.K13.Law (countsFull)
open _root_.Desc.K14.Law (pairsPlan)
open HashBuild (NC psF laidFull)
open IM (k1Ix)

/-- All fifty. -/
def fiftyB (f : ℕ → Bool → Bool) : Bool := (List.range 25).all fun l => f l false && f l true

theorem fifty_of {f : ℕ → Bool → Bool} (h : fiftyB f = true) (l : ℕ) (hl : l < 25) (d : Bool) :
    f l d = true := by
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h1
  cases d with
  | false => exact h1.1
  | true => exact h1.2

/-! ## seats -/

set_option maxRecDepth 1000000 in
/-- **The table's tenants of (segment, moment) are the place's seats.** -/
theorem later_seats : fiftyB (fun l d =>
    laterSeatsB P5T.N0Full (placeL l d) l (cond d 2 1) (baseL3 l d)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: the moments exchanged; one tree further: at no segment does it accept. -/
theorem later_seats_rejects : ((List.range 25).any fun l =>
    laterSeatsB P5T.N0Full (placeL l true) l 1 (baseL3 l true) ||
      laterSeatsB P5T.N0Full (placeL l true) l 2 (baseL3 l true + 1)) = false := by decide +kernel

theorem later_seats_of {N : Numbers} (hN : N.sent = P5T.N0Full.sent) (l : ℕ) (hl : l < 25)
    (d : Bool) : laterSeatsB N (placeL l d) l (cond d 2 1) (baseL3 l d) = true := by
  have h := fifty_of later_seats l hl d
  unfold laterSeatsB at h ⊢
  rw [hN]
  exact h

theorem place_is (l : ℕ) (d : Bool) : placeL l d = laterFull l d := rfl

/-- Each message of a later place has an OOD sample. -/
theorem sampled_at (l : ℕ) (hl : l < 25) (d : Bool) (j : Fin (shapesOf (placeL l d)).length) :
    sampledAt (placeL l d) j := by
  have h := List.all_eq_true.1 says_fifty l (List.mem_range.2 hl)
  have h1 := List.all_eq_true.1 h d (by cases d <;> simp)
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true (List.all_eq_true.1 h1.2 j (List.mem_finRange j))

/-- The field seats from the test, over letters. (planSeats_of,
Johnson/Desc/K1/Law/NewAtSending.lean, with seatOfMsg written out.) -/
theorem seats_of_later {N : Numbers} {P : Par} {m t nT : ℕ} (h : laterSeatsB N P m t nT = true)
    (hs : ∀ j : Fin (shapesOf P).length, sampledAt P j) : ∀ u ∈ N.sent m t,
    ∃ j : Fin (shapesOf P).length, sampledAt P j ∧
      u = (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0) := by
  intro u hu
  unfold laterSeatsB First.sameMembers at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h1 : u ∈ (List.range P.sent.size).map fun i =>
      (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) :=
    List.mem_of_elem_eq_true (h.2 u hu)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
  have hi' : i < (shapesOf P).length := by
    unfold shapesOf
    rw [List.length_map, Array.length_toList]
    exact List.mem_range.1 hi
  exact ⟨⟨i, hi'⟩, hs _, rfl⟩

/-- **The field seats.** -/
theorem seats_at (l : ℕ) (hl : l < 25) (d : Bool) : ∀ u ∈ P5T.N0Full.sent l (cond d 2 1),
    ∃ j : Fin (shapesOf (placeL l d)).length, sampledAt (placeL l d) j ∧
      u = (baseL3 l d + (layOf (placeL l d)).tree.getD j.val 0,
        (layOf (placeL l d)).part.getD j.val 0) :=
  seats_of_later (fifty_of later_seats l hl d) (sampled_at l hl d)

/-! ## The bases -/

set_option maxRecDepth 1000000 in
/-- **The trees in front of each of the fifty**, in the written counts. -/
theorem bases_counts : fiftyB (fun l d =>
    (countsFull[14 * l + k1Ix l d + 2]?).map (·.2) == some (baseL3 l d)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The like in the candidate numbers. -/
theorem bases_NC : fiftyB (fun l d =>
    NC.treesAt psF[14 * l + k1Ix l d + 2]? == baseL3 l d) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem bases_two : ((countsFull[2]?).map (·.2), (countsFull[356]?).map (·.2), NC.treesAt psF[2]?,
    NC.treesAt psF[356]?) = (some 0, some 82, 0, 82) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one border further the count parts, at every one of the fifty. -/
theorem bases_rejects : ((List.range 25).any fun l => [false, true].any fun d =>
    (countsFull[14 * l + k1Ix l d + 3]?).map (·.2) == some (baseL3 l d)) = false := by
  decide +kernel

/-! ## (iv) of the field told -/

/-- A tree's depth and width. -/
def wd (t : TreeShape) : ℕ × ℕ := (t.logN, t.mainWidth + t.maskWidth)

/-- The written table has the place's own layout's trees from base on. -/
def laidAtB (tab : List (ℕ × ℕ)) (P : Par) (base : ℕ) : Bool :=
  decide (0 < (layOf P).shapes.size) && (List.range (layOf P).shapes.size).all fun n =>
    tab[base + n]? == ((layOf P).shapes[n]?).map wd

set_option maxRecDepth 1000000 in
theorem laid_fifty : fiftyB (fun l d => laidAtB laidFull (placeL l d) (baseL3 l d)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem laid_two : (laidAtB laidFull (firstPar qFull ⟨1, 0⟩) 0 &&
    (linMessageW qFull.lin).any fun msg => laidAtB laidFull (parW qFull ⟨1, 0⟩ 4 msg) 82) =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree further the table parts from the layout at (0, true) and at the
opening. -/
theorem laid_rejects : (laidAtB laidFull (placeL 0 true) (baseL3 0 true + 1) ||
    laidAtB laidFull (firstPar qFull ⟨1, 0⟩) 1) = false := by decide +kernel

theorem laid_at (l : ℕ) (hl : l < 25) (d : Bool) (n : ℕ)
    (hn : n < (layOf (placeL l d)).shapes.size) :
    laidFull[baseL3 l d + n]? = ((layOf (placeL l d)).shapes[n]?).map wd := by
  have h := fifty_of laid_fifty l hl d
  unfold laidAtB at h
  rw [Bool.and_eq_true] at h
  exact eq_of_beq (List.all_eq_true.1 h.2 n (List.mem_range.2 hn))

/-! ## The six fields together -/

/-- **PlanRest's six fields at a later place, at the members by the make**: from the code tables'
equation, the one equation on the radii, and fits. -/
theorem rest_at {Xi : Type} {cs : Codes} (G : FileDescription Xi) {radM : ℕ → ℕ → ℕ} {rad : ℕ → ℕ} (l : ℕ)
    (hl : l < 25) (d : Bool) (hc : cs = (placeL l d).codes)
    (hr : RadAt Johnson.G.proofSendsFull.1.sends.length radM P5T.psFull (placeL l d) rad
      (baseL3 l d))
    (hf : ∀ x ∈ msOf (P5T.memberListsR Johnson.G.proofSendsFull.1.sends.length radM P5T.psFull),
      SeatFits G cs x.1.l x.1.seat) :
    MemsAt cs (msOf (P5T.memberListsR Johnson.G.proofSendsFull.1.sends.length radM P5T.psFull))
        (placeL l d) rad (baseL3 l d) ∧
      (∀ u ∈ P5T.N0Full.sent l (cond d 2 1),
        ∃ j : Fin (shapesOf (placeL l d)).length, sampledAt (placeL l d) j ∧
          u = (baseL3 l d + (layOf (placeL l d)).tree.getD j.val 0,
            (layOf (placeL l d)).part.getD j.val 0)) ∧
      PlanOwn (placeL l d) ∧
      ∀ x ∈ msOf (P5T.memberListsR Johnson.G.proofSendsFull.1.sends.length radM P5T.psFull),
        SeatFits G cs x.1.l x.1.seat := by
  refine ⟨memsAt_byMake hc ?_ hr, seats_at l hl d, ?_, hf⟩
  · have h := List.all_eq_true.1 mems_fifty l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at h
    cases d with
    | false => exact h.1
    | true => exact h.2
  · have h := List.all_eq_true.1 own_fifty l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at h
    cases d with
    | false => exact planOwn_of h.2
    | true => exact planOwn_of h.1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.later_seats
#print axioms VerifiableInference.Desc.K1.later_seats_rejects
#print axioms VerifiableInference.Desc.K1.later_seats_of
#print axioms VerifiableInference.Desc.K1.seats_at
#print axioms VerifiableInference.Desc.K1.bases_counts
#print axioms VerifiableInference.Desc.K1.bases_NC
#print axioms VerifiableInference.Desc.K1.bases_two
#print axioms VerifiableInference.Desc.K1.bases_rejects
#print axioms VerifiableInference.Desc.K1.laid_fifty
#print axioms VerifiableInference.Desc.K1.laid_two
#print axioms VerifiableInference.Desc.K1.laid_rejects
#print axioms VerifiableInference.Desc.K1.laid_at
#print axioms VerifiableInference.Desc.K1.rest_at
