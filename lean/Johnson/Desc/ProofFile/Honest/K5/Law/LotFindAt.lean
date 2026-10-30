-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotFindAt.lean: CONDITIONAL: WHAT THE HONEST SIDE OF THE LOT OF
THE KIND "an attention segment's own rounds" (K5) HOLDS AT AN ATTENTION SEGMENT's PLACE, AT EVERY
PUBLIC PART Z AND EVERY GROUND G: the half at what the maker of the place's public data yields
there. No hypothesis on the public input. Statements with their proofs; no definition.

Why. A law that says which half the halves of several lots, laid one behind another, hold at a place
p asks of the lot L that is meant: (L.halves Z G).find? (fun x => x.place == p) = some g
(`firstOf_find`, `atPure_first_find`, Johnson/Desc/ProofFile/Honest/FirstFind.lean). `k5LotK_find`
(Honest/K5/Law/LotFind.lean) has that under the library's hypothesis on the public input, which is
typed at the full size alone, so it cannot be called at small public files. Of that hypothesis its
proof spends one fact: which attention segments the ground has. Here that fact is a premise, which a
look into the ground's list decides.

How. A member of a list in which no place comes twice is what the search at its place finds
(`find_own_place`; kin: `find_once`, Honest/K3/Law/Thread/SitePays.lean, with the same statement,
which is not imported: it lies over much more). That no place comes twice in the lot's own list, and
at which place a half stands: `k5LotK_places_once`, `seatAtK_place` (Honest/K5/Law/LotClean.lean).

Main names:
  `find_own_place`   the search at a member's own place
  `k5Places_of_built`   a segment of kind 1 in the ground's list is an attention segment (the
      converse of `mem_k5Places`, Honest/K5/Law/LotClean.lean)
  `k5LotK_find_at`   **y is an attention segment of G and the maker yields Y there: then
      ((k5LotK cells keyOf).halves Z G).find? (fun q => q.place == ⟨1, some y.1, 3, .K5⟩) =
      some (k5Half cells Y)**
  `k5LotK_find_built`   **the same from G.built[l]? = some Xl and Xl.kind = 1**
  `k5Places_inj`   within the list a segment's number tells the member
  `k5LotK_find_none_at`, `k5LotK_find_off`   two controls: no half where the maker yields nothing;
      none at a segment that is no attention segment

Premises of the two main statements. hy (or hX and hk): the ground has an attention segment there.
hY: the maker of the place's public data (`seatAtK`, Honest/K5/KeysFit.lean) yields there: its three
tests say yes.
Limits. Neither premise is shown at any public part here. Under the library's hypothesis on the
public input, so at the full size alone, hy follows from the ground's list of attention segments
(`k5Places_scope`, Johnson/Desc/First/Att/Row/K5RowSeat.lean), and hY is shown at the key points'
reader `keyOfK3` (`seatAt_returns_K3`, Honest/K5/Law/KeysFitK3.lean); the law there is
`k5LotK_find_K3` (Honest/K5/Law/LotFind.lean), by a proof of its own. AT SMALL PUBLIC FILES, FOR
WHICH THIS FORM IS MADE, NO THEOREM SHOWS EITHER. LENGTHS ALONE: the maker's third test asks the key
points' lengths, at challenges that are all 0. Nothing is said of other lots, nor of what a half
sends.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotClean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Place)

variable {W₀ Rc Xi Tr V W X : Type}

/-- A member of a list in which no place comes twice is what the search at its place finds. -/
theorem find_own_place : ∀ {hs : List (Placed V W X)} {x : Placed V W X}, x ∈ hs →
    (hs.map (·.place)).Nodup → hs.find? (fun q => q.place == x.place) = some x
  | [], _, hx, _ => by cases hx
  | a :: hs, x, hx, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact List.find?_cons_of_pos (by exact beq_self_eq_true _)
    · have hne : ¬ ((a.place == x.place) = true) := fun e =>
        hn.1 (List.mem_map.2 ⟨x, hx', (beq_iff_eq.1 e).symm⟩)
      rw [List.find?_cons_of_neg (p := fun q : Placed V W X => q.place == x.place) hne]
      exact find_own_place hx' hn.2

/-- A segment of kind 1 in the ground's list stands in the list of attention segments, with its
number, its name and its group. -/
theorem k5Places_of_built {G : Ground} {l : Nat} {Xl : LinkH} (hX : G.built[l]? = some Xl)
    (hk : Xl.kind = 1) : (l, Xl.name, Xl.g) ∈ H2K5.k5Places G := by
  unfold H2K5.k5Places
  refine List.mem_map.2 ⟨(Xl, l), List.mem_filter.2 ⟨?_, by simp [hk]⟩, rfl⟩
  rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList]
  exact hX

/-- **WHAT THE LOT's OWN LIST HOLDS AT AN ATTENTION SEGMENT's PLACE, WHERE THE MAKER YIELDS.** -/
theorem k5LotK_find_at (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {y : Nat × String × Nat} (hy : y ∈ H2K5.k5Places G) {Y : Seat5}
    (hY : seatAtK keyOf Z G y.1 y.2.1 y.2.2 = some Y) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G).find?
      (fun q => q.place == ⟨1, some y.1, 3, .K5⟩) = some (k5Half cells Y) := by
  have hm : k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y ∈
      (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G :=
    List.mem_filterMap.2 ⟨y, hy, by rw [hY]; rfl⟩
  have hp : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y).place =
      ⟨1, some y.1, 3, .K5⟩ := seatAtK_place hY
  rw [← hp]
  exact find_own_place hm (k5LotK_places_once cells keyOf Z G)

/-- **The same from a look into the ground's list.** -/
theorem k5LotK_find_built (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {l : Nat} {Xl : LinkH} (hX : G.built[l]? = some Xl) (hk : Xl.kind = 1) {Y : Seat5}
    (hY : seatAtK keyOf Z G l Xl.name Xl.g = some Y) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G).find?
      (fun q => q.place == ⟨1, some l, 3, .K5⟩) = some (k5Half cells Y) :=
  k5LotK_find_at cells keyOf Z G (k5Places_of_built hX hk) hY

/-- Within the list of attention segments a segment's number tells the member. -/
theorem k5Places_inj {G : Ground} {y z : Nat × String × Nat} (hy : y ∈ H2K5.k5Places G)
    (hz : z ∈ H2K5.k5Places G) (e : y.1 = z.1) : y = z := by
  obtain ⟨A, a1, -, a3, a4⟩ := mem_k5Places hy
  obtain ⟨B, b1, -, b3, b4⟩ := mem_k5Places hz
  rw [e, b1] at a1
  obtain rfl := Option.some.inj a1
  exact Prod.ext e (Prod.ext (a3.trans b3.symm) (a4.trans b4.symm))

/-- A control: **where the maker yields nothing, the lot's own list holds no half at the place**: so
the premise that the maker yields carries weight. -/
theorem k5LotK_find_none_at (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {y : Nat × String × Nat} (hy : y ∈ H2K5.k5Places G)
    (hN : seatAtK keyOf Z G y.1 y.2.1 y.2.2 = none) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G).find?
      (fun q => q.place == ⟨1, some y.1, 3, .K5⟩) = none := by
  rw [List.find?_eq_none]
  intro q hq hb
  obtain ⟨z, hz, hf⟩ := List.mem_filterMap.1 hq
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hf
  have hp : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y).place =
      ⟨1, some z.1, 3, .K5⟩ := seatAtK_place hY
  rw [hp, beq_iff_eq] at hb
  have e : z.1 = y.1 := Option.some.inj (congrArg Place.link hb)
  obtain rfl := k5Places_inj hz hy e
  rw [hN] at hY
  cases hY

/-- A control: **at a segment that is no attention segment the lot's own list holds no half**: so
the premise that the segment is one carries weight. -/
theorem k5LotK_find_off (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {l : Nat} (hl : ∀ y ∈ H2K5.k5Places G, y.1 ≠ l) :
    ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G).find?
      (fun q => q.place == ⟨1, some l, 3, .K5⟩) = none := by
  rw [List.find?_eq_none]
  intro q hq hb
  obtain ⟨z, hz, hf⟩ := List.mem_filterMap.1 hq
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hf
  have hp : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Y).place =
      ⟨1, some z.1, 3, .K5⟩ := seatAtK_place hY
  rw [hp, beq_iff_eq] at hb
  exact hl z hz (Option.some.inj (congrArg Place.link hb))

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.find_own_place
#print axioms ProofFile.Honest.K5.k5Places_of_built
#print axioms ProofFile.Honest.K5.k5LotK_find_at
#print axioms ProofFile.Honest.K5.k5LotK_find_built
#print axioms ProofFile.Honest.K5.k5Places_inj
#print axioms ProofFile.Honest.K5.k5LotK_find_none_at
#print axioms ProofFile.Honest.K5.k5LotK_find_off
