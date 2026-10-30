-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/RadAtRows.lean: RadAt (Johnson/Desc/AtSeats/MemsAtPlan.lean: the one equation on the
radii that the field mems of PlanAt leaves) AT ALL FIFTY LATER PLACES, FROM ONE EQUATION ON THE ROWS
OF THE SENDINGS: that the first proof chain's rows have the written radii (radsFull,
Johnson/HB/LLHARD/RadiiWritten.lean). A joining of what lies. A law file; no running text imports
it.
  radF k i: the radius that radsFull has at (sending k, place i); 0 where it has none
  read_of_map: the two readers (radW's, P5T.radOf's) are one: over letters
  lit_is_rads: K1's files' written list (litAt sendsFullLit packFullLit 2 0) has, sending by
      sending, just radsFull's pairs: Lean's kernel; lit_rejects: the negative test
  radW_is: so radW k i = radF k i at every k i
  radOf_is: where the rows' first proof chain has radsFull's pairs, the reader
      P5T.radOf R k i is radF k i at every k i
  radAt_written: RadAt at radW, at each of the fifty (from rad_written)
  radAt_of_rows: RadAt at radM := P5T.radOf R, at each of the fifty, at the written seats, from hR
      : (P5T.firstRows R).map (·.sampled) = radsFull

One premise stays: hR: typed in scope in RadiiInScope.lean (radii_in_scope).
Evaluated true at the stored full-size set's public files through radFiftyB.
Nothing on soundness.

-/
import Johnson.Desc.AtSeats.RadAtTest
import Johnson.HB.LLHARD.RadiiWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open Johnson.G (sendsFullLit packFullLit radsFull)
open IM (k1Ix)

/-- The written radius at (sending, place); 0 where there is none. -/
def radF (k i : ℕ) : ℕ := ((radsFull.getD k []).getD i default).2

/-- **The two readers are one**, over letters. -/
theorem read_of_map {α : Type} (L : List α) (f : α → List (OracleShape × ℕ))
    (R : List (List (OracleShape × ℕ))) (h : L.map f = R) (k i : ℕ) :
    ((((L[k]?).bind fun y => (f y)[i]?).map (·.2)).getD 0) =
      ((R.getD k []).getD i default).2 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[k]? with
  | none => rfl
  | some y =>
    show ((((f y)[i]?).map (·.2)).getD 0) = (((f y)[i]?).getD default).2
    cases (f y)[i]? <;> rfl

set_option maxRecDepth 1000000 in
/-- **K1's files' written list has radsFull's pairs.** -/
theorem lit_is_rads : (litAt sendsFullLit packFullLit 2 0).map (·.2.l) = radsFull := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the list of another chain of the proof file parts from it. -/
theorem lit_rejects : decide ((litAt sendsFullLit packFullLit 2 1).map (·.2.l) = radsFull) =
    false := by decide +kernel

theorem radW_is (k i : ℕ) : radW k i = radF k i :=
  read_of_map (litAt sendsFullLit packFullLit 2 0) (fun y => y.2.l) radsFull lit_is_rads k i

theorem radOf_is {R : List Johnson.G.SendRow}
    (hR : (P5T.firstRows R).map (·.sampled) = radsFull) (k i : ℕ) : P5T.radOf R k i = radF k i :=
  read_of_map (P5T.firstRows R) (fun r => r.sampled) radsFull hR k i

theorem radAt_written (l : ℕ) (hl : l < 25) (d : Bool) :
    RadAt Johnson.G.proofSendsFull.1.sends.length radW P5T.psFull (placeL l d)
      (radRec (3 * l + cond d 2 1) (placeL l d)) (baseL3 l d) :=
  radFifty_at rad_written l hl d

/-- **RadAt at the radii P5T.radOf, from the one equation on the rows.** -/
theorem radAt_of_rows {R : List Johnson.G.SendRow}
    (hR : (P5T.firstRows R).map (·.sampled) = radsFull) (l : ℕ) (hl : l < 25) (d : Bool) :
    RadAt Johnson.G.proofSendsFull.1.sends.length (P5T.radOf R) P5T.psFull (placeL l d)
      (radRec (3 * l + cond d 2 1) (placeL l d)) (baseL3 l d) := by
  intro j hj k hk i p hp hs
  rw [radOf_is hR, ← radW_is]
  exact radAt_written l hl d j hj k hk i p hp hs

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.read_of_map
#print axioms VerifiableInference.Desc.K1.lit_is_rads
#print axioms VerifiableInference.Desc.K1.lit_rejects
#print axioms VerifiableInference.Desc.K1.radW_is
#print axioms VerifiableInference.Desc.K1.radOf_is
#print axioms VerifiableInference.Desc.K1.radAt_written
#print axioms VerifiableInference.Desc.K1.radAt_of_rows
