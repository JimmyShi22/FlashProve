-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/CellsAtName.lean: the table of cells that the approximate range proof's tie reads
(`cellsAt`, Johnson/Desc/Sound/CellsAt.lean), at an array's number whose name is known. Two
theorems.
Why. In the composed meaning of the open claims (`mgAll`, Johnson/Desc/Sound/MgAll.lean) the tie
reads
the witness through `cellsAt`, by an array's NUMBER in the open segment's list; the claims on linear
forms read it through `dataQ` (Johnson/Desc/Sound/FormsQ.lean), by the array's NAME. Whoever joins
the
two (the exchange at a segment's second sending: Johnson/Desc/Sound/StatedCell.lean's `ArmCell`)
wants
one equation between them.
  `link_of_segAt`: where the verifier's state has an open segment's part, its open link's context is
  that
    part's.
  `cellsAt_name`: at such a state, at an array's number t at which the part's list of arrays holds
  the
    name c: `cellsAt cs arr ms N m (z, s) w t r i` is `dataQ`'s cell at c, row r, place i.
Limits: an unfolding. That the numbers which the tie reads are numbers of that list is not said
here.
No soundness is claimed.

-/
import Johnson.Desc.Sound.CellsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Numbers)

theorem link_of_segAt (s : First.S) (p : K9.Part) (h : K9.segAt? s = some p) :
    s.link? = some p.L := by
  unfold K9.segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases hT : s.tl? with
      | none => simp [hL, hF, hT] at h
      | some tl =>
        simp [hL, hF, hT] at h
        rw [← h]

theorem cellsAt_name {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (m : ℕ) (z : P) (s : First.S) (w : Wit Cells Tok MsgT) (p : K9.Part)
    (h : K9.segAt? s = some p) (t : ℕ) (c : ℕ × String) (hc : p.L.arrayOf[t]? = some c) (r i : ℕ) :
    cellsAt cs arr ms N m (z, s) w t r i =
      (dataQ (N.group m) p (seatTab cs arr ms w)).cell c.1 c.2 r i := by
  rw [cellsAt_of_part cs arr ms N m (z, s) w t r i p h]
  have e : ((s.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default =
      c := by
    rw [link_of_segAt s p h]
    simp [Array.getD_eq_getD_getElem?, hc]
  show (dataQ (N.group m) p (seatTab cs arr ms w)).cell
    (((s.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default).1
    (((s.link?.map fun (L : OnBytes.Model.LinkCtx) => L.arrayOf).getD #[]).getD t default).2 r i = _
  rw [e]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.link_of_segAt
#print axioms VerifiableInference.Desc.Sound.cellsAt_name
