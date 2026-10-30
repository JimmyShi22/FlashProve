-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawGoodCapT.lean: THE LAW OF THE SUB-PROTOCOL OF KIND K8 (the approximate
range proof) IN WHICH THE VERIFIER SAMPLES THE MATRIX, AT TWO TABLES OF CELLS GIVEN OUTRIGHT, IN THE
FORM THAT THE TABLE OF JOINTS ASKS OF A SUB-PROTOCOL (`Piece.GoodIn`,
Johnson/Desc/Sound/GoodIn.lean), AT THE CAP: the list of errors `Err.cap 128` (Iop/ErrCap.lean): at
each round the number of its challenges / 2 ^ 128. Two statements, proved: calls alone.

WHENCE. This file is Johnson/Desc/First/K8/LawGoodCap.lean [not in this library] (no coding theory, no mark), typed again
over `k08_rowT_cap`
(Johnson/Desc/First/K8/LawTable.lean) in the place of `k08_row_place`
(Johnson/Desc/First/K8/LawRow.lean): the same `Piece` (a Lean structure), the same three steps, the
same two forms. What parts: the cells are read through two tables (array, row, column) ↦ field
element, not through a layout of committed entries over a finite index set; the part of the
verifier's state at which the law is stated is a letter tl0 with the premise `PlaceRec p tl0`, not
`recP tlL p`.

  **`k08_goodInT_cap`**: the `Piece` that holds the sub-protocol's own text `approximateRangeProofDrawKind atS p`, the one
    written round `rdt p`, no round behind, the extractor that hands the witness back, and the cap
    as its errors, is good between the two conditions and the two relations of `k08_rowT_cap`, to
    the letter, at that law's own premises (hE, hgt, hu, hP, hτ).
  `k08_goodInT_cap_whole`: the same at the numbers `p.toPar` of a place of the kind, whole
    (`ParW`, Johnson/Desc/First/K8/Whole.lean), at the one type of a claim.

How. `k08_rowT_cap` gives the law at the least error and "at most 2 ^ -128 a round"; so at most the
cap (`Err.le_cap_of_below_inv`); larger errors give a weaker statement (`Doomed.mono_err`,
Iop/Rbr.lean). The two structures part in their errors alone. At an extractor that hands the witness
back `Piece.GoodIn` and `Reduction.KeepsW` (Johnson/Desc/Plain/World.lean) unfold to one sentence:
Lean takes the one for the other by unfolding.

Limits. Those of `k08_rowT_cap`: its five premises stand as premises, shown at no value here; its
two conditions and two relations are that file's own. NO MEMBER IS SHOWN: a law at a condition that
holds of nothing is true and empty. Of the kind's three runs of claims nothing is said. No soundness
of any verifier follows from this file.

-/
import Johnson.Desc.First.K8.LawTable
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.Sound.GoodIn
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → ℕ → ℕ → ℕ → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
  (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)

/-- **The law at two tables, in the table of joints' form, at the cap.** -/
theorem k08_goodInT_cap (Cl : Type) (F : Frame) (p : Par) (base : ℕ)
    (hseat : ∀ i, (seat' i).1 < base)
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0) (hτ : p.tau = 128) :
    (⟨approximateRangeProofDrawKind (Cl := Cl) atS p, base, [rdt p], [], fun _ _ w => w,
        Err.cap 128 (uLT (Run.ckP .two) [rdt p])⟩ :
      Piece (Run.ckP .two) F S Cl (Wit Cells Tok MsgT)).GoodIn
      (fun a => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onA a ∧ Extra a.1)
      (fun b => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Cl F p base
        (leastAt p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧ TieAt entW a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧ SmallAt entW b.1 w ∧
        DigitsAt entW b.1 w) := by
  intro a ha
  obtain ⟨hK, hB⟩ := k08_rowT_cap tl0 cs l seat' arr entE entW G smpOf hs Cl F p base hseat hE hgt
    hu hP hτ
  exact Doomed.mono_err _ (Err.le_cap_of_below_inv 128 _ hB) (hK a ha)

/-- At the numbers of a place of the kind, whole, at the one type of a claim. -/
theorem k08_goodInT_cap_whole (F : Frame) (p : ParW) (base : ℕ)
    (hseat : ∀ i, (seat' i).1 < base)
    (hE : ∀ w t r c, early tl0 (.cell t r c) = true →
      entE (msgsOf cs l seat' arr w) t r c = entW w t r c)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p.toPar tl0) (hτ : p.tau = 128) :
    (⟨approximateRangeProofDrawKind (Cl := Claim) atS p.toPar, base, [rdt p.toPar], [], fun _ _ w => w,
        Err.cap 128 (uLT (Run.ckP .two) [rdt p.toPar])⟩ :
      Piece (Run.ckP .two) F S Claim (Wit Cells Tok MsgT)).GoodIn
      (fun a => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Claim F p.toPar base
        (leastAt p.toPar (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onA a ∧ Extra a.1)
      (fun b => (tabReads tl0 cs l seat' arr entE entW G smpOf hs Claim F p.toPar base
        (leastAt p.toPar (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) hseat).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧ TieAt entW a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧ SmallAt entW b.1 w ∧
        DigitsAt entW b.1 w) :=
  k08_goodInT_cap tl0 cs l seat' arr entE entW G smpOf hs Claim F p.toPar base hseat hE hgt hu hP
    hτ

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_goodInT_cap
#print axioms VerifiableInference.Desc.First.K8.k08_goodInT_cap_whole
