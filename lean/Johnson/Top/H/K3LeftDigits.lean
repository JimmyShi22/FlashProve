-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LeftDigits.lean: the kind "lookup" (K3): WHAT STANDS BEHIND A YES, AT THE SEAT OF
THE LOOKUP ON THE SMALLNESS TEST's DIGITS: the twin of K3LeavesAtCalls
(Johnson/Top/H/K3LeftStatement.lean) and of k3LeavesAtCalls_of (Johnson/Top/H/K3LeftProof.lean),
whose proof it follows line by line with the digits' seat's own lemmas. One definition of type Prop
and one theorem.

Main names.
  K3LeavesAtDigits: K3.block's decide at seatDigits leaves the record K3Left (K3DecideLeaves), at
    every place whose parameters make a shape.
  k3LeavesAtDigits_of: it is so, UNDER THE ONE NAMED PREMISE LkPadCEnd (K3LeftProof.lean), which is
    proved in Johnson/Top/H/K3CEnd.lean (lkPadCEnd): Johnson/Desc/First/Look/K3DigitsLookOut.lean
    calls it there.
OBJECT. Desc.K3.block's decide at Desc.K3.seatDigits.
USER. k3LeavesAtDigits (K3DigitsLookOut.lean).
LETTERS. All of K3LeavesAtDigits' are bound in it.
Where each field comes from: heardIs, padLeft: k3DecideHears_digits · shape: shapeOf_unique,
shape_some · zx, zy, zkSize, zkRaw: block_point_digits · zkLen: decide_zk_size · eRaw: lkPad_e ·
cEndEnts, cEndFilled: LkPadCEnd.
Limits. A tie: no error term. Nothing where decide refuses.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- **K3.block's decide at the digits' seat leaves the record.** -/
def K3LeavesAtDigits : Prop :=
  ∀ (Cl : Type) (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (h : Forest.Shape), p.shape = some h →
    K3DecideLeaves (Desc.K3.seatDigits claim).fork (Desc.K3.seatDigits claim).heard h
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide

/-- **It is so**, under the one named premise. -/
theorem k3LeavesAtDigits_of (hC : Fo.Tp.LkPadCEnd) : K3LeavesAtDigits := by
  intro Cl claim piece laid before p guests h hsh K _ ρ lm s s' rs cols hw hdec
  obtain ⟨F, F', g, hF, hF', hg, -, hS⟩ :=
    k3DecideHears_digits claim piece laid before p guests K ρ lm s s' rs cols hw hdec
  refine ⟨F, F', g, hF, hF', hg, fun hSz => ?_⟩
  obtain ⟨hShape, hPad, hI⟩ := hS hSz
  obtain rfl : g.shape = h := shapeOf_unique hShape (shape_some p h hsh)
  -- the points, as machine words
  obtain ⟨g1, hg1, -, hx, hy, hk, hz⟩ :=
    Desc.K3.block_point_digits claim piece laid before p guests hdec
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans hg1)
  obtain ⟨g2, hg2, hn⟩ := decide_zk_size (Desc.K3.seatDigits claim) piece laid before p guests
    (Desc.K3.seatDigits_reads claim) s s' rs cols hdec
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans hg2)
  -- lkPad's own yes
  obtain ⟨F3, F3', g3, t, hF3, hn3, hl, e3⟩ :=
    decide_lkPad (Desc.K3.seatDigits claim) piece laid before p guests s s' rs cols hdec
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF3]
    rfl
  obtain rfl : F = F3 := Option.some.inj (hF.symm.trans hF3)
  have hg3 : (Desc.K3.seatDigits claim).heard s' = some g3 := by
    rw [e3]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn3
  have hF3' : (Desc.K3.seatDigits claim).fork s' = some F3' := by
    rw [e3]
    exact seatDigits_keeps claim _ _ _ hsome hn3
  obtain rfl : g = g3 := Option.some.inj (hg.symm.trans hg3)
  obtain rfl : F' = F3' := Option.some.inj (hF'.symm.trans hF3')
  obtain ⟨c1, c2⟩ := hC _ _ _ _ _ _ _ _ hl hSz
  exact
    { heardIs := hI, padLeft := hPad, shape := rfl, zx := hx, zy := hy, zkSize := hk, zkRaw := hz,
      zkLen := hn, eRaw := Fo.Tp.lkPad_e _ _ _ _ _ _ _ _ hl, cEndEnts := c1, cEndFilled := c2 }

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3LeavesAtDigits_of
