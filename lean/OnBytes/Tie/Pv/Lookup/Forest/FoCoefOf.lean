-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoCoefOf.lean: CoefOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean)
from the success of HTailF2.piecesF and a shorter list of facts on public data.

 - coefOK_of_pieces: let piecesF return tl. Then CoefOK tl Fc holds if BZ is not ZZ, no matrix's
   array is BZ or ZZ, BZ has 32 rows, and the state Fc has BZ's virtual rows 0, 1, 2 and ZZ's
   virtual rows below 2 * zzBlocks. What CoefOK says of the pieces (their rows differ; none is a row
   under powers, a row of BZ, a matrix's row) follows.

Not claimed: anything on soundness, completeness or hiding.
Nor are the facts that are left claimed here: HTailF2.shapeF and addTreesF are to lay them, and the
routines between addTreesF and coefficientsF are to keep them.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes
import OnBytes.Tie.Pv.Lookup.Forest.FoPiecesF

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem coefOK_of_pieces {tl₀ tl : HTailF2} (h : tl₀.piecesF = .ok tl) (Fc : Fork)
    (hZ : tl.ix.BZ ≠ tl.ix.ZZ)
    (hm : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ ∧ tl.gtTree.getD mu 0 ≠ tl.ix.ZZ)
    (hR : (Fc.trees.getD tl.ix.BZ {}).R = 32)
    (hB : HasRow Fc tl.ix.BZ 0 ∧ HasRow Fc tl.ix.BZ 1 ∧ HasRow Fc tl.ix.BZ 2)
    (hr : ∀ i < 2 * tl.zzBlocks, HasRow Fc tl.ix.ZZ i) : CoefOK tl Fc where
  bz := hB
  bzR := hR
  mats := fun mu hmu => (hm mu hmu).1
  apart := pieces_apart h
  piece := fun a ha => by
    obtain ⟨e1, e2⟩ := pieces_low h a ha
    refine ⟨e1 ▸ hr a.2.row e2, (pieces_not_powers h a ha).1, (pieces_not_powers h a ha).2,
      e1 ▸ hZ, fun mu hmu e => (hm mu hmu).2 (e.1.trans e1)⟩

end Fo
