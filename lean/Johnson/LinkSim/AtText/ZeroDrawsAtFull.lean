-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ZeroDrawsAtFull.lean: at the full size and the verifier message whose hash
blocks are all 0, the point at which the link's prover folds the tables' rows is 0, and so is the
point of the link proof's own first OOD sample.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. At the full-size parameters (frS, dsFull), with the challenges computed from
zeroRho dsFull (drawsZero; Johnson/LinkSim/AtText/ZeroDraws.lean):
  fr_lGam_zero    the point lGam at which the prover's algorithm folds the tables' rows is 0.
  fr_lSeed_zero   the point of lSeed is 0. lSeed is the seed of the link proof's own first OOD
                  sample, the one that smAt answers for both members (both:
                  Johnson/Prover/Link/LinkAll.lean). Of the seed's factor nothing is said here.
  fr_zero0, fr_zero1   checked by evaluation in Lean's kernel: on the row 0, every element that
                  the format's program computes for round 0 is 0, and so is every one of the
                  first aR + aP of round 1.

How it fits. Johnson/LinkSim/AtHome/TwoIndices.lean uses both points 0: there the fold takes row 0
and the sample takes entry 0, where the cell (0, 0) is written.

Other names (namespace OnBytes.LinkSim.AtText).
  elems_at        the elements of round j of a list of challenges made round by round.
  drawsZero       the challenges computed from zeroRho dsFull.

Limits.
- One verifier message, at the full size. Rounds 0 and 1 alone.
- How many elements these rounds sample is not said here: fr_zero0 and fr_zero1 would hold of a
  round that samples none.

Notes.
- Its facts checked by evaluation stand under "set_option maxRecDepth 100000 in" (see Spec.lean,
  "maxRecDepth").
- The two points are 0 either way, since a coordinate beyond the list's end is read as 0 too
  (readP_zeros).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ZeroDraws
import Johnson.LinkSim.AtText.SeamAtFull3

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice
open OnBytes.Flat (dsFull)
open Johnson.Prover.Link
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD drawnSL)

theorem elems_at (g : RD → Fmt.Drawn) (ds : List RD) (j : ℕ) :
    (drawsOf (ds.map g) j).elems = ((ds[j]?.map fun d => (g d).elems).getD []) := by
  unfold drawsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ds[j]? <;> rfl

set_option maxRecDepth 100000 in
theorem fr_zero0 : ((dsFull[0]?.map fun d =>
    (Fmt.drawRound .two d.entry d.kind fun _ => 0).elems).getD []).all
      (fun x => x == (0, 0, 0)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_zero1 : (((dsFull[1]?.map fun d =>
    (Fmt.drawRound .two d.entry d.kind fun _ => 0).elems).getD []).take
      (frS.P.aR + frS.P.aP)).all (fun x => x == (0, 0, 0)) = true := by decide +kernel

/-- The challenges computed from the verifier message whose hash blocks are all 0. -/
def drawsZero : ℕ → Fmt.Drawn := drawsOf (drawnSL (ckP .two) dsFull (zeroRho dsFull))

/-- At the full size and zeroRho, the point at which the tables' rows are folded is 0. -/
theorem fr_lGam_zero : lGam frS drawsZero = fun _ => 0 := by
  unfold lGam drawsZero
  rw [drawnSL_zero, elems_at]
  exact readP_zeros _ _ fun x hx => eq_of_beq (List.all_eq_true.1 fr_zero0 x hx)

/-- At the full size and zeroRho, the point of the first OOD sample's seed is 0. -/
theorem fr_lSeed_zero : (lSeed frS drawsZero).1 = fun _ => 0 := by
  show readP (frS.P.aR + frS.P.aP)
    (((drawsZero 1).elems.map E.ofTriple).take (frS.P.aR + frS.P.aP)) = _
  unfold drawsZero
  rw [drawnSL_zero, elems_at, ← List.map_take]
  exact readP_zeros _ _ fun x hx => eq_of_beq (List.all_eq_true.1 fr_zero1 x hx)

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.elems_at
#print axioms OnBytes.LinkSim.AtText.fr_zero0
#print axioms OnBytes.LinkSim.AtText.fr_zero1
#print axioms OnBytes.LinkSim.AtText.fr_lGam_zero
#print axioms OnBytes.LinkSim.AtText.fr_lSeed_zero
