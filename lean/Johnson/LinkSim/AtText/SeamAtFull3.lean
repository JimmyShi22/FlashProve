-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamAtFull3.lean: at the full-size parameters, the public premises on sizes
(Sizes) hold at the challenges of every verifier message.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Each closed fact is checked by evaluation in Lean's kernel, and only public
numbers occur in the statements.
  fr_first      the sizes of the proximity test's first stage, as the prover's algorithm reads them
                off the plan, are the sizes of the link's group at 97 sampled positions (sg0 frP =
                frS.sg 97).
  fr_pad        the pad has a place of its own: no coefficient of a fold lies there.
  fr_cnts       in dsFull, rounds 16, 24, 31, 38 and 40 sample 97, 49, 49, 50 and 40 positions.
  fr_tails      the tails of the five stages' main rows and of their mask rows are 97, 49, 49, 50
                and 40 long: exactly as many as positions are sampled, so nothing is to spare.
  fr_fitsOk     the test fitsOk (SeamSizes.lean) accepts these counts.
  fr_fitsNo     a control that checks that the test can fail: with one position more at round 40
                alone, fitsOk rejects.
  fr_fitsNo16   the same control at round 16 alone.
  fr_sizes      hence Sizes frP frS 97 (SpecShift.lean) holds at the challenges of every verifier
                message of the link's protocol at the full-size parameters.

How it fits. fr_sizes is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean):
Johnson/LinkSim/AtHome/HomeTies.lean uses it to meet the premises on sizes at homeR b Z, and
home_upTo (Johnson/LinkSim/AtHome/RoadCloses.lean) passes them on. ShortTailAtFull.lean uses it too.

Limits.
- Everything is at the full-size parameters alone.

Notes. Each closed fact raises a limit of elaboration (Johnson/LinkSim/Spec.lean, "maxRecDepth").
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamSizes
import Johnson.Prover.Link.LinkAtFull

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Slice
open OnBytes.LinkSim.AtText
open OnBytes.Flat (dsFull)
open _root_.Desc.K15 (frP p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (SOf drawnSL)

set_option maxRecDepth 100000 in
/-- The sizes of the proximity test's first stage are the link's group sizes at 97 sampled
positions. -/
theorem fr_first : sg0 frP = frS.sg 97 := by
  have h : (sg0 frP).C = (frS.sg 97).C ∧ (sg0 frP).Z = (frS.sg 97).Z ∧
      (sg0 frP).h = (frS.sg 97).h ∧ (sg0 frP).g = (frS.sg 97).g ∧
      (sg0 frP).t = (frS.sg 97).t := by decide +kernel
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases hs : sg0 frP with
  | mk C Z hh g t =>
    rw [hs] at h1 h2 h3 h4 h5
    simp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl

set_option maxRecDepth 100000 in
/-- The pad has a place of its own: no coefficient of a fold lies there. -/
theorem fr_pad : frS.P.T.l ≤ frS.P.R * frS.P.C.l - 1 ∧
    frS.P.t0 + frS.P.T.r ≤ frS.P.R * frS.P.C.l - 1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- In dsFull, rounds 16, 24, 31, 38 and 40 sample 97, 49, 49, 50 and 40 positions. -/
theorem fr_cnts : [16, 24, 31, 38, 40].map (cntD dsFull) = [97, 49, 49, 50, 40] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The row tails of the five stages, for the main code and the mask code, are 97, 49, 49, 50 and 40
long. -/
theorem fr_tails : (frFirst :: frRest).map (fun s => ((sgOf s).C.r, (sgOf s).Z.r)) =
    [(97, 97), (49, 49), (49, 49), (50, 50), (40, 40)] := by decide +kernel

set_option maxRecDepth 100000 in
/-- The test fitsOk accepts the full-size counts of sampled positions. -/
theorem fr_fitsOk : fitsOk (cntD dsFull) frRest frFirst 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A control that checks that the test can fail: with one position more at round 40, fitsOk
rejects. -/
theorem fr_fitsNo :
    fitsOk (fun n => cntD dsFull n + if n = 40 then 1 else 0) frRest frFirst 6 = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same control at round 16. -/
theorem fr_fitsNo16 :
    fitsOk (fun n => cntD dsFull n + if n = 16 then 1 else 0) frRest frFirst 6 = false := by
  decide +kernel

/-- **The public premises on sizes, at the challenges of every verifier message.** -/
theorem fr_sizes (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsFull))) :
    Sizes frP frS 97 (drawsOf (drawnSL (ckP .two) dsFull ρ.2)) :=
  ⟨fr_first, fr_pad, frFirst, frRest, fr_cons,
    fitsOfOk _ (cntD dsFull) (possLen dsFull ρ.2) frRest frFirst 6 fr_fitsOk⟩

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.fr_first
#print axioms OnBytes.LinkSim.Seam.fr_pad
#print axioms OnBytes.LinkSim.Seam.fr_cnts
#print axioms OnBytes.LinkSim.Seam.fr_tails
#print axioms OnBytes.LinkSim.Seam.fr_fitsOk
#print axioms OnBytes.LinkSim.Seam.fr_fitsNo
#print axioms OnBytes.LinkSim.Seam.fr_fitsNo16
#print axioms OnBytes.LinkSim.Seam.fr_sizes
