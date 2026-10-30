-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ShortTailAtFull.lean: at the full size, what is left of the premises of the
negative test short_tail_fails at the challenges of a verifier message.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. At the full-size parameters (frP, frS, dsFull) and for every verifier message
ρ of the link proof there, it states short_tail_fails (Johnson/LinkSim/AtText/ShortTail.lean) with
the public premises on sizes proved (fr_sizes), and with PtsFull reduced to one condition on the
challenges.
  fr_short_tail_fails at the full size and for every verifier message ρ, data X and coins C, C' with
                  ShortPsi: suppose (1), a condition on the verifier's challenges alone: the 97
                  positions at which the first tree is opened are distinct modulo the mask code's
                  length. Suppose (2), a condition on the data, the honest coins and the challenges:
                  the last entry of the explicit shift of the tail of the row beside the two folded
                  rows (shPsi) is not 0. Then the two algorithms do not disclose the same.
  fr_ptsFull      PtsFull holds at the full size wherever (1) holds (by ptsFull_of_nodup,
                  ShortTailPts.lean).
  fr_q0_len       at the challenges of every verifier message the first tree is opened at 97
                  positions, counted with repeats (by possLen,
                  Johnson/LinkSim/AtText/SeamSizes.lean, and fr_cnts, SeamAtFull3.lean).
  fr_maskLog, fr_round16, fr_maskTail   checked by evaluation in Lean's kernel: the mask code of
                  the link's group is at most 2 ^ 32 long; the round whose positions open the
                  first tree is round 16; that code's tail has 97 entries.
Argued on paper, not proved: condition (1) holds for some verifier messages and fails for others,
so it can be no theorem for all of them.

How it fits. ShortTail.lean's head says what the test tests and how far it reaches.

Limits.
- short_tail_fails stays conditional. Beside the two premises that name the short coins (hC, hC'),
  two are left, and neither of these is proved to be met at any data or any verifier message.
- It is at the full size alone.
- How often (1) holds is not said here.

Notes.
- Its facts checked by evaluation stand under "set_option maxRecDepth 100000 in" (see Spec.lean,
  "maxRecDepth").
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ShortTailPts
import Johnson.LinkSim.AtText.SeamAtFull3

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice
open OnBytes.LinkSim.Seam
open OnBytes.Flat (dsFull)
open _root_.Desc.K15 (frP)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (SOf drawnSL)

set_option maxRecDepth 100000 in
theorem fr_maskLog : frS.P.Z.a ≤ 32 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_round16 : 6 + 2 + ((sg0 frP).h + (sg0 frP).g) = 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_maskTail : frS.P.Z.r = 97 := by decide +kernel

theorem fr_q0_len (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsFull))) :
    (q0 frP (drawsOf (drawnSL (ckP .two) dsFull ρ.2))).length = frS.P.Z.r := by
  unfold q0 openAt
  rw [List.length_map, fr_round16, possLen dsFull ρ.2 16, fr_maskTail]
  exact (List.cons.inj fr_cnts).1

/-- PtsFull at the full size, from the one condition on the verifier's challenges. -/
theorem fr_ptsFull (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsFull)))
    (hn : ((q0 frP (drawsOf (drawnSL (ckP .two) dsFull ρ.2))).map (· % 2 ^ frS.P.Z.a)).Nodup) :
    PtsFull frP frS (drawsOf (drawnSL (ckP .two) dsFull ρ.2)) :=
  ptsFull_of_nodup frP frS _ fr_maskLog (fr_q0_len ρ) hn

/-- short_tail_fails at the full size, with its premises on sizes proved and PtsFull reduced to
one condition on the challenges. -/
theorem fr_short_tail_fails (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsFull))) (X : LIn frS)
    (C C' : LCoins)
    (hn : ((q0 frP (drawsOf (drawnSL (ckP .two) dsFull ρ.2))).map (· % 2 ^ frS.P.Z.a)).Nodup)
    (hne : shPsi frP frS 97 X X C (drawsOf (drawnSL (ckP .two) dsFull ρ.2)) (frS.P.Z.r - 1) ≠ 0)
    (hC : ShortPsi frS C) (hC' : ShortPsi frS C') :
    shownOf (linkAll frP frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ.2))) ≠
      shownOf (simAll frP frS 97 X C' (drawsOf (drawnSL (ckP .two) dsFull ρ.2))) :=
  short_tail_fails (fr_sizes ρ) (fr_ptsFull ρ hn) hC hne hC'

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.fr_maskLog
#print axioms OnBytes.LinkSim.AtText.fr_round16
#print axioms OnBytes.LinkSim.AtText.fr_maskTail
#print axioms OnBytes.LinkSim.AtText.fr_q0_len
#print axioms OnBytes.LinkSim.AtText.fr_ptsFull
#print axioms OnBytes.LinkSim.AtText.fr_short_tail_fails
