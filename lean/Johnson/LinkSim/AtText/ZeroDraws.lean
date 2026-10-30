-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ZeroDraws.lean: the verifier message whose hash blocks are all 0, and the
challenges that are computed from it.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. A round's part of a verifier message, as the protocol is stated in Lean, is a
string of hash blocks (ckP, Run/PlanPull.lean) with the bits of the round's proof-of-work check
beside it. The challenges of a round are computed from it by the format's own program
(Fmt.drawRound, Fmt/Rules6Round.lean), on the row of the blocks' words (planPull_view). That the
blocks of a round's part with proof-of-work bits 0 are the blocks themselves is the library's
(GChal.old_zero, Iop/GrindProofs.lean). This file concerns verifier messages alone; no prover
occurs.
  zeroRho ds       the verifier message of the rounds ds with all blocks and all proof-of-work
                   bits 0.
  drawnSL_zero     for every list of rounds ds, the challenges computed from zeroRho ds are, round
                   by round, the format's program applied to the row 0.
  readP_zeros      a point read off elements that are all 0 is the point 0.
  eqk_zero         at the point 0, the corner "all false" has the weight 1.

How it fits. ZeroDrawsAtFull.lean applies these at the full size.
Johnson/LinkSim/AtHome/TwoIndices.lean, Johnson/LinkSim/AtHome/TwoPlains.lean and
Johnson/LinkSim/AtHome/TwoViews.lean take zeroRho dsFull as their one verifier message, at every
fixed coin, and compare an index with the index that has 1 added at the cell (0, 0). answer_home
proves that the prover's first answer changes by 1, two_plains that what the prover sends in the
clear differs, and two_views that the disclosed views differ. These hold coin by coin, at that one
verifier message, and say nothing on distributions over the coins
(Johnson/LinkSim/AtHome/TwoPlains.lean's limits).

Other names (namespace OnBytes.LinkSim.AtText).
  word_zeroDig, word_empty   checked by evaluation in Lean's kernel: a word of a block of zeros,
                   and of no block, is 0.
  rowOfDigs_zero   so the row of words is 0 everywhere.
  readE_zeros      the element read off (0, 0, 0), and off the default, is 0.

Limits.
- One verifier message. Nothing on how likely it is.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamFactors

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP rowOfDigs digToBytes planPull_view)
open TypedOracleCompiler.Run.PQ (RD uL drawnSL)

/-- All hash blocks and all proof-of-work bits 0. -/
def zeroRho : (ds : List RD) → Rho (uL (ckP .two) ds)
  | [] => ()
  | d :: ds => (GChal.zero d.entry.work fun _ _ => false, zeroRho ds)

theorem word_zeroDig : ∀ i : Fin 4, Fmt.digestWord (digToBytes fun _ => false) i.val = 0 := by
  decide +kernel

theorem word_empty : ∀ i : Fin 4, Fmt.digestWord ByteArray.empty i.val = 0 := by
  decide +kernel

theorem rowOfDigs_zero (K : ℕ) :
    rowOfDigs (fun (_ : Fin K) (_ : Fin 256) => false) = fun _ => 0 := by
  funext t
  have h4 : t % 4 < 4 := Nat.mod_lt _ (by decide)
  show Fmt.digestWord ((Array.ofFn fun _ : Fin K => digToBytes fun _ => false).getD (t / 4)
    ByteArray.empty) (t % 4) = 0
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split
  · exact word_zeroDig ⟨t % 4, h4⟩
  · exact word_empty ⟨t % 4, h4⟩

/-- The challenges computed from zeroRho ds: round by round, the format's program on the row 0. -/
theorem drawnSL_zero : ∀ ds : List RD, drawnSL (ckP .two) ds (zeroRho ds) =
    ds.map fun d => Fmt.drawRound .two d.entry d.kind fun _ => 0
  | [] => rfl
  | d :: ds => by
    show (ckP .two).dr d.entry d.kind (GChal.old (GChal.zero d.entry.work fun _ _ => false)) ::
      drawnSL (ckP .two) ds (zeroRho ds) = _
    rw [GChal.old_zero, (planPull_view .two d.entry d.kind _).2, rowOfDigs_zero, drawnSL_zero ds]
    rfl

theorem readE_zeros : readE (E.ofTriple (0, 0, 0)) = 0 ∧ readE zeroE = 0 := by
  refine ⟨?_, ?_⟩
  · rw [readE_ofTriple, ← toE_ofE 0]
    rfl
  · rw [readE_def, ← toE_ofE 0]
    rfl

/-- A point that is read off elements that are all 0 is the point 0. -/
theorem readP_zeros (n : ℕ) (l : List Fmt.Ext) (h : ∀ x ∈ l, x = (0, 0, 0)) :
    readP n (l.map E.ofTriple) = fun _ => 0 := by
  funext i
  show readE ((l.map E.ofTriple).getD i.val zeroE) = 0
  rcases Nat.lt_or_ge i.val (l.map E.ofTriple).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi, List.getElem_map,
      h _ (List.getElem_mem (by rw [List.length_map] at hi; exact hi))]
    exact readE_zeros.1
  · rw [List.getD_eq_default _ _ hi]
    exact readE_zeros.2

/-- At the point 0 the corner "all false" has the weight 1. -/
theorem eqk_zero (n : ℕ) : Alg.eqk (fun _ : Fin n => (0 : GE)) (fun _ => false) = 1 := by
  unfold Alg.eqk
  refine Finset.prod_eq_one fun v _ => ?_
  show (if false = true then (0 : GE) else 1 - 0) = 1
  rw [if_neg Bool.false_ne_true]
  exact sub_zero _

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.word_zeroDig
#print axioms OnBytes.LinkSim.AtText.word_empty
#print axioms OnBytes.LinkSim.AtText.rowOfDigs_zero
#print axioms OnBytes.LinkSim.AtText.drawnSL_zero
#print axioms OnBytes.LinkSim.AtText.readE_zeros
#print axioms OnBytes.LinkSim.AtText.readP_zeros
#print axioms OnBytes.LinkSim.AtText.eqk_zero
