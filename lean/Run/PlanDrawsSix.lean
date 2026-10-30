-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanDrawsSix.lean: an instance of the whole-protocol statements on the bias of drawing: at the
format page's own toy plan of six rounds, in both fields. In this plan each of the five draws of
`Fmt.Draw` occurs (of the seven kinds of `Fmt.Kind`, `join` does not).

The instance shows that the theorems are not empty; it is no parameter of a protocol. The
statements are those of Run/PlanDrawsQ.lean, on how the verifier messages of all rounds of a
protocol are made from 256-bit blocks and how much more often than its even share a value can come
(the bias). Definitions, a statement (`Run.Spec.planQ_six`) and its proof; three tests (#guard:
evaluations made while the file compiles; they leave no theorem).
The instance of Run/PlanDrawsQ.lean (a toy of this library's own: `Spec.planQ_toy`, at
Fmt/Toy1.lean) draws three positions and nothing else: exactly uniform. It exercises none of the
bias. This file takes the six entries of the page's toy plan (Fmt/Rules6Round.lean: `toyE1` to
`toyE6`) with their kinds: an element of the extension field; nothing; five positions below 2^10
and an element after them; a seed (a point of two coordinates and a factor that is not 0); forty
matrix entries; a sealing.

Main names:
  `six`: the six rounds, as data for `PQ.shapeOf` (no tree, no items: the prover's side is empty).
  `Spec.planQ_six`: it states three things for each field. First, the blocks, round by round, are 0
    (the trivial round in front), 5, 0, 6, 18, 1, 1. Second, `Shape.Draws.Good (kapSl 128)` holds,
    where `kapSl 128` (Iop/DrawOf.lean) is 1 + 2^-128. Third, the samplers' law holds with
    (1 + 2^-128)^18 and (1 + 2^-128)^31. The law is `Samplers.Good`, Iop/Pull.lean: its first
    number bounds each round's bias, its second their product over all rounds.
  The tests (#guard): the view (`ck`'s map to the format's record) of the sampler's value on blocks
    of test bytes is `Fmt.drawRound` on these bytes, at the rounds with a seed, with positions and
    an element, with matrix entries. (For all blocks that is a theorem: Run/PlanDraws.lean:
    `planDraws_tie`.)

Notation:
  `ck f`: the choice of challenge types with challenges as sampled values (Run/PlanDrawsQ.lean);
  `PQ.shapeOf`: the shape, with a trivial round in front (Run/PlanQTypes.lean);
  `planOf`: the draws of every round (Run/PlanDrawsQ.lean);
  `drawsQ`: the block samplers (Run/PlanDrawsQ.lean);
  18, 31 in `kapSl 128 ^ 18`, `kapSl 128 ^ 31`: the `a` and the `c` of `Spec.planQ_samplers`
    (Run/PlanDrawsQ.lean).

Limits (the degeneracies): the prover sends nothing: only the verifier's messages are those of the
toy plan. No work. The statement reads no proof of work, though the third entry has `work := 8`.
The numbers are a toy's: no security.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanDrawsQ
import Run.DrawGuard

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- a round with a given entry and kind, and an empty prover's side -/
def rdE (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) : PQ.RD := ⟨e, k, [], none, []⟩

/-- The six rounds of the page's toy plan. -/
def six : List PQ.RD :=
  [rdE _root_.Fmt.toyE1 .elems, rdE _root_.Fmt.toyE2 .nothing, rdE _root_.Fmt.toyE3 .positions,
    rdE _root_.Fmt.toyE4 .seeds, rdE _root_.Fmt.toyE5 .entries, rdE _root_.Fmt.toyE6 .sealed]

/-- The instance: the statements on the bias at the six rounds, for each field. -/
def Spec.planQ_six : Prop :=
  ∀ f : _root_.Fmt.Fld,
    blocksOf f _ (planOf f six) = [0, 5, 0, 6, 18, 1, 1] ∧
    Shape.Draws.Good (kapSl 128) (PQ.shapeOf (ck f) six) (drawsQ f six) ∧
    (Samplers.ofDraws (PQ.shapeOf (ck f) six) (drawsQ f six)).Good (kapSl 128 ^ 18) (kapSl 128 ^ 31)

theorem six_blocks :
    six.map (fun d => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)) =
      [5, 0, 6, 18, 1, 1] := by decide

theorem six_log : ∀ d ∈ six, d.entry.logN ≤ 64 := by decide

theorem planQ_six : Spec.planQ_six := by
  intro f
  refine ⟨by rw [planQ_blocks, six_blocks],
    planQ_good f six six_log,
    planQ_samplers f six six_log 18 31 (by decide) ?_⟩
  rw [six_blocks]
  decide

-- the view (`ck`'s map) of the sampler's value = the format's function on the bytes
#guard (ck .two).dr _root_.Fmt.toyE4 .seeds ((bsRound .two _root_.Fmt.toyE4 .seeds).φ (blk tb 18)) = _root_.Fmt.drawRound .two _root_.Fmt.toyE4 .seeds (_root_.Fmt.rowOfBlocks (tb ++ Array.replicate 13 (_root_.Fmt.zeroBytes 32)))
#guard (ck .one).dr _root_.Fmt.toyE3 .positions ((bsRound .one _root_.Fmt.toyE3 .positions).φ (blk tb 6)) = _root_.Fmt.drawRound .one _root_.Fmt.toyE3 .positions (_root_.Fmt.rowOfBlocks (tb ++ Array.replicate 1 (_root_.Fmt.zeroBytes 32)))
#guard (ck .two).dr _root_.Fmt.toyE5 .entries ((bsRound .two _root_.Fmt.toyE5 .entries).φ (blk #[tb[2]!] 1)) = _root_.Fmt.drawRound .two _root_.Fmt.toyE5 .entries (_root_.Fmt.rowOfBlocks #[tb[2]!])

end Run
