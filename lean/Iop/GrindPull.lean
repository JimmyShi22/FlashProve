-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindPull.lean: explicit error lists, from challenge samplers up to proof-of-work bits.

A record of protocols (`BatchProtocol`, Iop/Batch.lean) holds an encoder, a decoder and the protocols Test,
Link and Batch. `BatchProtocol.Sound` bounds the errors of all rounds by one number εs, and from that number
no factor 2^-b can be recovered: with short lists of positions εs is the error of the worst round
without proof of work. The step that adds b proof-of-work bits to a round (Iop/BatchGrind.lean)
needs the errors round by round (`BatchProtocol.SoundAt`, Iop/SoundAt.lean), and it is applied after
challenges are derived from hash blocks, by a pull-back along the challenge samplers (`BatchProtocol.pull`,
Iop/BatchPull.lean; `BatchProtocol.draws`, Iop/BatchWireDraw.lean). This file carries the explicit lists
through that pull-back (`BatchProtocol.SoundAt.draws`, `Err.BelowG.pull`; each count is multiplied by the
bound on the sampler's fibres). It uses the lemmas of Iop/PullProofs.lean and
Iop/BatchPullProofs.lean.

Main theorem (`grindDrawsSound`): for any type W of nonces with a fixed element, let L be sound with
explicit error lists, let the challenge samplers have bias at most κ₀ ≥ 1 for each hash block, and
let e_i ≤ c · 2^b_i · |C_i| in every round. Then `BatchProtocol.drawsGrind`, the record of protocols on hash
blocks with proof-of-work bits, satisfies `BatchProtocol.Sound` with the bound κ₀^K · c, where K is the
largest number of hash blocks of a round. The largest error of the protocol without proof of work
does not occur in this bound; a round with b_i = 0 must, as a probability, be below c (at most c) by
itself.
`grindDrawsProps` gives the other clauses of `BatchProtocol.Props`, without completeness, from `L.Props`, the
same conditions on the samplers and a bound n on the hash blocks of all rounds of a protocol
(`dr.TotLe n`), with the numbers of `BatchProtocol.draws`; soundness at c is a hypothesis there.

Notation: `Err s : Type` (Iop/Rbr.lean): one number for each round; these errors are counts of
challenge values, not probabilities (there, the head); in `Doomed s ε bad` (there), how many values
of the challenge may lead from a doomed transcript to one that is not doomed; e_i, b_i, C_i: of
round i, the entry in its list of errors (`εT`, `εL`, `εB`), the entry in its list of numbers of
proof-of-work bits (`gT`, `gL`, `gB`; `GBits`, Iop/GBits.lean), the type of challenges `r.Chal`
(`Round`, Iop/Shape.lean); `Err.BelowG g ε c : Prop` (Iop/Grind.lean): for a round r with the error
e and b such bits: `(e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞))`;
`σ.Good κ K : Prop`, for `κ K : ℝ≥0∞` (`Samplers.Good`, Iop/Pull.lean): every fibre has at most w
elements; for each round w * card Chal ≤ κ * card Src; and the product of these ratios over all
rounds is at most K (`w`, `Src`: fields of `Sampler`, there); the K of the main theorem is another:
`dr.K : ℕ` (Iop/BatchWireDraw.lean).
Limits: nothing is said on the size of any error: c is free, and at c ≥ 1 the statements on
soundness say nothing. What the heads of Iop/Grind.lean and Iop/BatchGrind.lean list as not said is
not said here either.
-/
import Iop.BatchGrindProofs
import Iop.BatchWireDrawOK

namespace Iop
open Prob
open scoped ENNReal

/-- The same numbers of proof-of-work bits after the pull-back along the samplers σ. -/
def GBits.pull : {s : Shape} → (σ : Samplers s) → GBits s → GBits (s.pull σ)
  | [], _, _ => ()
  | _ :: _, (_, σs), (b, g) => (b, GBits.pull σs g)

variable {I X : Type} {L : BatchProtocol I X} {Rno : I → X → Prop} {εT : Err L.offline.shape}
  {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape}

/-- Soundness for three explicit lists of errors is preserved by the pull-back, with the lists
`Err.pull`, if the bounds w of the samplers hold (`Fib`). -/
theorem BatchProtocol.SoundAt.pull (h : L.SoundAt Rno εT εL εB) {σT : Samplers L.offline.shape}
    {σL : Samplers L.link.shape} {σB : Samplers L.onlineBatch.loc.shape} (hT : σT.Fib)
    (hL : σL.Fib) (hB : σB.Fib) :
    (L.pull σT σL σB).SoundAt Rno (Err.pull σT εT) (Err.pull σL εL) (Err.pull σB εB) :=
  ⟨h.sndT.pull hT, h.sndL.pull hL, BatchPull.sndBL_pull hB h.sndB⟩

/-- If the samplers satisfy `Good κ K`, each bound grows by the factor κ at most; the numbers of
proof-of-work bits do not change. -/
theorem Err.BelowG.pull :
    ∀ {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}, σ.Good κ K →
      ∀ {g : GBits s} {ε : Err s} {c : ℝ≥0∞},
        Err.BelowG g ε c → Err.BelowG (g.pull σ) (Err.pull σ ε) (κ * c)
  | [], _, _, _, _, _, _, _, _ => trivial
  | r :: _, (σ, _), κ, _, h, (b, _), (e, _), c, hb => by
      obtain ⟨_, h', _⟩ := h.2.2
      refine ⟨?_, Err.BelowG.pull h' hb.2⟩
      show ((e * σ.w : ℕ) : ℝ≥0∞) ≤ κ * c * ((2 : ℝ≥0∞) ^ b * (Fintype.card σ.Src : ℝ≥0∞))
      push_cast
      calc
        (e : ℝ≥0∞) * σ.w ≤ c * ((2 : ℝ≥0∞) ^ b * Fintype.card r.Chal) * σ.w :=
          mul_le_mul' hb.1 le_rfl
        _ = c * (2 : ℝ≥0∞) ^ b * (σ.w * Fintype.card r.Chal) := by ring
        _ ≤ c * (2 : ℝ≥0∞) ^ b * (κ * Fintype.card σ.Src) := mul_le_mul' le_rfl h.2.1
        _ = κ * c * ((2 : ℝ≥0∞) ^ b * Fintype.card σ.Src) := by ring

variable {lam : ℕ}


/-- Challenge samplers that satisfy `Good` have the bounds on fibres that soundness after the
pull-back needs. -/
theorem Shape.Draws.Good.fibS {κ₀ : ℝ≥0∞} :
    ∀ {s : Shape} {ds : s.Draws lam}, ds.Good κ₀ s → (Samplers.ofDraws s ds).Fib
  | [], _, _ => trivial
  | _ :: _, (_, _), h => ⟨h.1.fib, Shape.Draws.Good.fibS h.2⟩

variable {dr : L.Draws lam}

/-- Soundness for three explicit lists of errors is preserved, with the lists `Err.pull`, when
challenges are derived from hash blocks by samplers that satisfy `Good`. -/
theorem BatchProtocol.SoundAt.draws {κ₀ : ℝ≥0∞} (h : L.SoundAt Rno εT εL εB) (hg : dr.Good κ₀) :
    (L.draws dr).SoundAt Rno (Err.pull (Samplers.ofDraws _ dr.T) εT)
      (Err.pull (Samplers.ofDraws _ dr.Lk) εL) (Err.pull (Samplers.ofDraws _ dr.B) εB) :=
  h.pull hg.1.fibS hg.2.1.fibS hg.2.2.fibS

variable (W : Type) [Inhabited W]

/-- The record of protocols on hash blocks, with proof-of-work bits; the lists g are given on the
rounds of L. -/
def BatchProtocol.drawsGrind (L : BatchProtocol I X) (dr : L.Draws lam) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) : BatchProtocol I X :=
  (L.draws dr).grind W (gT.pull (Samplers.ofDraws _ dr.T))
    (gL.pull (Samplers.ofDraws _ dr.Lk)) (gB.pull (Samplers.ofDraws _ dr.B))

/-- Under the hypotheses below (see the header): soundness at κ₀^K * c, K the largest number of hash
blocks of a round. -/
theorem grindDrawsSound {κ₀ : ℝ≥0∞} (h1 : 1 ≤ κ₀) (h : L.SoundAt Rno εT εL εB) (hg : dr.Good κ₀)
    {gT : GBits L.offline.shape} {gL : GBits L.link.shape} {gB : GBits L.onlineBatch.loc.shape} {c : ℝ≥0∞}
    (eT : Err.BelowG gT εT c) (eL : Err.BelowG gL εL c) (eB : Err.BelowG gB εB c) :
    (L.drawsGrind W dr gT gL gB).Sound Rno (κ₀ ^ dr.K * c) :=
  grindSoundB W _ _ _ _ _ _ _ _ _ _ _ (h.draws hg)
    (eT.pull (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K _ (le_max_left _ _) le_rfl))
    (eL.pull (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K _
        (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl))
    (eB.pull (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K _
        (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl))

/-- All clauses of `BatchProtocol.Props` but completeness, (Acc) (`BatchProtocol.PropsNoAcc`, Iop/BatchGrind.lean), for
the record of protocols on hash blocks with proof-of-work bits (`L.drawsGrind W dr gT gL gB`): the
numbers of `BatchProtocol.draws` (`M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize`), and the bound c on the errors in place
of εs. Hypotheses: `L.Props` (`h`), samplers as in `Spec.drawsPropsB` (`h1`, `hg`, `hn`;
Iop/BatchWireDraw.lean states it, `drawsPropsB` in Iop/BatchWireDrawOK.lean proves it), and
soundness at c (`hS`). -/
theorem grindDrawsProps {Ryes : I → X → Prop} {M : LH.Nums} {n : ℕ} {κ₀ : ℝ≥0∞} (h1 : 1 ≤ κ₀)
    (hg : dr.Good κ₀) (hn : dr.TotLe n) (h : L.Props Ryes Rno M) {gT : GBits L.offline.shape}
    {gL : GBits L.link.shape} {gB : GBits L.onlineBatch.loc.shape} {c : ℝ≥0∞}
    (hS : (L.drawsGrind W dr gT gL gB).Sound Rno c) :
    (L.drawsGrind W dr gT gL gB).PropsNoAcc
      Ryes Rno { M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize with εs := c } :=
  grindPropsB W _ _ _ _ _ _ _ _ _ c (drawsPropsB I X L Ryes Rno M lam n dr κ₀ h1 hg hn h) hS

end Iop
