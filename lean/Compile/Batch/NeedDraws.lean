-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedDraws.lean: a wire record whose challenges are made by block samplers reads, in
  each round, only the blocks of that round's sampler (words of this library: lean/GLOSSARY.md).

  Iop/Draw.lean, Iop/BatchWireDraw.lean: a challenge is made from b blocks of hash output by a
  "block sampler" (`BS`, Iop/Draw.lean: there "challenge sampler"), coordinate by coordinate, as the
  implementation samples (limits: the head of Iop/Draw.lean); b is a datum of the sampler of the
  round (Shape.Draws.bAt).
    `nbD dr`            the number of blocks that round i of protocol t needs: the b of its sampler
    `nb_ofDraws`        (QueryLayout.ofDraws ..).NB (nbD dr): the hypothesis of
                        Compile/Batch/NeedBlocks.lean, Compile/Batch/NeedP.lean,
                        Compile/Batch/NeedL.lean holds, without a hypothesis
    `sumNb_bAt`         under the hypotheses of its statement, the sum over the rounds of the blocks
                        and one chaining value each (`sumNb`): Shape.Draws.totB + the number of
                        rounds
    `cChain_nbD`        the part of the chains in the bound on the verifier (`cVBN_eq`,
                        Compile/Batch/NeedCost.lean): the blocks of all samplers of Test, Link and
                        Batch, and a chaining value for each round
  A sampler that rejects and tries again has the blocks of all its attempts in b: they are all
  marked by the table, and queried in every run (Compile/Batch/NeedTable.lean, header).
  Notation:
    `lam`, `K`: natural numbers: K blocks of lam bits give a verifier message (`WireRB`,
      Iop/BatchWire.lean)
    chaining value: the typed Fiat-Shamir oracle has one range for all rounds: K blocks and a
      chaining value (the head of Compile/Batch/NeedTable.lean)
    `dr`: an `L.Draws lam`: the challenge samplers of the three protocols (Iop/BatchWireDraw.lean);
      `ds`: an `s.Draws lam`: one sampler for each round (Iop/Draw.lean)
    `nbf`, `i`: ℕ → ℕ and ℕ; in `sumNb nbf s i`: for each round the blocks of its verifier message
      and the chaining value; i is the number of the first round (Compile/NeedCost.lean)
  Limits: nothing on the distributions of the samplers. No numeral.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.NeedCost
import Iop.BatchWireDraw

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (sumNb)

variable {lam K : ℕ}

theorem readsFrom_ofDraws :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam)
        (nps : s.NumPosB A pts) (nbf : ℕ → ℕ) (i : ℕ),
      (∀ k, nbf (i + k) = Shape.Draws.bAt s ds k) →
      RoundsQueryLayout.ReadsFrom nbf _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) i
  | [], _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (pt, pts), (bs, ds), (n0, nJ, nps), nbf, i, h => by
      refine ⟨?_, readsFrom_ofDraws s A pts ds nps nbf (i + 1) fun k => ?_⟩
      · have e : nbf i = bs.b := h 0
        rw [e]
        exact readsBelow_firstBlocks bs.b
      · have e := h (k + 1)
        rw [show i + 1 + k = i + (k + 1) by omega]
        exact e

theorem readsFrom_ofLocalD :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts) (nbf : ℕ → ℕ) (i : ℕ),
      (∀ k, nbf (i + k) = Shape.Draws.bAt s ds k) →
      RoundsQueryLayout.ReadsFrom nbf _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) i
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (pt, pts), (bs, ds), (np, nps), nbf, i, h => by
      refine ⟨?_, readsFrom_ofLocalD s pts ds nps nbf (i + 1) fun k => ?_⟩
      · have e : nbf i = bs.b := h 0
        rw [e]
        exact readsBelow_firstBlocks bs.b
      · have e := h (k + 1)
        rw [show i + 1 + k = i + (k + 1) by omega]
        exact e

/-- blocks and a chaining value for each round; s' is any shape with as many rounds (not all
hypotheses are named here: see the statement below) -/
theorem sumNb_bAt :
    ∀ (s s' : Shape) (ds : s.Draws lam) (nbf : ℕ → ℕ) (i : ℕ), s'.length = s.length →
      (∀ k, nbf (i + k) = Shape.Draws.bAt s ds k) →
      sumNb nbf s' i = Shape.Draws.totB s ds + s.length
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl, _ => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl, _ => absurd hl (by simp)
  | r :: s, _ :: s', (d, ds), nbf, i, hl, h => by
      have h0 : nbf i = d.b := h 0
      have ih := sumNb_bAt s s' ds nbf (i + 1) (by simpa using hl) fun k => by
        rw [show i + 1 + k = i + (k + 1) by omega]; exact h (k + 1)
      show (nbf i + 1) + sumNb nbf s' (i + 1) = (d.b + Shape.Draws.totB s ds) + (s.length + 1)
      rw [h0, ih]
      omega

variable {I X : Type}

/-- the number of blocks that round i of protocol t needs: that of its sampler -/
def nbD {L : BatchProtocol I X} (dr : L.Draws lam) : Tag → ℕ → ℕ
  | .test => Shape.Draws.bAt _ dr.T
  | .link => Shape.Draws.bAt _ dr.Lk
  | .onl => Shape.Draws.bAt _ dr.B

/-- The wire records of the block samplers read, in each round, the first blocks, as many as the
round's sampler has. -/
theorem nb_ofDraws (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
    (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol)
    (no : OpenNums) (dr : L.Draws lam) (ax : L.Aux pT pL pB) :
    (QueryLayout.ofDraws lam L pT pL pB z no dr ax).NB (nbD dr) :=
  ⟨readsFrom_ofLocalD _ _ _ _ _ 0 fun k => by rw [Nat.zero_add]; rfl,
    readsFrom_ofLocalD _ _ _ _ _ 0 fun k => by rw [Nat.zero_add]; rfl,
    readsFrom_ofDraws _ _ _ _ _ _ 0 fun k => by rw [Nat.zero_add]; rfl⟩

theorem length_pull' : ∀ (s : Shape) (σ : Samplers s), (Shape.pull s σ).length = s.length
  | [], _ => rfl
  | _ :: s, (_, σs) => congrArg (· + 1) (length_pull' s σs)

/-- The part of the chains in the bound on the verifier. -/
theorem cChain_nbD (L : BatchProtocol I X) (dr : L.Draws lam) :
    cChain (L.draws dr) (nbD dr) =
      (Shape.Draws.totB _ dr.T + L.offline.shape.length) +
        (Shape.Draws.totB _ dr.Lk + L.link.shape.length) +
        (Shape.Draws.totB _ dr.B + L.onlineBatch.loc.shape.length) := by
  show sumNb (Shape.Draws.bAt _ dr.T) (Shape.pull L.offline.shape _) 0 +
      sumNb (Shape.Draws.bAt _ dr.Lk) (Shape.pull L.link.shape _) 0 +
      sumNb (Shape.Draws.bAt _ dr.B) (Shape.pull L.onlineBatch.loc.shape _) 0 = _
  rw [sumNb_bAt _ _ dr.T _ 0 (length_pull' _ _) fun k => by rw [Nat.zero_add],
    sumNb_bAt _ _ dr.Lk _ 0 (length_pull' _ _) fun k => by rw [Nat.zero_add],
    sumNb_bAt _ _ dr.B _ 0 (length_pull' _ _) fun k => by rw [Nat.zero_add]]

end Need
end Compile.Batch
