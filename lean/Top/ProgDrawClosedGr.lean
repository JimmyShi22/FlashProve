-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/ProgDrawClosedGr.lean: formulas meant to bound the terms of the compiled scheme with
  proof-of-work bits. Three formulas (`alphaDG`, `epsG`, `zetaDGTot`) in the counts of the record of
  protocols without proof-of-work bits (`Top.CountsB`) and nine numbers of the proof of work, and
  two lemmas: `alphaDG` and `SG` bound their terms. No theorem on a scheme is in this file. (Terms:
  lean/GLOSSARY.md.)
    `GrSums`    nine numbers; under `GrSums.Of`, bounds for:
                mT, mL, mO   the attempts after the first, at most, of one transcript of Test, Link,
                             Batch (the sums of Dg.mo b over the rounds with b > 0 proof-of-work
                             bits);
                qT, qL, qO   the sums of (1 - 2^-b)^(Dg.mo b + 1) over these rounds;
                sT, sL, sO   the rounds with proof-of-work bits of one transcript (the searches).
  `CountNumsB.BfG`, `alphaDG`, `epsG`, `SG`, `zetaDGTot` are the explicit formulas:
      alphaDG g kt  = alphaD kt + (qT + qL + N · qO)
          Here N is the number of slots: a shared search, which runs once, is counted N times.
      epsG no lam e = (tC + tP + tv + 1) · e + 2 (tC + tP + tv + 2)² / 2^lam
          Here e is a supplied bound on every round error of the record with proof-of-work bits; no
          factor for the samplers' bias multiplies it, because it is a bound for the record after
          the samplers.
      BfG           = Bf + (mT + leaves · mL + n · N · mO): every attempt is counted, each search
                      at its cap
      zetaDGTot     = the overrun term
                      + t · max(A / 2^sMT, A / 2^lam, Bf / 2^min(sFS, lam), Rq / 2^lam)
                      + [A² / 2^sMT + A² / 2^lam + (Bf² + S · BfG) / 2^min(sFS, lam)
                         + 3 Rq² / 2^lam]
                      + the withheld part,
                      with S = sT + leaves · sL + n · N · sO (`SG`).
                      The part that is linear in t has no number of attempts in it; in the rest all
                      attempts occur once, times the number of searches.
      (`tv`, `A`, `Bf`, `Rq`: Top/BatchBoundsGen.lean; sMT, sFS: `Params`, Compile/Star.lean;
      leaves: `Params.leaves`, Compile/Spec.lean; n in these formulas: the number of batches.)
    `xGr_le`:
        under `CountsB`, `GrSums.Of`, 1 ≤ L.maxBatchSize and an inhabited type `Wn` of nonces: `xGr`
        of the wire record with proof-of-work bits (`WBdG`) is at most `SG`.


    `alphaG_le`:
        under `CountsB` and `GrSums.Of`: `alphaB` plus the failures of the searches (`gFail`) is at
        most `alphaDG` at kt = κ₀ ^ n.



  Sanity lemma at nine zeros: `alphaDG_zero`: the formula is `alphaD` (Top/BatchBoundsGenDr.lean).
  None is here for `epsG` or `zetaDGTot`. At lists of zeros the scheme is not the one without
  proof-of-work bits (one block more in the wire: Iop/GrindWire.lean): the sanity lemma is on the
  formula alone.
  Not used are the field `e` of `CountsB` (M.εs ≤ c.e) and M.εs itself, the error of L without
  proof-of-work bits: `alphaDG`, `epsG` and `zetaDGTot` do not read them; ε depends on e, a bound
  for the record with proof-of-work bits.

  Notation: κ₀, n: free in the lemmas here; under `BatchProtocol.Draws.Good` and `BatchProtocol.Draws.TotLe`
  (Iop/BatchWireDraw.lean): the bias of one block, a bound on the blocks of all rounds of one
  protocol; kt: an argument of the formulas, which the lemmas take at κ₀ ^ n; tC, tP, t: numbers of
  queries; `c : CountNumsB`: the counts of the three protocols (Top/BatchBoundsGen.lean); `alphaB`:
  the term of Compile/Batch/ with which a lemma compares a formula.

  The round errors in this header are numbers that the caller supplies (the argument `e`;
  the data field `LH.Nums.εs`, Iop/InteractiveOracleProof.lean, of `M`): that a record of protocols is sound at these
  numbers is no statement of this file, and no hypothesis of its lemmas; that tie is
  `Spec.grindSoundB` (Iop/BatchGrind.lean), under the hypotheses of its statement, for `L.grind` at
  such a number (that condition itself asks soundness of the parts one level down: the tie
  carries soundness, it does not found it).

  Limits: For what ε means, what is counted and what is not said, see the header of
  Compile/Batch/SpecGrind.lean. The factor "cap" in the part of ζ that is linear in t is the
  proof's, not the scheme's (there); `zetaDGTot` does not have it. The plain exit only; whole Merkle
  paths. No statement here is a security level.
-/
import Top.ProgDrawGr
import Top.ProgDrawClosed
import Compile.Batch.CountsGrTot
import Compile.Batch.FlagsFree

noncomputable section

namespace Top
open Iop Rom ZKCP Compile Compile.Batch Top.Batch
open scoped ENNReal

/-- Nine numbers of the searches. -/
structure GrSums where
  mT : ℕ
  mL : ℕ
  mO : ℕ
  sT : ℕ
  sL : ℕ
  sO : ℕ
  qT : ℝ≥0∞
  qL : ℝ≥0∞
  qO : ℝ≥0∞

/-- That they bound the sums over the three lists of numbers of proof-of-work bits. -/
structure GrSums.Of {Wn : Type} (Dg : GrData Wn) {sT sL sB : Shape} (gT : GBits sT) (gL : GBits sL)
    (gB : GBits sB) (g : GrSums) : Prop where
  mT : GBits.sumMo Dg sT gT ≤ g.mT
  mL : GBits.sumMo Dg sL gL ≤ g.mL
  mO : GBits.sumMo Dg sB gB ≤ g.mO
  sT : nTests sT gT ≤ g.sT
  sL : nTests sL gL ≤ g.sL
  sO : nTests sB gB ≤ g.sO
  qT : gFail Dg gT ≤ g.qT
  qL : gFail Dg gL ≤ g.qL
  qO : gFail Dg gB ≤ g.qO

namespace CountNumsB
variable (c : CountNumsB) (no : OpenNums) (p : Params) (lam : ℕ) (g : GrSums)

/-- Fiat-Shamir evaluations of honest C and P in set-up and n batches, all attempts counted. -/
def BfG (n : ℕ) : ℕ := c.Bf p n + (g.mT + p.leaves * g.mL + n * (c.N * g.mO))

def alphaDG (kt : ℝ≥0∞) : ℝ≥0∞ := c.alphaD kt + (g.qT + g.qL + (c.N : ℝ≥0∞) * g.qO)

def epsG (e : ℝ≥0∞) (tC tP : ℕ) : ℝ≥0∞ :=
  ((tC + tP + c.tv no + 1 : ℕ) : ℝ≥0∞) * e + 2 * ((tC + tP + c.tv no + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- The searches of set-up and n batches, at most. -/
def SG (n : ℕ) : ℕ := g.sT + p.leaves * g.sL + n * (c.N * g.sO)

/-- ζ for one bound t on all queries. -/
def zetaDGTot (kt : ℝ≥0∞) (t n : ℕ) : ℝ≥0∞ :=
  ((p.leaves : ℝ≥0∞) * binTail n p.leaves p.s1 +
    ((t : ℝ≥0∞) * muOf p lam (c.A p n) (c.Bf p n) (c.Rq n) +
      sqOf p lam (c.A p n) (c.Bf p n) (c.BfG p g n) (c.SG p g n) (c.Rq n)))
  + (kt * c.zT + (p.leaves : ℝ≥0∞) * (kt * c.zL) + (n : ℝ≥0∞) * ((c.N : ℝ≥0∞) * (kt ^ c.N * c.zO)))

theorem zetaDGTot_mono {kt kt' : ℝ≥0∞} (h : kt ≤ kt') (t n : ℕ) :
    c.zetaDGTot p lam g kt t n ≤ c.zetaDGTot p lam g kt' t n := by
  unfold zetaDGTot; gcongr

theorem alphaDG_mono {kt kt' : ℝ≥0∞} (h : kt ≤ kt') : c.alphaDG g kt ≤ c.alphaDG g kt' :=
  add_le_add (c.alphaD_mono h) le_rfl

/-- Sanity lemma: without proof-of-work bits (nine zeros) `alphaDG` is `alphaD` of
Top/BatchBoundsGenDr.lean. -/
theorem alphaDG_zero (kt : ℝ≥0∞) : c.alphaDG ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ kt = c.alphaD kt := by
  simp [alphaDG]

end CountNumsB

namespace ProgDraw
open Top.Prog
open Compile.BatchLife (Sims)

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L) {Wn : Type} [Inhabited Wn]
  (Dg : GrData Wn) (sW : Ser Wn) (gT : GBits (LBd lam L dr).offline.shape)
  (gL : GBits (LBd lam L dr).link.shape) (gB : GBits (LBd lam L dr).onlineBatch.loc.shape)

variable {M : LH.Nums} {κ₀ : ℝ≥0∞} {n : ℕ} {c : CountNumsB} {g : GrSums} {εs' e : ℝ≥0∞}

omit [Inhabited Wn] in
theorem alphaG_le (hc : CountsB L pT pL pB ax M c) (hg : GrSums.Of Dg gT gL gB g) :
    alphaB (LBd lam L dr) (numsDraw lam L dr M κ₀ n) +
        (gFail Dg gT + gFail Dg gL + L.maxBatchSize * gFail Dg gB) ≤
      c.alphaDG g (κ₀ ^ n) := by
  unfold CountNumsB.alphaDG
  rw [← hc.N]
  have h1 := hg.qT
  have h2 := hg.qL
  have h3 := hg.qO
  exact add_le_add (CountsBD.alphaB_le lam dr hc κ₀ n) (by gcongr)

/-- The searches of honest C and P: under the hypotheses below, `xGr` is at most `SG`. -/
theorem xGr_le (hc : CountsB L pT pL pB ax M c) (hg : GrSums.Of Dg gT gL gB g)
    (hN : 1 ≤ L.maxBatchSize) (k : ℕ) :
    xGr (WBdG lam L pT pL pB z no dr ax Dg gT gL gB) p k ≤ c.SG p g k := by
  rw [xGr_grind]
  have hNe : (LBd lam L dr).maxBatchSize = c.N := hc.N
  have hN' : 1 ≤ (LBd lam L dr).maxBatchSize := hN
  have t1 := le_trans (gSearchL_le Dg 0 1 _ gT) (le_trans (le_of_eq (Nat.one_mul _)) hg.sT)
  have t2 := le_trans (gSearchL_le Dg 0 1 _ gL) (le_trans (le_of_eq (Nat.one_mul _)) hg.sL)
  have t3 := le_trans
    (le_trans (gSearch_le Dg 0 _ hN' _ (LBd lam L dr).onlineBatch.ann gB) (Nat.mul_le_mul_left _ hg.sO))
    (le_of_eq (congrArg (· * g.sO) hNe))
  exact Nat.add_le_add (Nat.add_le_add t1 (Nat.mul_le_mul_left _ t2)) (Nat.mul_le_mul_left _ t3)

variable {Ryes Rno : I → X → Prop} {nb : ℕ} {kt : ℝ≥0∞}

end ProgDraw
end Top
