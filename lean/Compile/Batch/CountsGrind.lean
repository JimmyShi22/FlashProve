-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountsGrind.lean: the counts (Compile/Batch/Counts.lean, Compile/Batch/CountsGr.lean)
and α (`alphaBG`, Compile/Batch/SpecGrind.lean), taken at `QueryLayout.grind` (Iop/GrindWire.lean), the
wire record of protocols with proof-of-work bits, and written as sums over the lists that give the
number of such bits for each round (words of this library: lean/GLOSSARY.md).

For a wire record Wr of L, data D of the search (at most D.mo b + 1 attempts in a round with b such
bits) and lists gT, gL, gB of the numbers b:

  `GBits.sumMo D s g`  The sum of D.mo b over the rounds with b > 0: the attempts after the first,
                       at most, of one transcript. (`gFail D g` of Compile/Batch/FitGrind.lean: the
                       sum of (1 - 2^-b)^(D.mo b + 1) over these rounds: a union bound for the event
                       that some search of one transcript fails; `cFail_grind`, `cFail_grindLocal`
                       there.)
  `sMoreJ_grindLocal`, `sMore0_grindLocal`  Test and Link: all searches are the one slot's.
  `sMore_grind_le`  Batch: a search is the slot's in a local round and shared in a shared round; N ·
                    (the slots' further attempts) + (the shared further attempts) ≤ N · sumMo for N
                    ≥ 1.
  `cTrees_grind`, `cTrees_grindLocal`, `xTree_grind`  The trees are those of Wr: a nonce is in the
                                                      plain part.
  `xMore_grind_le`, `alphaBG_grind`  The further attempts, at most (maxBatchSize ≥ 1), and α, exactly, at
                                     `Wr.grind D gT gL gB`.

Notation: `W`: a type with a default element (`[Inhabited W]`): the type of nonces (the head of
Iop/Grind.lean); α: `alphaBG` (Compile/Batch/SpecGrind.lean): `alphaB L M` plus `cFail` of Test,
`cFail` of Link and `L.maxBatchSize` times `cFail` of Batch.

Limits: nothing on the mean number of attempts; a shared search, which runs once, is counted maxBatchSize times
in `xMore_grind_le` and in α. No statement here is a security level.
-/
import Compile.Batch.CountsGr
import Compile.Batch.FitGrind

noncomputable section

namespace Iop
open scoped ENNReal

variable {W : Type}

/-- the attempts after the first, at most, of one transcript -/
def GBits.sumMo (D : GrData W) : (s : Shape) → GBits s → ℕ
  | [], _ => 0
  | _ :: s, (b, g) => (if b = 0 then 0 else D.mo b) + GBits.sumMo D s g


end Iop

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {W : Type} [Inhabited W] {lam K : ℕ}

theorem moreOf_grOf (D : GrData W) (C P : Type) :
    ∀ b, moreOf (grOf D C P b) = if b = 0 then 0 else D.mo b
  | 0 => rfl
  | _ + 1 => rfl

/-! ## Test and Link -/

theorem sMoreJ_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s),
      sMoreJ (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) =
        GBits.sumMo D s g
  | [], _, _ => rfl
  | r :: _, (_, ws), (b, g) => by
      show moreOf (grOf D r.Chal r.Plain b) + sMoreJ _ _ (RoundsQueryLayout.grindLocal ws D g) = _
      rw [moreOf_grOf, sMoreJ_grindLocal D ws g]
      rfl

theorem sMore0_grindLocal (D : GrData W) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s),
      sMore0 (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) = 0
  | [], _, _ => rfl
  | _ :: _, (_, ws), (_, g) => by
      show 0 + sMore0 _ _ (RoundsQueryLayout.grindLocal ws D g) = 0
      rw [sMore0_grindLocal D ws g]

theorem cTrees_grindLocal (D : GrData W) (Ns : ℕ) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s),
      cTrees (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) Ns =
        cTrees s (RoundSplits.allLocal s) ws Ns
  | [], _, _ => rfl
  | _ :: _, (w, ws), (_, g) =>
    congrArg (fun x => Ns * 2 ^ w.depthJ + 2 ^ w.depth0 + x) (cTrees_grindLocal D Ns ws g)

/-! ## Batch -/

theorem more_grind_round (D : GrData W) (C P0 Pj : Type) (N : ℕ) (hN : 1 ≤ N) :
    ∀ (k : Kind) (b : ℕ),
      N * moreOf (grJOf D C Pj k b) + moreOf (gr0Of D C P0 k b) ≤ N * (if b = 0 then 0 else D.mo b)
  | .lo, 0 => le_refl _
  | .sh, 0 => le_refl _
  | .lo, _ + 1 => le_refl _
  | .sh, b + 1 => by
      show N * 0 + D.mo (b + 1) ≤ N * D.mo (b + 1)
      rw [Nat.mul_zero, Nat.zero_add]
      exact Nat.le_mul_of_pos_left _ hN

/-- N times the slots' further attempts and the shared further attempts, at most (N ≥ 1) -/
theorem sMore_grind_le (D : GrData W) (N : ℕ) (hN : 1 ≤ N) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s), N *
          sMoreJ (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) +
        sMore0 (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) ≤
      N * GBits.sumMo D s g
  | [], _, _, _ => le_refl _
  | r :: _, (a, _), (_, ws), (b, g) => by
      show N * (moreOf (grJOf D r.Chal a.Pj a.kind b) + sMoreJ _ _ (RoundsQueryLayout.grind ws D g)) +
          (moreOf (gr0Of D r.Chal a.P0 a.kind b) + sMore0 _ _ (RoundsQueryLayout.grind ws D g)) ≤
        N * ((if b = 0 then 0 else D.mo b) + GBits.sumMo D _ g)
      have h1 := more_grind_round D r.Chal a.P0 a.Pj N hN a.kind b
      have h2 := sMore_grind_le D N hN ws g
      rw [Nat.mul_add, Nat.mul_add]
      omega

theorem cTrees_grind (D : GrData W) (Ns : ℕ) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s),
      cTrees (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) Ns = cTrees s A ws Ns
  | [], _, _, _ => rfl
  | _ :: _, (_, _), (w, ws), (_, g) =>
    congrArg (fun x => Ns * 2 ^ w.depthJ + 2 ^ w.depth0 + x) (cTrees_grind D Ns ws g)

/-! ## The wire record of the protocols with proof-of-work bits -/

variable {I X : Type} {L : BatchProtocol I X} (Wr : QueryLayout lam L) (D : GrData W) (gT : GBits L.offline.shape)
  (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (p : Params)

/-- the trees are those of the wire record Wr -/
theorem xTree_grind (n : ℕ) : xTree (Wr.grind D gT gL gB) p n = xTree Wr p n := by
  show (p.leaves + 1) * 2 ^ Wr.depth + cTrees _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT) 1 +
      p.leaves * cTrees _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL) 1 +
      n * cTrees _ _ (RoundsQueryLayout.grind Wr.B.sh D gB) L.maxBatchSize = _
  rw [cTrees_grindLocal, cTrees_grindLocal, cTrees_grind]
  rfl

/-- the further attempts of Test, of all Links and of n batches, at most (`L.maxBatchSize` ≥ 1) -/
theorem xMore_grind_le (hN : 1 ≤ L.maxBatchSize) (n : ℕ) :
    xMore (Wr.grind D gT gL gB) p n ≤
      GBits.sumMo D _ gT + p.leaves * GBits.sumMo D _ gL + n * (L.maxBatchSize * GBits.sumMo D _ gB) := by
  show (sMoreJ _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT) + sMore0 _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT)) +
      p.leaves *
        (sMoreJ _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL) +
          sMore0 _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL)) +
      n * (L.maxBatchSize * sMoreJ _ _ (RoundsQueryLayout.grind Wr.B.sh D gB) + sMore0 _ _ (RoundsQueryLayout.grind Wr.B.sh D gB)) ≤
    _
  rw [sMoreJ_grindLocal, sMore0_grindLocal, sMoreJ_grindLocal, sMore0_grindLocal]
  exact Nat.add_le_add (le_refl _) (Nat.mul_le_mul_left _ (sMore_grind_le D L.maxBatchSize hN Wr.B.sh gB))

/-- α at the wire record with proof-of-work bits -/
theorem alphaBG_grind (M : LH.Nums) :
    alphaBG (Wr.grind D gT gL gB) M =
      alphaB (L.grind W gT gL gB) M + (gFail D gT + gFail D gL + L.maxBatchSize * gFail D gB) := by
  show alphaB _ M +
      (cFail _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT) + cFail _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL) +
        L.maxBatchSize * cFail _ _ (RoundsQueryLayout.grind Wr.B.sh D gB)) = _
  rw [cFail_grindLocal, cFail_grindLocal, cFail_grind]

end Compile.Batch
