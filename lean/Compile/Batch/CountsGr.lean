-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountsGr.lean: rounds with proof-of-work bits: the count of all attempts is the count
of Fiat-Shamir queries plus the attempts after the first; a bound for `alphaBG` from bounds on its
parts (words of this library: lean/GLOSSARY.md).

Compile/Batch/Counts.lean counts every attempt at the worst case (`cFb`, `xFbG`);
Compile/Batch/SpecGrind.lean states α (`alphaBG`) with the sums `cFail` of the probabilities that a
search fails.

  `sMoreJ`, `sMore0`  The attempts after the first, at most, summed over a list of rounds: of a
                      slot's own searches; of the shared searches.
  `cFb_eq`  cFb Ns s A W = (Ns + 1) · (number of rounds) + (Ns · sMoreJ + sMore0).
  `xFbG_eq`  xFbG W p n = xFb p n + xMore W p n: the count without such bits plus the further
             attempts of Test, of all Links and of n batches.
  `alphaBG_le_of`  From a bound on `alphaB` and bounds on the three sums `cFail`.

Limits: nothing on the mean number of attempts; every search is counted at its maximal length. No
statement here is a security level.
-/
import Compile.Batch.SpecGrind

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the attempts after the first of a slot's own searches, at most, summed over the rounds -/
def sMoreJ {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => moreOf w.grJ + sMoreJ s A W

/-- the attempts after the first of the shared searches, at most, summed over the rounds -/
def sMore0 {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => moreOf w.gr0 + sMore0 s A W

theorem triesOf_one_add {C P : Type} (g : Option (GrW C P)) : triesOf g = 1 + moreOf g := by
  cases g with
  | none => rfl
  | some g => exact Nat.add_comm _ _

/-- all attempts = one for each Fiat-Shamir query counted by xFb, and the attempts after the first
-/
theorem cFb_eq {K : ℕ} (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      cFb Ns s A W = (Ns + 1) * s.length + (Ns * sMoreJ s A W + sMore0 s A W)
  | [], _, _ => rfl
  | _ :: s, (_, A), (w, W) => by
      show Ns * triesOf w.grJ + triesOf w.gr0 + cFb Ns s A W =
        (Ns + 1) * (s.length + 1) +
          (Ns * (moreOf w.grJ + sMoreJ s A W) + (moreOf w.gr0 + sMore0 s A W))
      rw [cFb_eq Ns s A W, triesOf_one_add, triesOf_one_add]
      ring

variable (W : QueryLayout lam L) (p : Params)

/-- the attempts after the first, at most, of Test, of all Links and of n batches -/
def xMore (n : ℕ) : ℕ :=
  (sMoreJ L.offline.shape _ W.T.sh + sMore0 L.offline.shape _ W.T.sh) +
    p.leaves * (sMoreJ L.link.shape _ W.Lk.sh + sMore0 L.link.shape _ W.Lk.sh) +
    n * (L.maxBatchSize * sMoreJ L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh + sMore0 L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)

/-- the count with proof-of-work bits is the count without them plus the further attempts -/
theorem xFbG_eq (n : ℕ) : xFbG W p n = xFb (L := L) p n + xMore W p n := by
  unfold xFbG xFb xMore
  rw [cFb_eq, cFb_eq, cFb_eq]
  ring

variable {W p}


theorem alphaBG_le_of {M : LH.Nums} {a qT qL qO : ℝ≥0∞} (h0 : alphaB L M ≤ a)
    (h1 : cFail L.offline.shape _ W.T.sh ≤ qT) (h2 : cFail L.link.shape _ W.Lk.sh ≤ qL)
    (h3 : cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh ≤ qO) :
    alphaBG W M ≤ a + (qT + qL + L.maxBatchSize * qO) := by
  unfold alphaBG
  gcongr

end Compile.Batch
