-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLabelStd.lean: a standard way to encode the labels (purpose, counter) of
Compile/Batch/SeedLabel.lean as queries to the auxiliary oracle, for every record of protocols and
every λ. (Words of this library: lean/GLOSSARY.md.)

The oracle `OracleName.other` of Compile/Batch/Oracles.lean maps a list of bits to λ bits.

  `codeP`   a purpose as a pair of numbers, with the numbers that the implementation uses for its
            four keys: anchor (1, 0); leaf k (2, k); test (3, 0); link k (4, k)
  `tauStdB`   seeds are the numbers below 2^λ; the query for (seed, purpose, counter) is the λ bits
              of the seed followed by the binary digits of the number Nat.pair (Nat.pair a k)
              counter, where (a, k) is the code of the purpose; an answer is read as in
              Compile/Batch/SeedStd.lean (a number, reduced modulo the number of outcomes)
  `sigmaLabB`   the `Rom.SeedOracle` of that encoding for the committer of Compile/Batch/Star.lean
                with the standard decomposition into small samples (`blocksStd`,
                Compile/SeedStd.lean). `sigmaLabB_o`, `bias_sigmaLabB_w`: the two hypotheses of
                `Spec.seedMainB` (Compile/Batch/SeedStar.lean; proved in
                Compile/Batch/SeedMain.lean) on it; `sigmaLabB_sd`: there are 2^λ seeds

Limits: the implementation writes a label as four 32-bit words under a stream cipher's key; this
encoding is another injective one.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedLabel
import Compile.Batch.SeedStd

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

open Compile.Seed (ptStd pt_inj blocksStd)

/-- a purpose as a pair of numbers -/
def codeP : Purpose → ℕ × ℕ
  | .anchor => (1, 0)
  | .leaf k => (2, k)
  | .test => (3, 0)
  | .link k => (4, k)

theorem codeP_inj : Function.Injective codeP := by
  intro q q' h
  cases q <;> cases q' <;> simp_all [codeP]

variable {I X : Type} (lam K : ℕ) (L : BatchProtocol I X)

/-- The auxiliary oracle as a source of coins under labels. -/
def tauStdB : LabelOracle (spec lam K L) where
  o := OracleName.other
  sd := 2 ^ lam - 1
  pt := fun s q j => ptStd lam s (Nat.pair (Nat.pair (codeP q).1 (codeP q).2) j)
  inj := fun s q j s' q' j' h => by
    obtain ⟨h1, h2⟩ := pt_inj lam s _ s' _ h
    obtain ⟨h3, h4⟩ := Nat.pair_eq_pair.1 h2
    obtain ⟨h5, h6⟩ := Nat.pair_eq_pair.1 h3
    exact ⟨h1, codeP_inj (Prod.ext h5 h6), h4⟩
  ψ := (sigmaStdB lam K L).ψ

variable {lam} {L} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- The standard source of coins of the committer, with labels. -/
def sigmaLabB : SeedOracle (spec lam W.K L) := flatOf WP p (blocksStd lam) (tauStdB lam W.K L)

theorem sigmaLabB_o : (sigmaLabB W WP p).o = OracleName.other := rfl

theorem sigmaLabB_sd : (sigmaLabB W WP p).sd + 1 = 2 ^ lam := sigmaStdB_sd lam W.K L

theorem bias_sigmaLabB_w : (sigmaLabB W WP p).bias (blocksStd lam).w = 0 :=
  bias_sigmaStdB_w lam W.K L

end Seed
end Compile.Batch
