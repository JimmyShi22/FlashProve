-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySFileN.lean: the written counts of a whole file, with the shared rounds' counts
taken N times, are shares of at most εs, from the three chains' counts.



OnBytes/Flat/CarrySFile.lean has the written counts of a whole file (`errFile`) and `below_file`. A
file that is one of N in a session under one binding tree pays the counts of its shared rounds N
times (`Err.timesShared`, Iop/BatchSound.lean). By the file's annotation the shared rounds are the
joining round and the shared chain's. One theorem.

Main names:
  `below_file_shared`: asked: the first and the last chain's counts are shares of at most εs, and so
    are the shared chain's, N times.

Limits: this is the coarse count: every shared round pays N. It costs nothing where N = 1. Where N
is large and the shared chain's counts are near εs its second premise cannot be met: there the
finer rule is wanted, in which the head of the shared chain alone pays N
(OnBytes/TypedOracleCompiler/Joined/Fine.lean [not in this library]). No protocol occurs here.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySFile
import OnBytes.TypedOracleCompiler.Joined.TwoChains

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob OnBytes.Slice
open _root_.Compile.Joined (Chains)
open scoped ENNReal

variable {G : Chains}

/-- The same with the shared rounds' counts taken N times: asked of the shared chain's counts N
times. -/
theorem below_file_shared (hG : G.Laws) (N : ℕ) {ε₁ : Err G.s₁} {ε₂ : Err G.s₂} {ε₃ : Err G.s₃}
    {εs : ℝ≥0∞} (h₁ : Err.Below ε₁ εs) (h₂ : Err.Below (Err.times N ε₂) εs)
    (h₃ : Err.Below ε₃ εs) :
    Err.Below (Err.timesShared N G.ann (errFile G ε₁ ε₂ ε₃)) εs := by
  show Err.Below (Err.timesShared N (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃))
    (Err.app ((0, ε₁) : Err G.c₁) (Err.app ((0, ε₂) : Err G.c₂) ((0, ε₃) : Err G.c₃)))) εs
  rw [TypedOracleCompiler.Joined.timesShared_app, TypedOracleCompiler.Joined.timesShared_app,
    TypedOracleCompiler.Joined.timesShared_lo N G.A₁ _ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₁),
    TypedOracleCompiler.Joined.timesShared_sh N G.A₂ _
      ⟨hG.kindJ, RoundSplits.allKind_const .sh _ (fun _ => rfl) G.s₂⟩,
    TypedOracleCompiler.Joined.timesShared_lo N G.A₃ _ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₃)]
  exact Err.Below.app (s := G.c₁) ⟨by rw [Nat.cast_zero]; exact zero_le _, h₁⟩
    (Err.Below.app (s := G.c₂)
      ⟨by rw [Nat.mul_zero, Nat.cast_zero]; exact zero_le _, h₂⟩
      ⟨by rw [Nat.cast_zero]; exact zero_le _, h₃⟩)

end OnBytes.Flat
