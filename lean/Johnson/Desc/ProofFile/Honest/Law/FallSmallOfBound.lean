-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallSmallOfBound.lean: the hypothesis `FallSmall`
(E2E/BridgeAccept.lean) that `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean)
asks, from ONE hypothesis: a bound, by one number, on the chance that an honest run meets a listed
bad event, at every input of `TiedOut` and all coins.

  1  `fallSmall_of_bound`   from such a bound to `FallSmall` at the same number

What it is. An unfolding: `bound` is what `FallSmall` says at these letters, written out in the
terms of `fallAt`. Only the direction from `bound` to `FallSmall` is proved.

Why. A theorem that ends in such a bound, at these rows `G`, at the prover structure that `provG`
has (the committer's `proverAt` at 0 and `H`) and at the rounds' data `D` of the `LaidAt`, enters
here: ours (`falls_uniform_listed`, Honest/Law/FallsUniformListed.lean) or another author's. This
file imports none of them.

How. By unfolding, the sets of `fallG` are those of `fallAt` at the three purses of the coin and at
the instance that `instanceAsPlainRecord` writes. The rounds' data of a `LaidAt` are the object's, by
`data_atFiles` (E2E/BridgePaidAtFiles.lean). The number of the copy and the third part of the
private input are not read by `fallAt`: in the hypothesis they stand under "there is".

Limits.
  * `bound` is a hypothesis. It is proved here of nothing.
  * The chance is over the verifier's randomness alone, at each fixed input and each fixed list of
    coins. One number `pF` serves all of them.
  * The statement says nothing where `pF` is 1 or more, where `Yes` has no member, or where `Zs`
    takes every seed.
  * The bound is asked at the kit `ckP .two` and at the three values that `fallAlong`
    (E2E/BridgeFalls.lean) lays for the chains' tags.
  * `Zs` is a letter. The same hypothesis stands in `both_atFiles` of the same file too; by its
    authors' word in seven of their theorems in all, three of them at a set of seeds of their own.
  * No number follows.
  * The name is declared in the namespace `AtPublicFiles.AtFiles`, though the file lies under Johnson/: so the
    section's variables and abbreviations read as in E2E/BridgeJoinAtFiles.lean.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse Coins fallAt drawsAt)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- As in E2E/BridgeJoinAtFiles.lean: among all that is imported, the search for this instance runs
out of its budget. It is a proposition. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- From a bound by one number, at every input of `TiedOut` and all coins, to `FallSmall` at that
number, at the family and the falls of `honFit_atFiles`. -/
theorem fallSmall_of_bound (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed) (pF : ℝ≥0∞)
    (bound : ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : ProofFile.Inst) (k : Coins B),
      (∃ n e, TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n (w₀, rc, e) x) →
      Iop.prRho {ρ : Iop.Rho (chainsOf (ckP .two) D (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
          (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty).sh |
        (fallAt G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) w₀ rc x k
          (drawsAt (ckP .two) D (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
            (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ)).isSome = true} ≤ pF) :
    FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF := by
  obtain rfl := data_atFiles Z Zp Np cF scope live L
  exact fun n w a c ht => bound w.1 w.2.1 (instanceAsPlainRecord a) (pursesOf c) ⟨n, w.2.2, ht⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.fallSmall_of_bound
