-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubChall.lean: the experiments of zero-knowledge compilation for batches, with a
function of the key published at the setup. Definitions only, but for two equations that hold by
definition (words of this library: lean/GLOSSARY.md).

The reply to the first call "setup" is pw ivk (keyOf isk) for an arbitrary type V and an arbitrary
function pw : IVK → WKey → V, where `keyOf isk` (Compile/Batch/Mirror.lean) is what the reduction
(`wrapBP`, Compile/Batch/PubWr.lean) keeps of the proving key: for each copy its tree (all digests;
for each salted leaf the numbers of two tokens, which are numbers and not strings) and the proof
string of its Link.

  `BInP V`, `replyOfP`  the replies: an element of V, or the proofs of the adversary's own requests
  `toP`, `toP_replyOf`, `toP_inr`  a reply to a batch in the form of Compile/Batch/Chall.lean, as a
                                   reply here (so that the statements on the prover's program can be
                                   used as they are)
  `VCBP`  the challenger whose steps are programs with tokens (`Step`, Rom/Defer.lean)
  `chalLBP`, `chalLSBP`  the challengers in the late language (`LStep`, Rom/DeferLate.lean), without
                         and with the rejection of a batch on a copy that has served s1 batches

Notation:
  `L`: an `BatchProtocol I X`: the record of protocols (Test, Link, Batch; Iop/Batch.lean)
  `W`: a `QueryLayout lam L`, the wire record (Iop/BatchWire.lean)
  `WP`: a `WireBP L`: the prover's data for the three protocols, and the enumeration of the encoding
    randomness (Iop/BatchWireP.lean)
  `p`: a `Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of
    the salt of a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1; `p.s1`: a
    copy serves at most s1 batches in `chalLSBP`
  `i`: I, the index; the state Option (IskH lam L × ℕ): none before the setup, then the key and N₀;
    `IskH`: Compile/Batch/Star.lean
  `N₀`, `t₀`: number N₀ of tokens of the setup, number t₀ of tokens so far (`LeafGame.sess`,
    Compile/Batch/OverrunGen.lean); `virt N₀ δ c`: the program c under the renumbering
    (Compile/Step1_life2_Virt.lean)

After Compile/Batch/Chall.lean and Compile/Batch/ChallL.lean with the reply to the setup replaced
(these two files define no challenger).
-/
import Compile.Batch.ChallL

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.GlueB (GCall ownPf)
open Compile.Life2 (virt)
open Compile.DefC (virtL)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the replies of the experiment: what the setup publishes, or the proofs of the adversary's own
requests -/
abbrev BInP (V : Type) (lam : ℕ) (L : BatchProtocol I X) : Type := GlueB.GIn V (Prf lam L)

/-- the reply to a batch (`replyOf` of Compile/Batch/Chall.lean) -/
def replyOfP (V : Type) (b : Gen.Batch X Unit) (πs : List (Prf lam L)) : BInP V lam L :=
  .inr (ownPf b (fitLen ⟨0, default, none, none⟩ b.pairs.length πs).val)

/-- a reply to a batch in the form of Compile/Batch/Chall.lean, as a reply here -/
def toP (V : Type) (a : BIn lam L) : BInP V lam L := .inr (GlueB.listOf a)

theorem toP_replyOf (V : Type) (b : Gen.Batch X Unit) (πs : List (Prf lam L)) :
    toP V (replyOf b πs) = replyOfP V b πs := rfl
theorem toP_inr (V : Type) (l : List (Prf lam L)) : toP V (.inr l : BIn lam L) = .inr l := rfl

variable {V : Type} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)



/-- The challenger. Its state: none before the setup, then the key and the number N₀ of tokens of
the setup. The first call "setup" runs `Cp` on i and replies pw ivk (keyOf isk); a second one, and
a batch before the setup, get the reply `.inr []` and change nothing. A batch with a request of the
adversary's own (`hasOwn b`) runs `Pp` at the flags `ownFlag b`, under the renumbering
`virt N₀ (t₀ + 1 - N₀)` (t₀: the number of tokens so far), and gets the reply `replyOfP V b`; a
batch without one gets `.inr []`. -/
abbrev VCBP : Chall (spec lam W.K L) (split lam W.K L) (GCall X Unit) (BInP V lam L) where
  τ := Option (IskH lam L × ℕ)
  step := fun s c => match c, s with
    | .setup, none =>
      (Cp W WP p i).bind fun o =>
        Step.fresh 0 fun t => Step.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t))
    | .setup, some k => Step.pure (.inr [], some k)
    | .batch _, none => Step.pure (.inr [], none)
    | .batch b, some (k, N₀) =>
        if hasOwn b then
          Step.fresh 0 fun t₀ =>
              (virt N₀ (t₀ + 1 - N₀) (Pp W WP p k (ownFlag b) (reqs b))).bind fun πs =>
            Step.pure (replyOfP V b πs, some (k, N₀))
        else Step.pure (.inr [], some (k, N₀))

/-- The challenger in the late language, still with the true data (`CpL`, `PpL` on the index i). -/
def chalLBP : LChall (spec lam W.K L) (split lam W.K L) (GCall X Unit) (BInP V lam L) where
  τ := Option (IskH lam L × ℕ)
  step := fun s c => match c, s with
    | .setup, none =>
      (CpL W WP p i).bind fun o =>
        LStep.fresh 0 fun t => LStep.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t))
    | .setup, some k => LStep.pure (.inr [], some k)
    | .batch _, none => LStep.pure (.inr [], none)
    | .batch b, some (k, N₀) =>
        if hasOwn b then
          LStep.fresh 0 fun t₀ =>
              (virtL N₀ (t₀ + 1 - N₀) (PpL W WP p k (ownFlag b) (reqs b))).bind fun πs =>
            LStep.pure (replyOfP V b πs, some (k, N₀))
        else LStep.pure (.inr [], some (k, N₀))

/-- The same as `chalLBP`, rejecting a batch on a copy that has served s1 batches. -/
def chalLSBP : LChall (spec lam W.K L) (split lam W.K L) (GCall X Unit) (BInP V lam L) where
  τ := Option (IskH lam L × ℕ × (ℕ → ℕ))
  step := fun s c => match c, s with
    | .setup, none =>
      (CpL W WP p i).bind fun o =>
        LStep.fresh 0 fun t => LStep.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t, fun _ => 0))
    | .setup, some k => LStep.pure (.inr [], some k)
    | .batch _, none => LStep.pure (.inr [], none)
    | .batch b, some (k, N₀, c) =>
        if hasOwn b then
          LStep.fresh 0 fun t₀ => LStep.sample p.M fun j =>
            if c j.val < p.s1 then
              (virtL N₀ (t₀ + 1 - N₀) (PpLJ W WP p k (ownFlag b) (reqs b) j)).bind fun πs =>
                LStep.pure (replyOfP V b πs, some (k, N₀, Function.update c j.val (c j.val + 1)))
            else LStep.pure (.inr [], some (k, N₀, c))
        else LStep.pure (.inr [], some (k, N₀, c))

end Compile.Batch
