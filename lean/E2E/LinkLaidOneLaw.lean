-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkLaidOneLaw.lean: for the explicit link prover, two private inputs with the same OOD samples
and the same symbols read give the same output.

Summary. E2E/LinkGoodCanFail.lean derives a condition under which the premise on the link's
simulator fails: two private inputs that share their OOD samples and the symbols read but give
different outputs. This file proves that the explicit link prover does not meet that condition: for
it "the two outputs differ" is false. The main limit: no prover that does meet the condition is
exhibited, so nothing here proves that the premise ever fails.

Main result, at the parameters with an all-zero digest.
  `laid_one_law` (`OneLawAt R a`): for public files Z in scope and `laidAt` with all its parameters
    arbitrary: for all indices i and j, all randomness and seeds, and every verifier message with
    the proof-of-work test bits 0: if the two pairs of OOD samples are equal and the symbols read in
    the encodings are the same, the link prover's two outputs are the same. An output is a
    distribution over the prover's coins.

How. `premW_laid` (E2E/LinkLaidPrivacy.lean) and `link_outputs_agree` (E2E/LinkGoodCanFail.lean).
`premW_laid` is applied with one copy, no session, coins of length 0 and a list E of each value once
(`bitsE_listed`); the link prover is the same for all parameters (`laid_side`).

Terms: E2E/HidingTerms.lean.

Limits.
- That there are two such private inputs at two indices is not proved here. Where there is none but
  a private input with itself, the statement says nothing.
- No pair of private inputs is known for which this statement and `laid_plains_differ`
  (E2E/LinkLaidTwoViews.lean) both say something. That one's two private inputs have the same
  randomness and seeds; this one asks for the same OOD samples and the same symbols read, which is
  proved nowhere for such a pair. The two do not clash: that one compares two points at each coin,
  this one two distributions over the coins.
- It restates, for two private inputs, what the simulator's clause says for each. No property is
  claimed beyond that clause.
- It is about the interactive link protocol, before any hashing.
- It is stated at `homeR b Z`, the input at one fixed digest. That `VerifierAndGoals.verify` is ever called at
  this input is not proved (the header of E2E/LinkLaidPrivacy.lean).

Definitions and helper lemmas.
  `OneLawAt R a`: the statement, for arbitrary R and arbitrary parameters a.
  `oneLaw_of`: it holds where `PremW` holds for a at all indices and all seeds, with the link's
    error 0, and the link prover's set `Hid` is empty.
  `oneLaw_congr`: the statement reads only the link prover.


-/
import E2E.LinkLaidPrivacy
import E2E.LinkGoodCanFail

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.CanFail
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (homeR)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- **The same OOD samples, the same symbols read: one output**, for arbitrary R. -/
def OneLawAt (R : InnerCompilerInput) (a : AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) : Prop :=
  ∀ (i j : R.Index) (r r' s s' : R.protocol.EncodingRandomness) (e e' f f' : R.protocol.OutOfDomainSeed) (ρ : Rho R.protocol.link.shape),
    (R.protocol.recOf i r e, R.protocol.recOf i r' e') = (R.protocol.recOf j s f, R.protocol.recOf j s' f') →
    R.protocol.link.extAns (R.protocol.recOf i r e, R.protocol.recOf i r' e')
        (RoundsQueryLayout.zero R.protocol.link.shape R.linkRoundSplits (wLC R.queryLayout).sh ρ) (R.protocol.encodeIndex i r, R.protocol.encodeIndex i r') =
      R.protocol.link.extAns (R.protocol.recOf j s f, R.protocol.recOf j s' f')
        (RoundsQueryLayout.zero R.protocol.link.shape R.linkRoundSplits (wLC R.queryLayout).sh ρ) (R.protocol.encodeIndex j s, R.protocol.encodeIndex j s') →
    a.Hs.Lk.output (i, (r, e), (r', e')) (R.protocol.recOf i r e, R.protocol.recOf i r' e')
        (RoundsQueryLayout.zero R.protocol.link.shape R.linkRoundSplits (wLC R.queryLayout).sh ρ) =
      a.Hs.Lk.output (j, (s, f), (s', f')) (R.protocol.recOf j s f, R.protocol.recOf j s' f')
        (RoundsQueryLayout.zero R.protocol.link.shape R.linkRoundSplits (wLC R.queryLayout).sh ρ)

theorem oneLaw_of (R : InnerCompilerInput) (a : AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (Sm : Sims R.protocol)
    (Ryes : R.Index → R.Instance → Prop) (c : CoinNums R.LeafBody) (N : NumsW)
    (hP : PremW R.queryLayout R.seedQueries R.answerCode R.compilerParameters a Sm (fun _ => True) (fun _ => True) Ryes c N)
    (hz : N.zL = 0) (hH : ∀ w x ρ, ρ ∉ a.Hs.Lk.Hid w x) : OneLawAt R a :=
  fun i j r r' s s' e e' f f' ρ hx ha =>
    link_outputs_agree (hz ▸ hP.good) i j r r' s s' e e' f f' trivial trivial trivial trivial
      trivial trivial ρ hx ha (hH _ _ _) (hH _ _ _)

/-- The statement reads only the link prover. -/
theorem oneLaw_congr (R : InnerCompilerInput) (a a' : AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (h : a'.Hs.Lk = a.Hs.Lk) (H : OneLawAt R a) : OneLawAt R a' := by
  unfold OneLawAt at H ⊢
  rw [h]
  exact H

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **At `homeR b Z` and `laidAt`**, with all its parameters arbitrary, for public files Z in scope.
-/
theorem laid_one_law (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (scope : InScope Z = true) :
    OneLawAt (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E) := by
  obtain ⟨E', hE'⟩ := bitsE_listed b Z b₀ 0 0 ℓr capT capL capB
  exact oneLaw_congr (homeR b Z) (laidAt b Z b₀ 0 0 ℓr capT capL capB E')
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
    ((laid_side b Z b₀ M ℓ ℓr capT capL capB E).trans
      (laid_side b Z b₀ 0 0 ℓr capT capL capB E').symm)
    (oneLaw_of (homeR b Z) (laidAt b Z b₀ 0 0 ℓr capT capL capB E') _ (fun _ _ => True) _ _
      (premW_laid b Z b₀ 0 0 0 ℓr capT capL capB E' scope (by decide) (Nat.zero_le _)
        (Nat.zero_le _) hE' fun _ _ => True) rfl fun _ _ _ h => h)

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.oneLaw_of
#print axioms AtPublicFiles.LinkLaid.oneLaw_congr
#print axioms AtPublicFiles.LinkLaid.laid_one_law
