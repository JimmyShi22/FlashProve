-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkLaidTwoViews.lean: the link strategy that the scheme of E2E/LinkLaidPrivacy.lean plays does
not ignore the index: adding 1 to one cell of the index changes what it sends in the clear, at one
verifier message, at every coin.

Summary. Johnson/LinkSim/AtHome/TwoPlains.lean proves, for the explicit link prover, that adding 1
to cell (0, 0) of the index changes the plain messages of its run (`two_plains`). This file states
that fact for the strategy that `laidAt` plays for a link, and does the same for the weaker
statements of Johnson/LinkSim/AtHome/TwoViews.lean on disclosed views. These are negative facts
about the prover's run: two things differ. No property is claimed. The main limit: the comparison is
coin by coin; for the two outputs, which are distributions over the coins, nothing follows.

Main results, at the parameters with an all-zero digest. None has a premise.
  `laid_plains_differ`: for every index i, all randomness and seeds and every coin, the plain
    messages of the run of the strategy that `laidAt` plays for a link differ between i and the
    index with 1 added at cell (0, 0), for the verifier message `zeroAtHome Z c₀`, whose hash blocks
    are all 0. This is `two_plains`, applied.
  `laid_views_differ`: the same for the disclosed views (`homeView`), each at its own two OOD
    samples.
  `laid_two_views`: the link prover of `laidAt` is `explicitLinkProver b Z`, and `TwoViewsAt b Z` holds.
  `laid_view`: `homeView`, for the private input (i, u, v), both tables' OOD samples and a coin, is
    the disclosed view of the run of the strategy that `laidAt` plays for a link there. By
    unfolding.

Which of these says that a message changes. A disclosed view also holds the symbols that are read in
the two encoded indices. So by their type `TwoViewsAt`, `laid_two_views` and `laid_views_differ`
would also hold for a link prover that sends fixed messages: as guards against "constant in the
index" they cannot fail. `two_plains` and `laid_plains_differ` are about the plain messages. For a
link prover that sends fixed messages `two_plains`' statement is false (`silent_not_two_plains`,
Johnson/LinkSim/AtHome/TwoPlains.lean).

Terms: E2E/HidingTerms.lean.

Limits.
- The same coin on both sides. In the words of Johnson/LinkSim/AtHome/TwoViews.lean: "The two views
  differ coin by coin; of the two outputs, which are distributions over the coins, nothing follows."
  And of Johnson/LinkSim/AtHome/TwoPlains.lean: "two families of points that differ coin by coin can
  have the same distribution."
- One verifier message, after the trivial first round. The range of all indices and the set of all
  seeds; the indices are matrices of the type, not those of any model.
- Before any hashing: it is about the interactive protocol's run. Nothing on the hashed link proof.
- It is stated at `homeR b Z`, the input at one fixed digest. That `VerifierAndGoals.verify` is ever called at
  this input is not proved (the header of E2E/LinkLaidPrivacy.lean).
- All limits of Johnson/LinkSim/AtHome/TwoViews.lean and Johnson/LinkSim/AtHome/TwoIndices.lean
  hold.

Definition.
  `TwoViewsAt b Z`: the statement of `two_views_valid`, verbatim: there are two valid private inputs
    with their instances, the same randomness and seeds, two indices, and a verifier message at
    which the prover aborts for neither, such that at every coin the two disclosed views differ.


-/
import E2E.LinkLaidPrivacy
import Johnson.LinkSim.AtHome.TwoPlains

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.LinkLaid
open OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.LinkSim (validLk)
open OnBytes.LinkSim.AtText
open Johnson.Prover.Link
open _root_.Desc.K15 (frP)
open _root_.Iop (Rho Tr Strat InteractiveOracleProof DView Honest)
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)
open _root_.Run.PQ (CK)
open TypedOracleCompiler.Run.PQ (RD SOf uL drawnSL rvSL)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **Two indices, two disclosed views**: the statement of `two_views_valid`. -/
def TwoViewsAt : Prop :=
  ∃ (w w' : HomeWt b Z) (x x' : OnBytes.Flat.RecFull × OnBytes.Flat.RecFull),
    OnBytes.LinkSim.validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w x ∧
    OnBytes.LinkSim.validLk (homeR b Z).protocol (fun _ => True) (fun _ => True) w' x' ∧
    w'.1 ≠ w.1 ∧ w'.2 = w.2 ∧
    ∃ ρ : Rho (HomeQ Z).shape,
      ρ ∉ (explicitLinkProver b Z).withheld w x ∧ ρ ∉ (explicitLinkProver b Z).withheld w' x' ∧
      ∀ c : Johnson.Prover.Link.Kc, homeView b Z w x c ρ ≠ homeView b Z w' x' c ρ

variable (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- **For the link prover of `laidAt`.** No premise. -/
theorem laid_two_views :
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs.Lk = explicitLinkProver b Z ∧ TwoViewsAt b Z :=
  ⟨rfl, two_views_valid b Z⟩

/-- That file's disclosed view is the disclosed view of the run of the strategy that the scheme
plays for a link. -/
theorem laid_view (i : (homeR b Z).Index) (u v : (homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed)
    (κ : Johnson.Prover.Link.Kc) (ρ : Rho (HomeQ Z).shape) :
    homeView b Z (i, u, v) ((homeR b Z).protocol.recOf i u.1 u.2, (homeR b Z).protocol.recOf i v.1 v.2) κ ρ =
      (HomeQ Z).dview ((homeR b Z).protocol.recOf i u.1 u.2, (homeR b Z).protocol.recOf i v.1 v.2)
        ((explicitLinkProver b Z).ext (i, u, v))
        (((laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st.Lk i u v κ).run ρ).1 := rfl

/-- For every index, the view there and the view for the index with 1 added at cell (0, 0) differ,
each at its own two OOD samples, at every coin. -/
theorem laid_views_differ (i : (homeR b Z).Index) (u v : (homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed)
    (κ : Johnson.Prover.Link.Kc) (c₀ : (_root_.Run.PQ.s0 (_root_.Run.ckP .two)).up.Chal) :
    homeView b Z (i, u, v) ((homeR b Z).protocol.recOf i u.1 u.2, (homeR b Z).protocol.recOf i v.1 v.2) κ
        (zeroAtHome Z c₀) ≠
      homeView b Z (bumpWt b Z (i, u, v))
        ((homeR b Z).protocol.recOf (bumpWt b Z (i, u, v)).1 u.1 u.2,
          (homeR b Z).protocol.recOf (bumpWt b Z (i, u, v)).1 v.1 v.2) κ (zeroAtHome Z c₀) :=
  two_views b Z (i, u, v) _ _ κ c₀

/-! ## The plain messages themselves -/

/-- **For the strategy that the scheme plays for a link**: the plain messages of its run for the
index i and for the index with 1 added at cell (0, 0) differ: the same randomness and seeds, the
same coin. -/
theorem laid_plains_differ (i : (homeR b Z).Index) (u v : (homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed)
    (κ : Kc) (c₀ : (_root_.Run.PQ.s0 (ckP .two)).up.Chal) :
    (((laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st.Lk i u v κ).run (zeroAtHome Z c₀)).1.plains ≠
      (((laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st.Lk (bumpWt b Z (i, u, v)).1 u v κ).run
        (zeroAtHome Z c₀)).1.plains :=
  two_plains b Z (i, u, v) _ _ κ c₀

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.laid_two_views
#print axioms AtPublicFiles.LinkLaid.laid_view
#print axioms AtPublicFiles.LinkLaid.laid_views_differ
#print axioms AtPublicFiles.LinkLaid.laid_plains_differ
