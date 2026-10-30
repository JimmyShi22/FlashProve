-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/LinkLaidAccepted.lean

What this file has. laid_accepted proves acceptance at every challenge that passes the proof-of-work
check. At every verifier message that passes the proof-of-work checks, the link's interactive
verifier accepts the explicit prover's (explicitLinkProver b Z) run, for every index, all encoding randomness
and OOD seeds of both tables, and every coin of the prover. The prover never aborts, so no passing
message is excepted. The passing messages are a small set by design (the proof of work's bits). That
such a message exists at each round, and how the hashed scheme's prover finds one, is not this
file's and is not proved here. It holds for public files in scope with a live description, and
laid_accepted_zFull and laid_accepted_zGap prove it at the library's two named sets of public files
with no premise left. So the link prover in the scheme of E2E/LinkLaidPrivacy.lean is one that the
link's interactive verifier accepts, before hashing. That it is no placeholder does not follow from
acceptance: it is two_plains with silent_not_two_plains (Johnson/LinkSim/AtHome/TwoPlains.lean),
before hashing and coin by coin. Whether this verifier also accepts the placeholder link prover is
not proved in this group of files, either way. The statement is the conclusion of homeSide_accepted
(Johnson/LinkSim/AtHome/HomeAccepted.lean), verbatim, for the link prover of laidAt.

Where this stands (in full: E2E/ZetaAtCaps.lean): index privacy says little without completeness of
the same provers. This file has a first part of that, for the link's explicit prover alone, before
hashing.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

Theorems, at `homeR b Z`.
  `laid_accepted`: for public files Z in scope with a live description, the four clauses
    `LinkAcceptedAt` hold for the link prover of `laidAt`, with no verifier message excluded
    (`Falls.none`):
    1. the strings that the link verifier reads beside the messages (the prover's "external
    strings") are the two encodings of the index;
    2. if a verifier message with its proof-of-work test bits set to 0 is one at which the prover
    aborts, so is the message itself;
    3. `AccLaw`: for every coin of the prover, the interactive verifier accepts the prover's run for
    every verifier message that passes the proof-of-work checks and at which the prover does not
    abort;
    4. the set of verifier messages at which the prover aborts has measure 0.
    Clause 3 is stated for instances with Yes i x and seeds outside Zs i r. Yes and Zs are
    arbitrary, so with Yes := True and Zs := ∅ it holds for every instance and every seed.
  `laid_accepted_zFull`, `laid_accepted_zGap`: the same at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`, with no
    premise on the public files.

Limits, the weightiest first.
- This is the interactive form, before any hashing. For a produced hashed link proof, the
  interactive verifier accepts its transcript at the challenges that hashing gives
  (AtFullSide/E2E/LinkLaidHashedAccepted.lean); that the hashed verifier accepts the proof is not
  proved. (usual for an interactive oracle proof)
- No lemma that ends in the hashed verifier's acceptance can be applied to laidAt (the header of
  E2E/LinkLaidPrivacy.lean says why).
- It covers one of the three sub-protocols; the provers of the other two are placeholders that send
  fixed messages.
- What that verifier would reject is not stated here: that is soundness.
- It is stated at homeR b Z, the input at one fixed digest; that verify is ever called at this
  digest is not proved (the header of E2E/LinkLaidPrivacy.lean).
- All limits of homeSide_accepted hold.

Tests and notes.
- Of the four clauses the second and the fourth say little: the set of verifier messages at which
  the prover aborts is empty (home_withheld, Johnson/LinkSim/AtHome/TwoViews.lean), and the empty
  set meets both.
- Why an interactive verifier's message has proof-of-work test bits: E2E/HidingTerms.lean,
  "Proof-of-work test".

Terms: E2E/HidingTerms.lean.

The definition `LinkAcceptedAt` has a docstring.

This file lies in the side library AtFullSide, which is built with a larger thread stack
(lake build AtFullSide).


-/
import E2E.LinkLaidPrivacy
import AtFullSide.E2E.AtWrittenFiles
import Johnson.LinkSim.AtHome.HomeAccepted

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles storedPublicFiles zGap)
open FlashProve (protocolDataWellFormed homeR)
open AtPublicFiles.AtWritten (open_zFull open_zGap)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- **The four clauses on the link**, for arbitrary R. -/
def LinkAcceptedAt (R : InnerCompilerInput) (Hs : ThreeProvers R.protocol) (F : Falls Hs) (Yes : R.Index → R.Instance → Prop)
    (Zs : R.Index → R.protocol.EncodingRandomness → Set R.protocol.OutOfDomainSeed) : Prop :=
  (∀ i r e r' e', Hs.Lk.ext (i, (r, e), (r', e')) =
    (R.protocol.encodeIndex i r, R.protocol.encodeIndex i r')) ∧
  (∀ w x c ρ, RoundsQueryLayout.zero R.protocol.link.shape R.linkRoundSplits (wLC R.queryLayout).sh ρ ∈
      Hs.Lk.withheld w x ∪ F.Lk w x c → ρ ∈ Hs.Lk.withheld w x ∪ F.Lk w x c) ∧
  (∀ i x r e r' e' c, Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
    AccLaw (batLC R.protocol R.linkRoundSplits) (wLC R.queryLayout)
      (R.protocol.recOf i r e, R.protocol.recOf i r' e')
      (Hs.Lk.ext (i, (r, e), (r', e')))
      (Hs.Lk.strat (i, (r, e), (r', e'))
        (R.protocol.recOf i r e, R.protocol.recOf i r' e') c)
      (Hs.Lk.withheld (i, (r, e), (r', e'))
          (R.protocol.recOf i r e, R.protocol.recOf i r' e') ∪
        F.Lk (i, (r, e), (r', e'))
          (R.protocol.recOf i r e, R.protocol.recOf i r' e') c)) ∧
  (∀ i x r e r' e' c, Yes i x →
    prRho (Hs.Lk.withheld (i, (r, e), (r', e'))
        (R.protocol.recOf i r e, R.protocol.recOf i r' e') ∪
      F.Lk (i, (r, e), (r', e'))
        (R.protocol.recOf i r e, R.protocol.recOf i r' e') c) ≤ 0)

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **At `homeR b Z`, for the link prover of `laidAt`, with no verifier message excluded.** -/
theorem laid_accepted (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed) :
    LinkAcceptedAt (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs
      (Falls.none (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs) Yes Zs :=
  homeSide_accepted b Z scope live (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs
    (Falls.none (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs) Yes Zs
    (laid_side b Z b₀ M ℓ ℓr capT capL capB E) (fun _ _ _ => rfl)

theorem laid_accepted_zFull (b₀ : (homeR b storedPublicFiles).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b storedPublicFiles b₀ M ℓ ℓr capT capL capB)
    (Yes : (homeR b storedPublicFiles).Index → (homeR b storedPublicFiles).Instance → Prop)
    (Zs : (homeR b storedPublicFiles).Index → (homeR b storedPublicFiles).protocol.EncodingRandomness → Set (homeR b storedPublicFiles).protocol.OutOfDomainSeed) :
    LinkAcceptedAt (homeR b storedPublicFiles) (laidAt b storedPublicFiles b₀ M ℓ ℓr capT capL capB E).Hs
      (Falls.none (laidAt b storedPublicFiles b₀ M ℓ ℓr capT capL capB E).Hs) Yes Zs :=
  laid_accepted b storedPublicFiles open_zFull.1 open_zFull.2 b₀ M ℓ ℓr capT capL capB E Yes Zs

theorem laid_accepted_zGap (b₀ : (homeR b zGap).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b zGap b₀ M ℓ ℓr capT capL capB)
    (Yes : (homeR b zGap).Index → (homeR b zGap).Instance → Prop)
    (Zs : (homeR b zGap).Index → (homeR b zGap).protocol.EncodingRandomness → Set (homeR b zGap).protocol.OutOfDomainSeed) :
    LinkAcceptedAt (homeR b zGap) (laidAt b zGap b₀ M ℓ ℓr capT capL capB E).Hs
      (Falls.none (laidAt b zGap b₀ M ℓ ℓr capT capL capB E).Hs) Yes Zs :=
  laid_accepted b zGap open_zGap.1 open_zGap.2 b₀ M ℓ ℓr capT capL capB E Yes Zs

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.laid_accepted
#print axioms AtPublicFiles.LinkLaid.laid_accepted_zFull
#print axioms AtPublicFiles.LinkLaid.laid_accepted_zGap
