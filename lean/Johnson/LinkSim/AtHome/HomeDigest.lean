-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeDigest.lean: the protocol structure of homeR b Z depends neither on the
digest nor on b.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves, all by unfolding. Take the input of the transformation at any b, public files
Z, digest c and further digests m. homeR_L_at: its protocol structure protocol is (flashProveDescription.F Z).withProvers (flashProveDescription.P Z), in
which neither c, m nor b occurs; homeR b Z is the case c = allZeroDigest, m = []. homeR_I_at: its type Index is
(flashProveDescription.C Z).I, likewise. homeR_L_b: (homeR b' Z).protocol = (homeR b Z).protocol for any two b and b'. homeR_link:
(homeR b Z).protocol.link = HomeQ Z, the link protocol of Johnson/LinkSim/AtHome/TwoViews.lean.

So the encoder, the OOD samples and the link protocol, which are all parts of protocol, are the same at
every digest and every b.

How it fits. It is the lemma behind Home.lean's limit on the digest. That homeExactAt's statement
reads of homeR b Z only its type Index and its protocol structure protocol is by inspection of seven
definitions, not proved: HomeWt, homeExt, homeIn, explicitLinkProver and homeSim (SpecHome.lean), HomeQ
(TwoViews.lean) and homeInst (HomeExactAll.lean).

Names (namespace OnBytes.LinkSim.AtHome): homeR_I_at, homeR_L_at, homeR_L_b, homeR_link.

Limits.
- The compilation data (W, Sd, cA, p) may depend on the digest; nothing is proved of them here. So
  linkFieldsHome and the files Compile*.lean are still stated at the one digest (see Home.lean's
  limits).
- Nothing here is about dependence on the public files Z.

Notes.
- A form that sets the input at (c, m) and homeR b Z side by side is not stated; homeR_L_at says the
  same.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.TwoViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.LinkSim (validLk)
open _root_.Iop (Rho InteractiveOracleProof Honest prRho)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- The protocol structure does not depend on b. -/
theorem homeR_L_b (b' : PublicFiles → ℕ) : (homeR b' Z).protocol = (homeR b Z).protocol := rfl

/-- The link protocol of homeR b Z is HomeQ Z. -/
theorem homeR_link : (homeR b Z).protocol.link = HomeQ Z := rfl

/-- At every digest and all further digests, the protocol structure is one term, in which no digest
and no b occurs: the structure made of the three protocols at Z and their provers. -/
theorem homeR_L_at (c : Digest) (m : (flashProveDescription.reBound b).More) :
    ((flashProveDescription.reBound b).input Z c m).protocol = (flashProveDescription.F Z).withProvers (flashProveDescription.P Z) := rfl

/-- At every digest and all further digests, the type of indices is one term, in which no digest and
no b occurs. -/
theorem homeR_I_at (c : Digest) (m : (flashProveDescription.reBound b).More) :
    ((flashProveDescription.reBound b).input Z c m).Index = (flashProveDescription.C Z).I := rfl

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.homeR_I_at
#print axioms OnBytes.LinkSim.AtHome.homeR_L_at
#print axioms OnBytes.LinkSim.AtHome.homeR_L_b
#print axioms OnBytes.LinkSim.AtHome.homeR_link
