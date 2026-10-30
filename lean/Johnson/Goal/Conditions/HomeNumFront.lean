-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeNumFront.lean: at the description's own input (homeR, homeT:
Johnson/Goal/Conditions/HomeAtWider.lean), at every value d of the public reading: the told OOD-seed
wire's test on the copy's number reads the number that the front round's plain part holds.
This file states no goal. One statement, by unfolding.

Main names (namespace FlashProve).
  num_homeT   ((homeT b Z).Sd d).num k π is "the front round's plain part of π holds the number k",
    as a Boolean.

Why. A theorem on the session's honest prover that takes any OOD-seed wire at the input's wiring
asks just this of the wire. With it the clause "honest" of the last list (LastFits,
Johnson/Goal/Conditions/HomeLast.lean), which speaks at every d, can be fed at one wiring.

Limits. On one field of the wire. Nothing on any prover.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeAtWider

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **The told wire's test on the copy's number reads the front round's number**, at every d. -/
theorem num_homeT (b : PublicFiles → ℕ) (Z : PublicFiles) (d : (homeT b Z).D) (k : ℕ) (π) :
    ((homeT b Z).Sd d).num k π =
      decide (((chainsOf (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
        (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
        ByteArray.empty).plF π).copy = k) := rfl

end FlashProve
