-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtHomeT.lean: the family of inputs homeT b Z over the input homeR b Z has all the
properties that the theorems of this folder ask of a family and its public reading.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
familyLaws_home: for every b and all public files Z, FamilyLaws
(Johnson/FrontRoad/AtBuiltMore.lean) holds of the description flashProveDescription.reBound b, the values allZeroDigest and [],
the family homeT b Z (Johnson/Goal/Conditions/HomeAtWider.lean) and the pairing of a digest with a
list of digests. flashProveDescription is the built description (Johnson/Goal/Conditions/BindsAtThe.lean). flashProveDescription.reBound b
is flashProveDescription with the number of the honest committer's coins set to b Z, a field that no verifier and no
goal reads (Johnson/Goal/Conditions/ReBound.lean); its verifier is flashProveDescription's by definition
(VerifierAndGoals.verify_reBound).

  FamilyLaws.reBound   in general form: the properties carry over from a description D and a family
      T to D.reBound b and T.reBound (b Z).
  homeT_eq   homeT b Z is the family layoutsOfBuiltDescription flashProveData allZeroDigest [] Z
      (Johnson/FrontRoad/AtBuiltNamed.lean) with that number set, by definition.
  forall_home   what holds of the built description's input at every pair (c, m), with that number
      set, holds of the family's input at every d.

How it fits. The explicit link prover and its simulator (Johnson/LinkSim/AtHome/) are stated at
homeR b Z. This file lets the theorems of this folder be applied there. Not one of the release's
goal statements.

Limits. Equations and properties of terms of the library: nothing on soundness, completeness or
hiding. It is at the built description; that this is the description where the goals read it is a
theorem and not a definition (theDescription_eq, Johnson/Goal/Description/Description.lean).
-/
import Johnson.FrontRoad.AtBuiltNamed
import Johnson.Goal.Conditions.HomeAtWider

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.FrontRoad
open VerifierAndGoals FlashProve FlashProve VerifiableInference VerifiableInference.OnPublicFiles Rom
open _root_.Iop (Dig)

/-- The properties of a family carry over when the number of the honest committer's coins is set
anew: no property reads that number. -/
theorem FamilyLaws.reBound {D : Description} {Z : PublicFiles} {c₀ : Digest} {m₀ : D.More}
    {T : LayoutsByPublicReading (D.input Z c₀ m₀)} {pair : Digest → D.More → T.D}
    (h : FamilyLaws D Z c₀ m₀ T pair) (b : PublicFiles → ℕ) :
    FamilyLaws (D.reBound b) Z c₀ m₀ (T.reBound (b Z)) pair where
  onto := h.onto
  eq := fun c m => congrArg (fun r : InnerCompilerInput => r.reBound (b Z)) (h.eq c m)
  noCoin := h.noCoin
  asks := h.asks
  once := h.once
  spare := h.spare
  reads := h.reads
  total := h.total
  eight := h.eight

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- homeT b Z is the named family at the built description with the number of coins set. -/
theorem homeT_eq : homeT b Z = (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z).reBound (b Z) := rfl

/-- **All the properties hold of homeT b Z**, for every b and all public files Z. -/
theorem familyLaws_home : FamilyLaws (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z) Prod.mk :=
  (familyLaws_the Z).reBound b

/-- What holds of the built description's input at every pair (c, m), with the number of coins set,
holds of the family's input at every d. -/
theorem forall_home {Q : InnerCompilerInput → Prop} (h : ∀ c m, Q ((flashProveDescription.input Z c m).reBound (b Z)))
    (d : (homeT b Z).D) : Q ((homeT b Z).at d) :=
  forall_at (D := flashProveDescription.reBound b) (familyLaws_home b Z).onto (familyLaws_home b Z).eq h d

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.FamilyLaws.reBound
#print axioms OnBytes.FrontRoad.homeT_eq
#print axioms OnBytes.FrontRoad.familyLaws_home
#print axioms OnBytes.FrontRoad.forall_home
