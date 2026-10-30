-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SpellsC.lean: THE FIRST EQUATION OF THE INTERFACE (SpellsC,
Johnson/Bind/Cpp/Spells.lean), PROVED, at all public files Z and every hash function, under no
premise: the told part of the public reading's value is the hash function's answer at the string of
the three public files.

Why. The written committer (LayoutsByPublicReading.commitAtCoins, Johnson/Top/ToldCommitPlain.lean) lays beside its
key "the told part of d", d the value of the told structure's public reading. The running committer
(Johnson/Bind/Twin.lean) asks the format's hash for the digest of the three public files. The tie
between the two wants that these are one digest.

How. Two fields of the told structure are named by `T₀_fields`
(Johnson/Goal/Conditions/BindsPlain.lean; not called here: both equations hold by unfolding): the
public reading is `pub8` and the told part is `cfg8`, the first of its answers
(Johnson/Top/PreThreePub.lean). `pub8_det` gives the reading's value. Its
first string `s0Of` (Johnson/Top/Pub/PubStrings.lean) has the text of `configString` (Ladder.lean).

Main names (namespace Bind.Cpp): `dAt_value`, `part_value`, **`spellsC`**.
Limits. One equation between terms of this library. Nothing on any program; no binding of the
commitment (the opening form, BindsWith), no correctness of extraction, no index privacy (hiding of
the weights).
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Spells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.K.Arm.Pub (pub8 cfg8 pub8_det)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem OnBytes.K.Arm.Pub.pub8 PV.EncId.encF LPFD.Full.mD
  LPFD.Full.mOneAt PV.MFull.cfgF

/-- The public reading's value at a hash function is `pub8`'s. -/
theorem dAt_value (Z : PublicFiles) (hash : Hash) :
    dAt Z hash = (pub8 OnBytes.Tie.recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay).det
      (_root_.Run.famOne hash) := rfl

/-- The told part is the first answer. -/
theorem part_value (Z : PublicFiles) (d : (T₀ Z).D) : (T₀ Z).part d = cfg8 d := rfl

/-- **THE TOLD PART IS THE FILES' DIGEST.** -/
theorem spellsC (Z : PublicFiles) (hash : Hash) : SpellsC Z hash := by
  show (T₀ Z).part (dAt Z hash) = hash (configString Z)
  rw [part_value, dAt_value, pub8_det]
  rfl

end Bind.Cpp

end

#print axioms Bind.Cpp.dAt_value
#print axioms Bind.Cpp.part_value
#print axioms Bind.Cpp.spellsC
