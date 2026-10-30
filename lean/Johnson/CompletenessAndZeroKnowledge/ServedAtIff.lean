-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ServedAtIff.lean: ServedAt (Johnson/Face/NeverBuilt.lean) and the statements' ServedRequest are one relation.

1.  WHAT IS CLAIMED: at settings read from the files, at the index and instance types of the protocol, ServedAt holds exactly where ServedRequest does, at
    any bound. Their two builders and two maps from weights are one: the one text but for the input that they go through.
2.  servedAt_eq: so the two are equal as relations, and what is stated at ServedRequest speaks of theProvers.
-/
import VerifiableInference.Final.ModelTieAtFiles
import Johnson.Face.NeverBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Compilation.Seam
open VerifierAndGoals FlashProve
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles
open LPFD.Full (XF)

variable (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

section General
variable (b : PublicFiles → ℕ)

-- In a variable b Lean need not evaluate the number committerCoinCountLessOne Z when it compares the index types of the two inputs.
theorem servedAt_iff_gen (i : FullSizeMatrix) (x : XF) :
    ServedAt Z (settingsOfRead pp) i x ↔ ServedRequest b Z hr i x := by
  constructor
  · rintro ⟨w, p, o, hi, hform, hres, hb⟩
    have hq : Flat.buildReq (p, o) [] = some x :=
      (build_dStarBuilt flashProveData Z allZeroDigest [] (p, o) []).symm.trans hb
    exact ⟨w, p, o, hi, hform, hres, (congrFun (congrFun (FlashProve.build_home b Z) (p, o)) []).trans hq⟩
  · rintro ⟨w, p, o, hi, hform, hres, hb⟩
    have hq : Flat.buildReq (p, o) [] = some x :=
      (congrFun (congrFun (FlashProve.build_home b Z) (p, o)) []).symm.trans hb
    exact ⟨w, p, o, hi, hform, hres, (build_dStarBuilt flashProveData Z allZeroDigest [] (p, o) []).trans hq⟩

end General

/-- **One relation**, at the bound of the statements. -/
theorem servedAt_iff (i : FullSizeMatrix) (x : XF) :
    ServedAt Z (settingsOfRead pp) i x ↔ servedAt Z hr i x :=
  servedAt_iff_gen Z hr committerCoinCountLessOne i x

/-- The two as relations. -/
theorem servedAt_eq : (ServedAt Z (settingsOfRead pp) : FullSizeMatrix → XF → Prop) = servedAt Z hr :=
  funext fun i => funext fun x => propext (servedAt_iff Z hr i x)

end VerifiableInference.Compilation.Seam

#print axioms VerifiableInference.Compilation.Seam.servedAt_iff_gen
#print axioms VerifiableInference.Compilation.Seam.servedAt_iff
#print axioms VerifiableInference.Compilation.Seam.servedAt_eq
