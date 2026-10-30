-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WireDepthZero.lean: at every key's chains that the verifier program admits, the depth
of the request tree of the key file's calls in the written wiring is 0.

Theorems; no definition. Johnson/Flat/WireAt.lean lays that depth as the depth of the binding tree
in the key's chains' parameters (`G.k.oneTime.binding.logLeaves`), at a letter G. The hypotheses on
the key file's soundness count a shared round's error 2 ^ that depth times (`CompilerSoundnessConditionStatements.keySound`,
Johnson/Top/InnerCompiledVerifier.lean). The program's own test on a key's public values admits one leaf alone
(`Key.fixedOk`, OnBytes/Key/Fixed.lean; `Key.admitted`, OnBytes/Key/OneTime.lean), and its check of
a key file says yes only where that test passed. So there the factor is 1.

Main names:
  `logLeaves_of_admitted`: where `Key.admitted p = true`: `p.binding.logLeaves = 0`.
  `admitted_of_check`: where `Key.check k file` returned a table: `Key.admitted k.oneTime = true`.
  `wireFullAt_depthT_zero`, `wireSmallAt_depthT_zero`: where `Key.admitted G.k.oneTime = true`: the
    wiring's field `depthReqT` is 0.
  `wireFullAt_depthT_of_check`, `wireSmallAt_depthT_of_check`: the same where the program's check of
    a key file at G's chains returned a table.

Limits: G stays a letter: that its chains are admitted, or that a check at them said yes, is a
premise. A, E, P are letters too: no value of them is given (Johnson/Flat/TwoSizes.lean's Limits).
At a G at the plan of Z (`AtPlan Z G`), where the program said yes (`PortYesAt`,
OnBytes/K/Top.lean) on files with Z's three public files, `atPlan_port` (OnBytes/Flat/BigAt.lean)
gives that premise (`Key.check G.k F.key = .ok table`); no theorem here makes that step. Beyond
this file, no file calls the six theorems yet. The hypothesis `CompilerSoundnessConditionStatements.keySound` at the written
wiring (a field of `RemainingSoundnessConditionsFromDryRunAtFullSize` | `RemainingSoundnessConditionsFromDryRunAtSmallSize`, Johnson/Flat/TwoSizes.lean) is still asked at a
letter G, with the factor 2 ^ `G.k.oneTime.binding.logLeaves`: no theorem here names it or rewrites
it, and it stays unproved. "The factor is 1" is 2 ^ 0: by reading; no theorem states it. "The
program" is here `verify-on-bytes`, the verifier written in Lean (`Key.check`,
OnBytes/Key/File.lean): of the C++ verifier `cp_verify` nothing is said. No number but that depth
is evaluated. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WireAt
import OnBytes.TieK.Chains

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat OnBytes.Slice

/-- The program's test on a key's public values admits a binding tree of one leaf alone. -/
theorem logLeaves_of_admitted {p : Params.OneTime} (h : Key.admitted p = true) :
    p.binding.logLeaves = 0 := by
  unfold Key.admitted Key.fixedOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

/-- The program's check of a key file returns a table only at chains that it admits. -/
theorem admitted_of_check {k : Params.KeyChains} {file : ByteArray} {table : Params.TableName}
    (h : Key.check k file = .ok table) : Key.admitted k.oneTime = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, -, h2, -⟩ := TieK.key_check_chains _ _ _ h
  simpa using h2

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- **At admitted chains the key file's request tree has one leaf**, at the full size. -/
theorem wireFullAt_depthT_zero (h : Key.admitted G.k.oneTime = true) (salt : ℕ) :
    (wireFullAt A E G P salt).depthReqT = 0 :=
  (wireFullAt_depths A E G P salt).2.1.trans (logLeaves_of_admitted h)

/-- The same where the program's check of a key file at G's chains returned a table. -/
theorem wireFullAt_depthT_of_check {file : ByteArray} {table : Params.TableName}
    (h : Key.check G.k file = .ok table) (salt : ℕ) : (wireFullAt A E G P salt).depthReqT = 0 :=
  wireFullAt_depthT_zero A E G P (admitted_of_check h) salt

end

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- **At admitted chains the key file's request tree has one leaf**, at the small size. -/
theorem wireSmallAt_depthT_zero (h : Key.admitted G.k.oneTime = true) (salt : ℕ) :
    (wireSmallAt A E G P salt).depthReqT = 0 :=
  (wireSmallAt_depths A E G P salt).2.1.trans (logLeaves_of_admitted h)

/-- The same where the program's check of a key file at G's chains returned a table. -/
theorem wireSmallAt_depthT_of_check {file : ByteArray} {table : Params.TableName}
    (h : Key.check G.k file = .ok table) (salt : ℕ) : (wireSmallAt A E G P salt).depthReqT = 0 :=
  wireSmallAt_depthT_zero A E G P (admitted_of_check h) salt

end

end VerifiableInference.OnPublicFiles
