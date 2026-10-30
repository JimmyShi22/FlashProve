-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeSalt.lean: at all public files in scope at which the description's own
test on the files returns true (protocolDataWellFormed), the plan's length of a leaf's salt is 40 bytes.
This file states no goal. Two statements with their proofs.

Main names (namespace FlashProve).
  saltG_the   saltG (dataAtFiles flashProveData Z).G = 40.
  bytes_forty   so strings of 40 bytes meet the clause "bytes" of the last list (LastFits,
    Johnson/Goal/Conditions/HomeLast.lean) at every such Z.

Why. The committer's bytes (the field sb of LastArgs) are one value for all public files, and the
clause "bytes" asks their length to be the plan's at each set of files. LastFits has "in scope" and
protocolDataWellFormed among its clauses. So one value serves every set of files at which the list can hold at all:
also two sets at once (Johnson/Goal/Conditions/HomePutTwo.lean [not in this library]). Whether
protocolDataWellFormed returns true at any
given files is not said here.

How. The step stood inside the proof of wordsFitAt_the (Johnson/Goal/Meaning/WordsFitAtThe.lean):
chainsOf_key_salt_at (there) at thePlan_key and publicO_at_scope. Under protocolDataWellFormed the description's
plan is thePlan: by unfolding.

Limits. A number of the plan. Nothing on any prover.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.WordsFitAtThe
import OnBytes.Prover.Print.Tidy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve
open LPFD.Full (saltG)
open OnBytes.Prover.Print (fitBytes size_fitBytes)

/-- **In scope, where protocolDataWellFormed returns true, the plan's salt has 40 bytes.** -/
theorem saltG_the (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    saltG (dataAtFiles flashProveData Z).G = 40 := by
  have hG : (dataAtFiles flashProveData Z).G = thePlan (asDescriptionFiles Z) := by
    show flashProveData.filesParametersOrDefault (asDescriptionFiles Z) = _
    unfold DescriptionData.filesParametersOrDefault
    exact if_pos live
  obtain ⟨X₀, m, hX, _, hG', hc, _⟩ := thePlan_key Z live
  have hf := (H2K.Sizes.publicO_at_scope scope hX).frame
  rw [hG, hG']
  exact OnBytes.Model.Verify.chainsOf_key_salt_at hc hf

/-- **Strings of 40 bytes have the plan's length**, at every such Z. -/
theorem bytes_forty (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (s : ByteArray) : (fitBytes 40 s).size = saltG (dataAtFiles flashProveData Z).G := by
  rw [saltG_the Z scope live]
  exact size_fitBytes 40 s

end FlashProve
