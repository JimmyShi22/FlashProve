-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SpellsId.lean: at the description's own told structure: the hash function's answer
at the code of a key whose told part is the public files' digest is the format's commitment ID:
`SpellsId Z hash` (Johnson/Bind/Cpp/Spells.lean), at every Z and every hash function, with no
premise. By `digest_encF` (Johnson/Bind/Cpp/SpellsIdCode.lean), `T₀_fields`
(Johnson/Goal/Conditions/BindsPlain.lean) and `layoutsByPublicReading_total` (Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean): every
key of these types has a code, so no bound on a key is left.
Limits. An equation between two Lean texts, both made of the same functions of Fmt/. It holds
together the call's number, the order of the parts, the six numbers of the shape, and that no key
lacks a code. The spellings of the OOD seed and the OOD answers are the same terms on both sides:
nothing is said of them here. Z enters through the files' digest alone (`digest_encF` has the same
at every digest). At the full-size shape: the six numbers are constants on both sides, on the left
`OnBytes.Params.recordLink.table`, on the right the numerals of `nameAt` (`name_is` holds the two
together), whatever Z's own files say of the table or of the salts' length. Nothing on a
commitment's properties or on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Spells
import Johnson.Bind.Cpp.SpellsIdCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open _root_.Iop (Dig)

/-- Every key has a code under the told structure's code. -/
theorem total_T₀ (Z : PublicFiles) (key : Dig 256 × TypedOracleCompiler.Compile.Batch.Cms.KeyRoot 256 (R₀ Z).protocol) :
    (T₀ Z).encT key ≠ none := layoutsByPublicReading_total (dataAtFiles flashProveData Z) allZeroDigest [] key

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] PV.EncId.encF T₀ OnBytes.K.IdTable.spellAns
  OnBytes.K.IdTable.spellSeed Fmt.publishedIDW Fmt.tableName Fmt.HM

/-- **THE ANSWER AT THE KEY'S CODE IS THE FORMAT'S COMMITMENT ID**, at every Z and hash function. -/
theorem spellsId (Z : PublicFiles) (hash : Hash) : SpellsId Z hash := by
  intro root rcd
  have ht := total_T₀ Z (hash (configString Z), ⟨root, rcd⟩)
  unfold ZKCP.digestUnder
  rw [(T₀_fields Z).2.2] at ht ⊢
  exact digest_encF hash (hash (configString Z)) root rcd ht

end Bind.Cpp

#print axioms Bind.Cpp.total_T₀
#print axioms Bind.Cpp.spellsId
