-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Description/KeyWritten.lean: in scope, at every function o in the second hash
function's place: either the verifier says no to all, or the data of the key file's seat, and of the
proof file's, are the written data, two closed terms.
`key_written_of_liveAt`, `proof_written_of_liveAt`: in scope, where `protocolDataWellFormedAt o` says yes, the
seat's data at o are the written ones: from `key_row_laid_at`
(Johnson/Goal/Numbers/KeyRowLaid.lean), whose two steps in a row are the key file's seat's own text,
and `LPFD.Full.laidPOf_written` (Johnson/Desc/Laid/ProofFullScope.lean): both hold at every o.
`written_or_no_all`: so, at the name: no at every parser, form and hash function
(`theDescription_dead_all`, DeadParser.lean), or both data are the written ones.
`key_built_written`: where the goals read the description, the letter DK that the verifier reads.
At which o: in scope `publicOfO o` returns only at an o whose digests of the four public tables are
the format's: at every other o the seats refuse, and a law at every o holds there by the verifier's
refusal. One o stands in premise and term: nothing is said across two.
Limits. In scope, at the format's second hash function, no files are known at which `protocolDataWellFormedAt o`
says no; at that function it says yes at the written copies by theorem (AtFullSide/Top/), as bytes
by evaluation alone. Nothing on soundness.

-/
import Johnson.Goal.Description.DeadParser
import Johnson.Goal.Numbers.KeyRowLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **In scope, where `protocolDataWellFormedAt o` says yes, the key file's data are the written data.** -/
theorem key_written_of_liveAt (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormedAt o (asDescriptionFiles Z) = true) :
    theKeyDataAt o (asDescriptionFiles Z) = Johnson.G.writtenKFull := by
  obtain ⟨K, _, _, hK, _, _⟩ := theLiveAt_made o (asDescriptionFiles Z) live
  rw [theKeyDataAt_ok hK]
  rcases VerifiableInference.PlanWritten.key_row_laid_at (o := o) (Z := Z) scope with
    ⟨e, he⟩ | ⟨r, hr⟩
  · exact absurd (he.symm.trans hK) (by simp)
  · exact (congrArg Prod.fst (Except.ok.inj (hr.symm.trans hK))).symm

/-- **The same of the proof file's.** -/
theorem proof_written_of_liveAt (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormedAt o (asDescriptionFiles Z) = true) :
    theProofDataAt o (asDescriptionFiles Z) = Johnson.G.writtenPFull := by
  obtain ⟨_, P, _, _, hP, _⟩ := theLiveAt_made o (asDescriptionFiles Z) live
  obtain ⟨D, r⟩ := P
  rw [theProofDataAt_ok hP]
  exact LPFD.Full.laidPOf_written (o := o) (Z := Z) scope hP

/-- **At the name, in scope, at every o: no to all, or both files' data are the written data.** -/
theorem written_or_no_all (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) :
    (∀ (Form : Type) (parse : Parser (theDescription o) Z Form) (hash : Hash)
        (commitment : Commitment) (prompt output : List Token) (form : Form),
        (VerifierAndGoals.verify (theDescription o) Z parse commitment prompt output form).evaluate hash =
          false) ∨
      (theKeyDataAt o (asDescriptionFiles Z) = Johnson.G.writtenKFull ∧
        theProofDataAt o (asDescriptionFiles Z) = Johnson.G.writtenPFull) := by
  cases hl : protocolDataWellFormedAt o (asDescriptionFiles Z) with
  | false =>
    exact Or.inl fun _ parse hash c p out form =>
      theDescription_dead_all o Z hl parse hash c p out form
  | true =>
    exact Or.inr ⟨key_written_of_liveAt o Z scope hl, proof_written_of_liveAt o Z scope hl⟩

/-- In scope, where `protocolDataWellFormed` says yes, the key file's data that the verifier reads are the written
data. -/
theorem key_built_written (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : (dataAtFiles flashProveData Z).DK = Johnson.G.writtenKFull :=
  (dk_built_live Z live).trans (key_written_of_liveAt OnBytes.secondHashFunction Z scope live)

end FlashProve

#print axioms FlashProve.key_written_of_liveAt
#print axioms FlashProve.proof_written_of_liveAt
#print axioms FlashProve.written_or_no_all
#print axioms FlashProve.key_built_written
