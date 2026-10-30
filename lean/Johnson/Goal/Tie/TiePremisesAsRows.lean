-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/TiePremisesAsRows.lean: the tie's premises as rows with code.
`tieRows`: five named tests: the files are in the goals' scope; the family's test, handed in as a
Bool; O answers the first public string with 32 bytes; it answers the seven further strings with 32
bytes each; the decoders take the bytes. `tiePremB`: all five. `verify_of_tiePrem`: where it says
yes, the goals' verify at the built D* is `DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof` (DescriptionOfData.lean). `verify_out_of_scope`: out
of scope it is false.
Limit. The second row is what the caller hands in: it is to be computed as `L.live` at the files.

-/
import Johnson.Goal.Tie.DescriptionOfDataRefuse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Maker OnBytes.Tie
open PV.Head (cThru sevenThru)

/-- The five premises, by name. -/
def tieRows (live : Bool) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes) : List (String ×
            Bool) :=
  [("tie 1: the public files are in the goals' scope (VerifierAndGoals.InScope)", InScope Z),
    ("tie 2: the family's test on numbers at these public files (Lay.live; its yes gives tAt's \
        three tests on the data)", live),
    ("tie 3: O's answer at the first public string has 32 bytes", decide ((cThru O (asDescriptionFiles
        Z)).size = 32)),
    ("tie 4: so have its answers at the seven further public strings",
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).all fun b => decide (b.size =
                                32)),
    ("tie 5: the three decoders take the five parsed files, and every judged row in front says yes \
        (decodeD)",
      (decodeD (cThru O (asDescriptionFiles Z)) B).isSome)]

/-- As one test. -/
def tiePremB (live : Bool) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes) : Bool :=
  (tieRows live Z O B).all (·.2)

/-- **Where the test says yes, the goals' verify at the built D* is `DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof`.** -/
theorem verify_of_tiePrem (L : DescriptionData) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (h : tiePremB (L.live (asDescriptionFiles Z)) Z O B = true) (commitment : Commitment) (prompt output :
                   List Token) :
    ∃ (live : L.live (asDescriptionFiles Z) = true) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
      (f : DecodedProof), decodeD (cThru O (asDescriptionFiles Z)) B = some f ∧
      (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
          (hashOf O) =
        (dataAtFilesFromRounds L (asDescriptionFiles Z) (L.G (asDescriptionFiles Z)) (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z))
            (L.hlive
            _ live)).innerCompiledVerifierAnswerOnDecodedProof
          (cThru O (asDescriptionFiles Z)) hO
          (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (hashOf O) commitment prompt
              output f := by
  unfold tiePremB tieRows at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨scope, fit, hO, h7, hd⟩ := h
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hd
  exact ⟨fit, hO, f, hf, verify_descriptionOfDataOnBytes L Z scope fit O hO h7 commitment prompt output B f hf⟩

/-- Out of the goals' scope it says no. -/
theorem verify_out_of_scope (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = false) (hash :
                        VerifiableInference.Hash)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        hash = false :=
  verify_evaluate_out (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) scope hash commitment prompt output
      B

end FlashProve
