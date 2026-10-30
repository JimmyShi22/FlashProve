-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/TieSmallFacts.lean: small facts beside the tie.
`dsF_eq`, `xsF_eq`: the values' rounds and places of the entry are the frame's. `kf_dead`:
  `LPFD.Full.KF`
at the empty data twice is 140, by the kernel. `decodeD_aux`: `decodeD` hands the further tokens on
untouched. `verify_pad_beyond`: in scope, where the family's test says yes and the decoders take the
bytes, at a full window the goals' verify at the built D* gives one answer at any two lists of
further tokens of the vocabulary.

-/
import Johnson.Goal.Tie.TieWhole
import Johnson.Goal.Tie.PadBeyond

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie
open PV.Head (cThru sevenThru)
open Inst.Model

theorem dsF_eq : PV.EntryFive.dsF = dsFull := rfl

theorem xsF_eq : PV.EntryFive.xsF = frD.xs := rfl

/-- What KF says at the empty data twice: by the kernel. -/
theorem kf_dead : LPFD.Full.KF emptyRoundsData emptyRoundsData = 140 := by decide +kernel

/-- decodeD hands the further tokens on untouched. -/
theorem decodeD_aux (c : ByteArray) (B : FormBytes) (a : List Token) (f : DecodedProof) (h : decodeD c
        B = some f) :
    decodeD c { B with aux := a } = some { f with aux := a } := by
  unfold decodeD at h ⊢
  dsimp only at h ⊢
  split at h
  · split at h
    · rename_i x mT mB e1 e2 e3 hok
      obtain rfl := Option.some.inj h
      simp only [hok, if_true]
    · cases h
  · cases h

/-- **VerifierAndGoals.verify at the built D* does not turn with the further tokens at a full window.** -/
theorem verify_pad_beyond (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (live : L.live
                        (asDescriptionFiles Z) = true)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) (f : DecodedProof)
    (hdec : decodeD (cThru O (asDescriptionFiles Z)) B = some f) (a : List Token)
    (hv : (vocabularyTokens B.aux).isSome = true) (hv' : (vocabularyTokens a).isSome = true)
    (h : ppref.T ≤ prompt.length + output.length) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output { B with aux
                                    := a }).evaluate
        (hashOf O) =
      (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
          (hashOf O) := by
  have hfa : f.aux = B.aux := by
    have := decodeD_aux _ B B.aux f hdec
    have e : ({ B with aux := B.aux } : FormBytes) = B := rfl
    rw [e, hdec] at this
    exact (congrArg DecodedProof.aux (Option.some.inj this))
  rw [verify_descriptionOfDataOnBytes L Z scope live O hO h7 commitment prompt output _ _ (decodeD_aux _ B a f
                    hdec),
    verify_descriptionOfDataOnBytes L Z scope live O hO h7 commitment prompt output B f hdec,
    DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof_pad_beyond _ _ hO _ _ commitment prompt output { f with aux := a } hv' h,
    DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof_pad_beyond _ _ hO _ _ commitment prompt output f (by rw [hfa]; exact hv) h]

end FlashProve
