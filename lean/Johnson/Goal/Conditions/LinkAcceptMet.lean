-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file states no goal.
Johnson/Goal/Conditions/LinkAcceptMet.lean: THE TWO PREMISES OF link_accLaw
(Johnson/Prover/Link/LinkAccept.lean) ARE MET TOGETHER AT THE INPUT homeR b Z: at two OOD samples
and two encodings of one index. One statement, with its proof.

  accept_met_home   Meant, and "every stored symbol carries its position", at every Z, every index
                    and all seeds: no premise

By: meant_home (Johnson/Goal/Conditions/LinkMeant.lean) · enc_pos
(Johnson/Goal/Conditions/LinkFitsPaid.lean).
Limits. It shows that link_accLaw's two premises can be met together, and where. Nothing on the
decision. Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Goal.Conditions.LinkMeant
import Johnson.Prover.Link.LinkYesStm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run.PQ (SgX)
open _root_.Iop (twoExternalStrings)
open Johnson.Prover.Link (Meant)

/- Lean compares these by their names. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

theorem accept_met_home (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (q q' : (homeR b Z).protocol.EncodingRandomness)
    (e e' : (homeR b Z).protocol.OutOfDomainSeed) :
    Meant ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
        ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
          (tailWords frS q.2))
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q'.1)))
          (tailWords frS q'.2)) ∧
      ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
        ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
          (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).1 = x := by
  have m := meant_home b Z i q q' e e' _ _ rfl rfl
  refine ⟨⟨m.1, m.2.1, m.2.2.1, m.2.2.2.1, m.2.2.2.2.1, m.2.2.2.2.2.1, m.2.2.2.2.2.2⟩, ?_⟩
  intro w x h
  cases w
  · exact enc_pos b Z i q ⟨x, h⟩
  · exact enc_pos b Z i q' ⟨x, h⟩

end FlashProve

#print axioms FlashProve.accept_met_home
