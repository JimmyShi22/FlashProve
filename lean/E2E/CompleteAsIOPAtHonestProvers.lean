-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtHonestProvers.lean: the last line, TheProverIsCompleteAsIOP
(E2E/CompleteAsIOPAtTheTerm.lean), from the named statements of HonDebts at honestProvers' own seats.
It states no goal.

  CompleteInParts.refuseUnserved   the parts carry to the same provers under refuseUnserved, since
    every clause is at pairs of the relation, and these are served.
  parts_at_honestProvers   the parts at honestProvers, from HonDebts where the maker returns and the
    offline description is named, at sides G whose provers are the return's,
    as a hypothesis hG.
  theProver_of_debts   the last line.

Limits. HonDebts and hG are hypotheses, and that the maker returns and the offline description is
named: no value is shown to meet them. The numbers pT, zB, z, pF are letters: that they add up to
at most the target is hypothesis hsum.
-/
import E2E.CompleteAsIOPAtTheTerm
import E2E.CompleteAsIOPFromDebts

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Prob
open _root_.Iop

variable {Index Instance : Type} {L : HolographicProtocol Index Instance}

/-- **The parts carry to the provers under refuseUnserved.** -/
theorem CompleteInParts.refuseUnserved {prover : HonestProvers L} {work : PartsWork L}
    {copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool} {Relation Served : Index → Instance → Prop}
    {offlineError linkError onlineError : ℝ≥0∞}
    (h : CompleteInParts L prover work copyNumberIn Relation offlineError linkError onlineError)
    (hs : ∀ i x, Relation i x → Served i x) :
    CompleteInParts L (prover.refuseUnserved Served) work copyNumberIn Relation offlineError
      linkError onlineError where
  offlineAccepted := h.offlineAccepted
  linkAccepted := h.linkAccepted
  onlineAccepted := fun i x r e n hy => by
    have hb := h.onlineAccepted i x r e n hy
    unfold FailsRarely at hb ⊢
    refine le_trans (pr_mono _ ?_) hb
    rintro ⟨c, ρ⟩ hf
    rcases hf with hw | hr
    · refine Or.inl ?_
      rcases hw with hw | hn | hh
      · exact Or.inl hw
      · exact absurd (hs i x hy) hn
      · exact Or.inr hh
    · exact Or.inr hr
  sendsCopyNumber := h.sendsCopyNumber

end VerifiableInference.Compilation

namespace AtPublicFiles.AtFiles.HonestTerm
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (ProverCoinCounts Sides)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne)
open OnBytes.Prover (ofRecs)
open VerifiableInference.Compilation (CompleteInParts)
open P5J

local instance (priority := high) nonemptyPadZ_atHonestProvers : Nonempty PadZ := pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_atHonestProvers : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atHonestProvers : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (P : Parts Z) (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (description : OfflineDescription)

/-- The offline prover at its description. -/
abbrev offlineAt :=
  offlineProverWithEncodedTable Z (keyFileDescription description.source description.numbers description.later) P.book
    (P.prover description) runValueBytes runValueBytes (offlineStart description)

/-- **The parts at honestProvers, from the named statements.** -/
theorem parts_at_honestProvers (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H) {Relation : FullSizeMatrix → XF → Prop}
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {pT zB z pF : ℝ≥0∞}
    (hf : (workAtFiles Z).Faithful)
    (d : HonDebts allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description) Relation FT
      (fun _ _ => ∅) 0 pT zB z pF) :
    CompleteInParts (protocolAtFiles Z) (ofRecs (honestProvers Z P)) (workAtFiles Z) (copyNumberAtFiles Z)
      Relation pT 0 (zB + z + pF) := by
  have hk : offlineProver P = offlineAt P description := by simp only [offlineProver, hD]
  have hfam : famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H = onlineProverAt returned places firstChain := by
    rw [famG_eq, hG]
    rfl
  have hr : onlineProver Z =
      famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H := by
    rw [hfam]
    simp only [onlineProver, hM, hP, hC]
  have e : honestProvers Z P = proversOf (offlineAt P description) (linkProverAtFiles committerCoinCountLessOne Z)
      (famG Z returned.Z places firstChain runValueBytes runValueBytes returned.B G returned.H) := by
    simp only [honestProvers, hk, hr]
  rw [e]
  exact parts_of_debts committerCoinCountLessOne Z returned.Z places firstChain runValueBytes runValueBytes
    returned.B G returned.H (keyFileDescription description.source description.numbers description.later)
    P.book (P.prover description) runValueBytes runValueBytes (offlineStart description) hf d

/-- **The last line, from the named statements.** -/
theorem theProver_of_debts {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hM : onlineMaker Z = .ok returned)
    (hP : H2U.placesOfMade returned.Z.made = .ok places)
    (hC : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain)
    (hD : offlineDescription Z = .ok description)
    (G : Sides (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey _ _ _)
    (hG : G.prover returned.H = returned.H)
    {FT : AtPublicFiles.KeyBridge.FallT (offlineAt P description)} {pT zB z pF : ℝ≥0∞}
    (hsum : pT + 0 + (zB + z + pF) ≤ completenessTarget)
    (hf : (workAtFiles Z).Faithful)
    (d : HonDebts allZeroDigest [] Z returned.Z places firstChain runValueBytes runValueBytes returned.B G
      returned.H (keyFileDescription description.source description.numbers description.later) P.book
      (P.prover description) runValueBytes runValueBytes (offlineStart description)
      (ServedRequest committerCoinCountLessOne Z hr) FT (fun _ _ => ∅) 0 pT zB z pF) :
    TheProverIsCompleteAsIOP Z P hr := fun _ _ =>
  ⟨hf, pT, 0, zB + z + pF, hsum,
    (parts_at_honestProvers P returned places firstChain description hM hP hC hD G hG hf
      d).refuseUnserved fun _ _ h => h⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.parts_at_honestProvers
#print axioms AtPublicFiles.AtFiles.HonestTerm.theProver_of_debts
