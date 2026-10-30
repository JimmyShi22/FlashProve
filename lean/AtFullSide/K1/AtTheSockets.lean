-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/AtTheSockets.lean: what the shared sending (kind K1), its Script and its head hand to the one object
(AtFullSide/Honest/TheOneObject.lean, TheSockets; AtFullSide/Honest/ThreadsAtTheTerm.lean, ThreadFields), in these
structures' own letters.

  1  wholeRun_of_sockets   the two fields publicData and shapesToEnd give RunsAll 0 358 startShA c
  2  k1_five_at_sockets    K1's share of owes₁, yes₁ and carry₁: FiveAtBorderJ at every place of the kind, at threadOne,
                           saidOne, shapesAtFirst and the falls firstFalls
  3  fix₁_at_sockets       the field fix₁, at theFirstParts
  4  rootedSides_at_sockets   the field rootedSides
  5  seat_at_head          a value for the field seat: under the head the seat makes a base

theFirstParts (TheOneObject.lean) and shapesAtFirst (ThreadsAtTheTerm.lean) are abbreviations; they are written out here, so
that this file imports neither: ⟨firstScriptAt matrixInput Sz.ref openHonest A h.firstChain, numbers⟩ and
shapeJ (firstZA (Tab.g A.Z base.G₀) (Tab.vals A.Z base.G₀)) startShA. threadOne and saidOne are TheThreeThreads.lean's.

2 is k1_fiveJ_of_run (FiveOfWholeRun.lean) at w := R.own, Said := saidOne, fall := fallsBy (firstFalls A numbers) …; the
ground of J is base.G₀ by seatGround_of_base. 3 is treesFixed_first (FirstScriptFixed.lean). 4 is sides_are_whole
(Honest/K1/Pay/Whole.lean). owesS_of_fiveJ (Honest/Thread/FiveAtBorder.lean) gathers 2 with the other kinds' like.

Limits.
  * made, seat, publicData and shapesToEnd are hypotheses: fields of TheSockets.
  * 2 pays at the 52 members of the kind K1 alone. owes₁, yes₁ and carry₁ ask all 358.
  * Those of FiveOfWholeRun.lean: each field stands under the thread's invariant in front of the member; accepted and next
    are asked with J in hand; at an input that does not meet the thread's valid all six fields are idle.
  * At the base prover.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.K1.FiveOfWholeRun
import AtFullSide.K1.FirstScriptFixed
import Johnson.Desc.ProofFile.Honest.K1.Pay.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open VerifiableInference.Desc (KindName)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The sockets' two fields on the run on shapes, as one closed statement. -/
theorem wholeRun_of_sockets {X₀ : OnBytes.Model.Verify.Public} {c : ShA}
    (publicData : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol
      VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (shapesToEnd : (shapeL (LWn X₀)).run 358 startShA = .ok c) : RunsAll 0 358 startShA c :=
  runsAll_of_ex ⟨X₀, publicData, (run_is_from _ _ _).symm.trans shapesToEnd⟩

/-- **K1's share of owes₁, yes₁ and carry₁.** -/
theorem k1_five_at_sockets (h : HeadAtReturn files A) (numbers : FallNumbers)
    {base : ProofFile.PureBase} {X₀ : OnBytes.Model.Verify.Public} {c : ShA}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (seat : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base)
    (publicData : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol
      VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (shapesToEnd : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ
        (threadOne h (⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain,
          numbers⟩ : FirstThreadParts A) R)
        (saidOne h (⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain,
          numbers⟩ : FirstThreadParts A) R)
        (shapeJ (firstZA (Tab.g A.Z base.G₀) (Tab.vals A.Z base.G₀)) startShA)
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b := by
  intro b p hb hk
  have H := ProofFile.Honest.K1.k1_fiveJ_of_run (wholeRun_of_sockets publicData shapesToEnd) made h
    (⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain,
          numbers⟩ : FirstThreadParts A) rfl R.own
    (saidOne h (⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain,
          numbers⟩ : FirstThreadParts A) R)
    (fun _ _ _ a => a.1.1) (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b p hb hk
  rw [seatGround_of_base seat] at H
  exact H

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The field fix₁.** -/
theorem fix₁_at_sockets (h : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A) :
    ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      (ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A
        h.firstChain).fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b :=
  ProofFile.Honest.K1.treesFixed_first h.head made

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The field rootedSides.** -/
theorem rootedSides_at_sockets (h : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A) :
    rootedAll h.description A.H = true := by
  have hr := (ProofFile.Honest.K1.Pay.sides_are_whole (I := matrixInput)
    (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) rfl h.head made).2.1
  have e := (atPure_at_laid h.head.laid made).2
  have hr' : rootedAll (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain) A.H = true := by
    rw [← e]
    exact hr
  exact hr'

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **A value for the field seat.** -/
theorem seat_at_head (h : HeadAtReturn files A) :
    ∃ base, ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  exact ⟨Bs, hB⟩

end AtFullSide.Honest

#print axioms AtFullSide.Honest.wholeRun_of_sockets
#print axioms AtFullSide.Honest.k1_five_at_sockets
#print axioms AtFullSide.Honest.fix₁_at_sockets
#print axioms AtFullSide.Honest.rootedSides_at_sockets
#print axioms AtFullSide.Honest.seat_at_head
