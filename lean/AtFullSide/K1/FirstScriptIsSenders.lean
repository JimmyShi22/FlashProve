-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FirstScriptIsSenders.lean: the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean) is the Script of a senders' record in the form that the first thread's
authors ask (SendersRecord.script, ScriptIsTheSenders, Honest/Thread/TheFirstThread.lean); and K1's laws on
that Script at their first thread.

  1  firstRecord   the record: K1's numbers and data, the cells, the token, K1's reader, the other senders
  2  firstScript_written   the closed Script with its readers and the code switch's data written out
     firstScript_written_head   the same under the head, with the proximity test's share written out too
     firstScript_is_record   under the head at the maker's return: firstScriptAt is that record's Script
  3  scriptIsTheSenders_first   so ScriptIsTheSenders holds of every parts whose script is firstScriptAt
     firstParts, scriptIsTheSenders_parts   the first thread's parts at the closed Script, and the same there
  4  ownTrees_firstThread, k1Seated_firstLetters   ownTrees_first and k1Seated_first at firstThread and
     firstLetters, where parts.script is firstScriptAt

How. Their record lists K1's jobs by the places' numbers (byNo) at the ground seatGround A; ours lists them
by written numbers (k1MembersW) at A.G. Under the head the two grounds are one (seatGround_of_base,
atPure_at_laid_ground) and the two lists are one (byNo_at_head, Honest/Thread/JoinAtHead.lean).

Limits. The head and the maker's return are hypotheses. The other fields of parts stay free. All limits of
FirstScript.lean stand. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type}

/-- **The senders' record at the base prover.** -/
def firstRecord (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) : SendersRecord A ProofFile.Inst where
  number := lotNo OnBytes.secondHashFunction A.Z
  lotData := lotData S
  sendingWData := K13.wDataAt Op.pile
  cells := cellsB I A.Z
  token := tokB
  reader := witB I A.Z
  others := otherSendersAt I S A cF

variable {files : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The closed Script, its parameters written out**: K1's reader and the code switch's readers are the
filling's; the code switch's data are withSwitchData S (lotData S). By unfolding. -/
theorem firstScript_written (cF : Chain TS ProofFile.Cl) :
    firstScriptAt I S Op A cF =
      joinQ cF.blocksInOrder 0 (cellsB I A.Z) tokB (P5J.At.arr A.Z)
        (fun v : LocB W₀ => (⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩ : PlaceIn ProofFile.Inst)) ()
        (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
        ((K2.switchShareAt A.B cF.blocksInOrder 0 A.Z A.G (K2.withSwitchData S (lotData S) A.Z A.G)
          (fun v : LocB W₀ => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) noTree).add
          (testShareAt I S A cF)) :=
  rfl

/-- **The same under the head, the proximity test's share written out too**: the code switch's finish pl is
found, the test's job at it has six stages, and the other senders' record is the sum of the two written
shares. In firstScript_written the second summand is testShareAt, which falls to the empty record where there
is no finish; K1's jobs read the data lotData S and K13.wDataAt Op.pile by their own texts (jobTwoAt, jobLaterAt,
jobWAt, AtFullSide/K1/RecordAtBase.lean). -/
theorem firstScript_written_head {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction files D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    ∃ pl, K12.AtProof.finishAt A.Z A.G = some pl ∧
      (testJobAt I S A.Z A.G pl).p.nums.stages.length = 6 ∧
      firstScriptAt I S Op A cF =
        joinQ cF.blocksInOrder 0 (cellsB I A.Z) tokB (P5J.At.arr A.Z)
          (fun v : LocB W₀ => (⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩ : PlaceIn ProofFile.Inst)) ()
          (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
          ((K2.switchShareAt A.B cF.blocksInOrder 0 A.Z A.G (K2.withSwitchData S (lotData S) A.Z A.G)
            (fun v : LocB W₀ => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) noTree).add
            (K12.k12Share 0 (testJobAt I S A.Z A.G pl) () (roundsTo cF.blocksInOrder 354) 77 (P5J.At.arr A.Z)
              testOk pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0)
              (fun τ => shapeAtSeat A.Z (77 + τ) 1) 354 noTree)) := by
  obtain ⟨pl, hf, e⟩ := otherSenders_at_head (I := I) (S := S) h hA
  refine ⟨pl, hf, testJob_six h pl, ?_⟩
  show scriptAt I S Op A cF (cellsB I A.Z) tokB (otherSendersAt I S A cF) = _
  rw [e]
  rfl

/-- **Under the head at the maker's return, the closed Script is the record's Script.** -/
theorem firstScript_is_record (H : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    firstScriptAt I S Op A H.firstChain =
      SendersRecord.script H (firstRecord I S Op A H.firstChain) := by
  obtain ⟨Bs, base₀, O⟩ := H.head.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground H.head.laid O.blank hA
  have eS : seatGround A = Bs.G₀ := seatGround_of_base O.made
  have key : byNo H.firstChain.blocksInOrder
      (lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z (seatGround A) ++
        OnBytes.SendSim.Seat.wJobs (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt Op.pile) A.Z
          (seatGround A)) =
      k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G) := by
    rw [eS, eG]
    exact byNo_at_head H.head O (lotNo OnBytes.secondHashFunction A.Z) (lotData S) (K13.wDataAt Op.pile)
  exact (congrArg (fun js => joinQ H.firstChain.blocksInOrder 0 (cellsB I A.Z) tokB (P5J.At.arr A.Z)
    (witB I A.Z) () js (otherSendersAt I S A H.firstChain)) key).symm

/-- **The first thread's authors' proposition on the Script holds at the closed Script.** -/
theorem scriptIsTheSenders_first (H : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (parts : FirstThreadParts A) (hp : parts.script = firstScriptAt I S Op A H.firstChain) :
    ScriptIsTheSenders H parts :=
  ⟨ProofFile.Inst, firstRecord I S Op A H.firstChain, hp.trans (firstScript_is_record H hA)⟩

/-- **The first thread's parts at the closed Script.** numbers: the stated numbers of the falls, which no
test reads. -/
def firstParts (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) (numbers : FallNumbers) :
    FirstThreadParts A :=
  ⟨firstScriptAt I S Op A cF, numbers⟩

/-- The proposition at these parts. -/
theorem scriptIsTheSenders_parts (H : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) (numbers : FallNumbers) :
    ScriptIsTheSenders H (firstParts I S Op A H.firstChain numbers) :=
  scriptIsTheSenders_first H hA _ rfl

/-- **K1's trees at the first thread.** -/
theorem ownTrees_firstThread (H : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (parts : FirstThreadParts A) (hp : parts.script = firstScriptAt I S Op A H.firstChain)
    (w : LocB W₀) {y : Nat × SendJob (PlaceIn ProofFile.Inst) Unit}
    (hy : y ∈ k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G)) :
    OwnTrees (firstThread H parts w) y.1 y.2.P.trees.length (treeTbl 0 (witB I A.Z) y.2 ())
      fun _ => 0 := by
  unfold firstThread firstLetters
  rw [hp]
  exact ownTrees_first H.head hA _ _ _ _ _ _ _ _ _ w hy

/-- **K1Seated, all twenty fields, at each of the 52 members, at the first thread's letters.** -/
theorem k1Seated_firstLetters (H : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (parts : FirstThreadParts A) (hp : parts.script = firstScriptAt I S Op A H.firstChain)
    (w : LocB W₀) :
    (∃ blk, K1Seated (firstLetters H parts w) 2 blk (witB I A.Z) (jobTwoAt S A.Z A.G) () .opening
      (P5J.At.arr A.Z) (P5J.At.seats A.Z) (P5J.At.ms A.Z files.lay)
      (K1.radRec 0 (jobTwoAt S A.Z A.G).P)) ∧
    (∀ l, l < 25 → ∀ d : Bool, ∃ blk, K1Seated (firstLetters H parts w) (K1.noL l d) blk
      (witB I A.Z) (jobLaterAt S A.Z A.G l d) () (cond d (.digits l) (.reads l)) (P5J.At.arr A.Z)
      (P5J.At.seats A.Z) (P5J.At.ms A.Z files.lay)
      (K1.radRec (3 * l + (if d then 2 else 1)) (jobLaterAt S A.Z A.G l d).P)) ∧
    (∃ blk, K1Seated (firstLetters H parts w) 356 blk (witB I A.Z) (jobWAt Op A.Z A.G) () .w
      (P5J.At.arr A.Z) (P5J.At.seats A.Z) (P5J.At.ms A.Z files.lay)
      (K1.radRec 81 (jobWAt Op A.Z A.G).P)) := by
  unfold firstLetters
  rw [hp]
  exact k1Seated_first H.head hA _ _ _ _ _ _ _ _ _ w

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.firstRecord
#print axioms ProofFile.Honest.K1.firstScript_written
#print axioms ProofFile.Honest.K1.firstScript_written_head
#print axioms ProofFile.Honest.K1.firstScript_is_record
#print axioms ProofFile.Honest.K1.scriptIsTheSenders_first
#print axioms ProofFile.Honest.K1.scriptIsTheSenders_parts
#print axioms ProofFile.Honest.K1.ownTrees_firstThread
#print axioms ProofFile.Honest.K1.k1Seated_firstLetters
