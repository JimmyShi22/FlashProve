-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersAtTheWrittenScript.lean   (in the side library: it imports AtFullSide)

Nothing on hiding. No property of the protocol is claimed. Theorems alone; joinings by calls.

IF "ready" RETURNS, THE FIRST THREAD AT THE WRITTEN FIRST SCRIPT HOLDS AT THE START. No stand is shown here: that "ready" returns is a premise.
The written Script is "firstScriptAt" (AtFullSide/K1/FirstScript.lean). IT STANDS AT THE BASE PROVER: the return A of the maker at the filling
"onlineProverPartsInUse matrixInput secondHashFunction Sz.ref openHonest", with coins of the type IndexCommitterCoins. The online prover of E2E/TheHonestProver.lean is that
filling READ THROUGH "OnlineProverParts.through id (tableCoins files) …": another return, with coins of another type. NOTHING HERE CARRIES THE END TO THAT
RETURN. WHERE IT IS SPENT, by its spender's word: at the base: "AtPublicFiles.Bridge.yesAt_of_base" (E2E/ThruYesBase.lean) and its kin read "ready", the threads
and the yes at the prover that the family reads through; the end's type is the premise a₁ of "threadsC_of" (E2E/DebtsOfThreads.lean), which is
general in the prover.

THE END, "enters_first_chain_at_the_written_script": under a head H at the base return: "ready" returns R; "okStart" accepts; three premises on the code switches (lent, closing, publicOk) and one on public sizes (planesSizes) ⊢ "Enters₁" at
"firstThread H (firstParts …) R.own".
BY CALLS of: "enters_first_chain_over_matrices" (EntersItemsFirstChain.lean) · "requestIsReadBackAtFirstThread"
(EntersRequestAtFirstThread.lean) · "rawOn_at_the_first_script" (EntersSymbolsAtTheWrittenScript.lean) ·
"firstScriptCellsHoldAtMatrixInput", "firstScriptTokenMakesTheRequest" (EntersTokenAndCellsAtTheWrittenScript.lean).
So the written Script meets "ScriptReadsTheInput" at every input that meets "ReadyInput", UNDER the base return, the head and the four premises
named above ("written_script_reads_the_input"). THAT THESE HOLD TOGETHER AT ANY FILES IS NOT SHOWN HERE: so both theorems may still hold emptily.
WHAT STAYS A PREMISE: the base return and the head at it; that "ready" returns; "okStart"; lent, closing, publicOk; planesSizes.
-/
import Johnson.HonestTrace.Joint.EntersItemsFirstChain
import Johnson.HonestTrace.Joint.EntersRequestAtFirstThread
import AtFullSide.HonestTrace.EntersSymbolsAtTheWrittenScript
import AtFullSide.HonestTrace.EntersTokenAndCellsAtTheWrittenScript
import AtFullSide.HonestTrace.EntersAtStoredFiles
import AtFullSide.K1.FirstScriptIsSenders
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.HonestTrace (Sz ServesAt ScriptSymsRawOn theTrace cellOf planeOf)
open Inst.Model (Instance ppref)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt firstParts LocB)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf)
open OnBytes.HonestTrace.EntersAtStoredFiles (baseFilling)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- Its trace is the input's. -/
theorem baseFilling_trace :
    baseFilling.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ := rfl

/-- **The written Script reads the input as "ScriptReadsTheInput" asks**, at every input that meets "ReadyInput". -/
theorem written_script_reads_the_input
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (H : HeadAtReturn files A)
    (lent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (closing : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (publicOk : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB FullSizeMatrix, ReadyInput H.description A.H w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p
        ((K2.segmentsOf A.Z A.G).take p.link) w.x = true)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (Meaning.sizesOf (P5J.At.X A.Z) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (Meaning.sizesOf (P5J.At.X A.Z) link).k number = (Sz.ref.shapeNo link number).2)
    (k : Coins A.B) {v : LocB FullSizeMatrix} (ready : ReadyInput H.description A.H v) :
    ScriptReadsTheInput A.Z (firstScriptAt matrixInput Sz.ref openHonest A H.firstChain) k v :=
  ⟨HonestTraceRun.Enters.firstScriptCellsHoldAtMatrixInput Sz.ref openHonest A H.firstChain v,
    HonestTraceRun.Enters.firstScriptTokenMakesTheRequest matrixInput Sz.ref openHonest A
      H.firstChain v,
    fun _ _ _ _ _ traceIs =>
      OnBytes.HonestTrace.rawOn_at_the_first_script H.head made lent closing publicOk planesSizes k
        ready traceIs⟩

/-- **Three fields of the threads' debts, in their own letters, at the written Script**: "startFit", "requestParses" and "served" of
"ThreadDebts" (AtFullSide/Honest/ThreadsAtTheTerm.lean), their texts written out; that file is not imported. The first is the premise
"accepts" handed through; the second follows from it and the head; the third is "served_and_tied_of_ready" at the written Script. -/
theorem three_thread_debts_at_the_written_script
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (H : HeadAtReturn files A) (numbers : FallNumbers) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst}
    {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w₀ rc ξ k = .ok R)
    (accepts : H.description.okStart ξ = true)
    (lent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (closing : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (publicOk : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB FullSizeMatrix, ReadyInput H.description A.H w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p
        ((K2.segmentsOf A.Z A.G).take p.link) w.x = true)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (Meaning.sizesOf (P5J.At.X A.Z) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (Meaning.sizesOf (P5J.At.X A.Z) link).k number = (Sz.ref.shapeNo link number).2) :
    H.description.okStart ξ = true ∧
      (_root_.Meaning.backReq (H.head.𝔇.reqB ξ.pub)).isSome = true ∧
      ∃ (i : Cm.Idx) (s : Instance ppref), ServesAt (P5J.At.X A.Z) i s ∧
        OnBytes.HonestTrace.ScriptTies files A.Z H.firstChain
          (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers).script k R.own i s := by
  obtain ⟨i, s, -, -, Sv, Ti⟩ := served_and_tied_of_ready baseFilling_trace made H
    (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers) returns accepts
    (written_script_reads_the_input made H lent closing publicOk planesSizes k
      (readyInput_of_ready returns accepts))
  exact ⟨accepts, HonestTraceRun.Enters.requestIsReadBackAtFirstThread accepts, i, s, Sv, Ti⟩

/-- **THE END: the first thread at the written Script holds at the start that "ready" gives, at the base return.** -/
theorem enters_first_chain_at_the_written_script
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (H : HeadAtReturn files A) (numbers : FallNumbers) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst}
    {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w₀ rc ξ k = .ok R)
    (accepts : H.description.okStart ξ = true)
    (lent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (closing : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (publicOk : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB FullSizeMatrix, ReadyInput H.description A.H w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p
        ((K2.segmentsOf A.Z A.G).take p.link) w.x = true)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (Meaning.sizesOf (P5J.At.X A.Z) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (Meaning.sizesOf (P5J.At.X A.Z) link).k number = (Sz.ref.shapeNo link number).2) :
    Enters₁ H.description A.H
      (firstThread H (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers) R.own) w₀ rc
      ξ k R :=
  enters_first_chain_over_matrices baseFilling_trace made H
    (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers) returns accepts
    (HonestTraceRun.Enters.requestIsReadBackAtFirstThread accepts)
    (written_script_reads_the_input made H lent closing publicOk planesSizes k
      (readyInput_of_ready returns accepts))

end HonestTraceRun.Meets

#check @HonestTraceRun.Meets.enters_first_chain_at_the_written_script
#print axioms HonestTraceRun.Meets.baseFilling_trace
#print axioms HonestTraceRun.Meets.written_script_reads_the_input
#print axioms HonestTraceRun.Meets.three_thread_debts_at_the_written_script
#print axioms HonestTraceRun.Meets.enters_first_chain_at_the_written_script
