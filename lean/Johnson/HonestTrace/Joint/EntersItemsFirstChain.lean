-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersItemsFirstChain.lean

Nothing on hiding. No property of the protocol is claimed. Theorems alone.

THE FIRST THREAD HOLDS AT THE START THAT "ready" GIVES, AT A PROVER OVER THE MATRICES. "enters_firstThread"
(Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean) takes a served request and the Script's ties to it ("ServesAt", "ScriptTies").
Here, at a return of the maker at any filling over the matrices whose trace is "fullIn"'s read through the index that the matrix holds
(coins and own states are letters: EntersItemsOverMatrices.lean): where "ready" returns R and the description's first test accepts
the instance, both are had from "ScriptReadsTheInput" at R's input: the index is one that the input's
matrix holds, the request is what the input's bytes are read as.

* "served_and_tied_of_ready": ready returns, okStart accepts, the Script reads the input ⊢ ∃ i served: the input's matrix holds i, the input's
  bytes are read as served, ServesAt, ScriptTies.
* "enters_first_chain_over_matrices": so "Enters₁" at the first thread.

Limits. NO SCRIPT IS SHOWN TO MEET "ScriptReadsTheInput": parts.script is a field of a letter: both theorems may hold emptily.
(At the base return the written first Script is shown to meet it, under premises:
AtFullSide/HonestTrace/EntersAtTheWrittenScript.lean.) That
"ready" returns, that "okStart" accepts and the parse of the request's bytes are premises. The limits of the files called
come with them.
Not claimed: that a part plays; that a verifier accepts.
-/
import Johnson.HonestTrace.Joint.EntersItemsOverMatrices
import Johnson.Desc.ProofFile.Honest.Thread.EntersFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.HonestTrace (ServesAt ScriptTies)
open Inst.Model (Instance ppref)
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles.Flat (indexOf Holds)

variable {files : VerifierAndGoals.PublicFiles} {Rc X₀ X : Type} {P : OnlineProverParts FullSizeMatrix Rc Cells X₀ X}
  {returned : OnlineProverWithDescription FullSizeMatrix Rc Cells X₀ X}

/-- **A served request and the Script's ties to it, where "ready" returns.** -/
theorem served_and_tied_of_ready (traceField : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned)
    (h : HeadAtReturn files returned) (parts : FirstThreadParts returned) {w₀ : FullSizeMatrix}
    {rc : Rc} {ξ : ProofFile.Inst} {k : Coins returned.B}
    {R : Ready FullSizeMatrix Rc ProofFile.Inst OnBytes.TableKey Cells X₀ X}
    (returns : ready h.description returned.B returned.H w₀ rc ξ k = .ok R)
    (accepts : h.description.okStart ξ = true)
    (reads : ScriptReadsTheInput returned.Z parts.script k R.own) :
    ∃ (i : Cm.Idx) (served : Instance ppref), Holds R.own.w₀ i ∧ ProofFile.instOf R.own.x = some served ∧
      ServesAt (P5J.At.X returned.Z) i served ∧
      ScriptTies files returned.Z h.firstChain parts.script k R.own i served :=
  scriptTies_of_readyInput h.head traceField made (readyInput_of_ready returns accepts) reads

/-- **The first thread holds at the start that "ready" gives.** -/
theorem enters_first_chain_over_matrices (traceField : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok returned)
    (h : HeadAtReturn files returned) (parts : FirstThreadParts returned) {w₀ : FullSizeMatrix}
    {rc : Rc} {ξ : ProofFile.Inst} {k : Coins returned.B}
    {R : Ready FullSizeMatrix Rc ProofFile.Inst OnBytes.TableKey Cells X₀ X}
    (returns : ready h.description returned.B returned.H w₀ rc ξ k = .ok R)
    (accepts : h.description.okStart ξ = true)
    (parses : (_root_.Meaning.backReq (h.head.𝔇.reqB ξ.pub)).isSome = true)
    (reads : ScriptReadsTheInput returned.Z parts.script k R.own) :
    Enters₁ h.description returned.H (firstThread h parts R.own) w₀ rc ξ k R := by
  obtain ⟨i, served, -, -, Sv, Ti⟩ :=
    served_and_tied_of_ready traceField made h parts returns accepts reads
  exact enters_firstThread returns accepts parses Sv Ti

end HonestTraceRun.Meets

#check @HonestTraceRun.Meets.enters_first_chain_over_matrices
#print axioms HonestTraceRun.Meets.served_and_tied_of_ready
#print axioms HonestTraceRun.Meets.enters_first_chain_over_matrices
