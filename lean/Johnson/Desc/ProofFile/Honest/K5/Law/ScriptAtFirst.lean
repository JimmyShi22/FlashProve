-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ScriptAtFirst.lean: conditional: what the attention sub-protocol
(K5) asks of the first thread's Script holds at the first chain's Script at the base prover
(firstScriptAt, AtFullSide/K1/FirstScript.lean), at the reference sizes, with the index's reader a
letter. No definition; one theorem.

  k5ScriptQ_at_firstScript   K5ScriptQ at firstScriptAt, at each group below 12

The premises, all of them: h, the head at the return; made, the maker returns A at the filling;
traceIsFull, at each input that meets ReadyInput the trace's cells are the integer model's; hg, the
group is below 12. Under "for all a x₁" in its end: a is the plan of group g, and x₁ the place that
lookAt finds at segment 2 g + 1.

How. k5ScriptQ_at_joinQ_fit (AtFullSide/K5/TieAtJoinTop.lean) at joinFit_first and switch_in_first;
hv by hv_at_head, which spends the first clause of ReadyInput; the opening's job is the first member
of K1's list; the reader is K1's by its text.

Limits.
  * Conditional: traceIsFull is a premise here. K5ScriptQ speaks of the inputs that meet ReadyInput
    alone: where no input does it says nothing.
  * The base filling at IndexCommitterCoins, the first chain alone, the full size alone.
  * Nothing here says that the prover's sides play the Script's texts.
  * eMask says nothing where the book lends K5's row no coins.
  * NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.K5.TieAtJoinTop
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc.First.Look (lookAt)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K1 (firstScriptAt cellsB tokB witB readersB noTree joinFit_first switch_in_first
  mem_k1MembersW mem_k1Members)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **K5ScriptQ at the first chain's Script at the base prover, at each group below 12.**
Conditional: every premise stands, by name, in the file's head. -/
theorem k5ScriptQ_at_firstScript (h : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (traceIsFull : TraceIsFull (P5J.At.X A.Z) (ReadyInput h.description A.H) (id : Cells → Cells))
    {g : Nat} (hg : g < 12) :
    ∀ a x₁, (P5J.At.X A.Z).A[g]? = some a →
      lookAt (P5J.At.X A.Z) (2 * g + 1) false = some x₁ →
      K5ScriptQ h.head (firstScriptAt I Sz.ref Op A h.firstChain) (ReadyInput h.description A.H)
        (roundsTo h.firstChain.blocksInOrder (borderOf g)) x₁ a id
        (seatOf keyOfK3 A.Z A.G h.firstChain g a) (OnBytes.Model.Forest.elems a.fs) := by
  obtain ⟨-, hG, -⟩ := atPure_ok made
  exact AtFullSide.K5.k5ScriptQ_at_joinQ_fit (wt := I.weights A.Z) (rest := noTree) h.head
    (cellsB I A.Z) tokB planesAtRef_ref hg made traceIsFull
    (joinFit_first h.head made) switch_in_first
    (fun _ hp _ => hv_at_head h.head hG A.H hp)
    (mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl)))) (fun _ => rfl)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5ScriptQ_at_firstScript
