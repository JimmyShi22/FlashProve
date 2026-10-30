-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunAnswersAt.lean: THE NAMED PREMISE `RunAnswers` (Honest/K9/BackAt.lean: "the run's
own reader answers at the stand's state", at the head's five entries) PAID AT THE FRAME's OWN THREAD AT THE LIBRARY's
HEAD, by one call of the frame's `head_hrun` (Honest/Law/Rule/HeadHrun.lean). A statement and its proof; no goal is
stated.
  **`runAnswers_at_head`**   at T := the thread of `lettersHead …`, b := the number of the head's batching in the
      head's own table, L the head's own link at 24: `RunAnswers T b pw`, at every pw
The stand's pair gives the thread (its first half); the five entries lie in the head's order and none is
"K8.equations": by evaluation.
WHAT IS NOT CLAIMED. That a stand is there. `ItemBack` at the frame's thread (Honest/K9/BackAt.lean's `itemBack_head`
wants the library's `HeadTake` beside this). No member: called by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.BackAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.HeadHrun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Chain Strs Place Link Claim)
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The named premise at the frame's own thread.** -/
theorem runAnswers_at_head {L : Link TS Claim} (hlk : h.𝔇.lk 24 = some L) (pw : K9.Where) :
    RunAnswers (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.fullLinks P5J.At.ps 24) pw (L := L) := by
  intro κ s m En ds y cols s' x' z G St o ho
  refine head_hrun h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w St.thr.1 hlk o ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.runAnswers_at_head
