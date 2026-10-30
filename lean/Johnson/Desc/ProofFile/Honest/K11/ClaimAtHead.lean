-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimAtHead.lean: the proofs of `HeardLaidOfWa`, `HeadClaimOfWa`
and `HeadClaimReached` (Honest/K11/ClaimAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How: calls. That a hearing is laid: `WaK6`'s first clause is a yes of the output head's own block,
which the library writes out (`Came.decide_record`, Johnson/Desc/Kinds/Law/RowPromise.lean): it lays
the hearing; its fourth clause keeps it (`KeptWFo`, Johnson/Desc/Kinds/Law/WeightAtFo.lean). The
second: two more clauses of `WaK6`, then the core (`headClaimOfRun`, ClaimOfQuiet.lean of this
folder). The third: the library has `WaK6` at every state reached at 346 (`P4.waK6_rchAt`,
Johnson/P4R/WaK6AtRchAt.lean), called as `K11.k11Few_of_last`'s field waK6 calls its like
(Johnson/K11R/CondOfLast.lean). The request's words: at a reached state without a mark they are the
instance's (the field reqIs of `P5J.foldFacts_at_head'`, Johnson/P5J/FoldJ3Whole.lean), and the
request has passed the first state's test (`Meaning.K2.reqOk_of_noMark`, Johnson/IMR/AtReach.lean),
so the first state bears them too.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimOfQuiet
import Johnson.P4R.WaK6AtRchAt
import Johnson.IMR.AtReach
import Johnson.K11R.CondOfEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc.First (Here)
open VerifiableInference.Desc.K13.Law (LFull laid_in_scope)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open P5J (F0T)

/-- **What the head heard is laid.** -/
theorem heardLaidOfWa : HeardLaidOfWa := by
  intro W V' s hW
  obtain ⟨_, _, _, _, _, _, hd, _, _, hk, _, _, _⟩ := hW
  obtain ⟨a, F1, X0, Q, _, _, _, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.decide_record _ _ _ _ hd
  obtain ⟨o, o', ho, ho', ex, _⟩ := hk
  rw [e] at ho
  obtain rfl := Here.head.inj ho
  exact ⟨o', X0, ho', ex⟩

/-- **At the library's condition on the state in front of the merge.** -/
theorem headClaimOfWa : HeadClaimOfWa := by
  intro H Z G x heard s o claim hW ho hoc hreq hy hties
  obtain ⟨o₂, hx, ho₂, hox⟩ := heardLaidOfWa _ _ _ hW
  obtain rfl : o₂ = o := Here.head.inj (ho₂.symm.trans ho)
  obtain ⟨_, _, _, _, cov, t', _, _, _, _, hcov, hcl, _⟩ := hW
  obtain ⟨k1, k2, k3, k4⟩ := hties o₂ hx ho hox
  exact headClaimOfRun H Z G x heard s cov hx t' claim hcov (hcl o₂ hx claim ho hox hoc) hreq hy
    k1 k2 k3 k4

set_option maxRecDepth 100000 in
/-- **At every state without a mark that is reached at border 346.** -/
theorem headClaimReached : HeadClaimReached := by
  intro H Z D r Zp Np cF xP Bs Str y x heard s o claim h hB hr hf ho hoc hy hties
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have hW := P4.waK6_rchAt h.scope h.reads O h.laid.planOk ((x.pub, s), y) hr hf
  have hq := Meaning.K2.reqOk_of_noMark h.scope h.reads O (rchAt_raw hr) hf
  have hstart : (startS Zp x.pub).req = Verify.words32 x.pub.request := by
    unfold startS
    dsimp only
    rw [if_pos hq]
    rfl
  have hp := (P5J.pins_of_laid h.scope h.laid).1
  have FF := P5J.foldFacts_at_head' h.toAtMg (Str := Str)
    (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) (fun _ _ ha => ha)
    (L := LFull) (laid_in_scope h.scope h.laid.pub hp) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have hreq : s.req = Verify.words32 x.pub.request := FF.reqIs 346 ((x.pub, s), y) hr hf
  exact headClaimOfWa H Zp Bs'.G₀ x heard s o claim hW ho hoc (hreq.trans hstart.symm) hy hties

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.heardLaidOfWa
#print axioms ProofFile.Honest.K11.headClaimOfWa
#print axioms ProofFile.Honest.K11.headClaimReached
