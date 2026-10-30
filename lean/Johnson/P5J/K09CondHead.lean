-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09CondHead.lean: ON THE SECOND ROAD: THE BATCHING KIND's NAMED CONDITION AT THE CLOSED
CONSTANT (`AtMgA.K9Cond`, K09Kind.lean) FROM THE HEAD `AtMgA` AND THE TOWER's THREE EQUATIONS: the
road of K09EndC.lean, stopped one step short of its end, for whoever spends the condition itself
(the ties of the frame's sub-protocol behind the batching come out of it: `k09_behindTies`,
K09Behind.lean). One theorem.

What is said.
  `k09_cond_of_head`: **`h.K9Cond 𝔏` from the head `AtMgA` at the second hash function and the
    tower's own three equations on the flat lists' heads: no other premise.** By `k9Cond_of_laws`
    (K09Seat.lean), `list_hlen` (K09Len.lean), `k9Laws_of_listC`, `k9ListC_of_rest`,
    `k9RestC_of_sorts`, `k9SortsC_of_left`, `k9LeftC_of_last`, `k9LastC_at_head`.

Limits. BOOK-KEEPING: the road of `k09_kind_of_head` unrolled, stopped one step short of its end.
«From the head» means: from all the fields of `AtMgA` (Johnson/P5J/MgAtAll.lean), not from the entry
tests alone; that a head exists is not said here. The theorem is an implication. AT THE SECOND HASH
FUNCTION AND THE FULL SIZE ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09EndC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9Asks (funs_layers funs_att funs_head)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (batchAt onTR frontAt kx_of_table ledger_at_front
  part_at_batch_all K9Closed K9OwnL K9OwnA K9OwnH PosPlan OkCoreLess core_layers_front
  core_att_front core_head_front NumbersOk hmS_at digHeard_of_leftOn leftOn_digits_front
  leftOn_digits_head ledgerB_of_sized merge_clause_347 entsMerge_at_347 OkCore OkLayers OkAtt
  OkHead pi8)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.K14.Law (seatZ secondAt)

open VerifiableInference.Desc.First.Att.P (parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf workOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF

/-- **THE NAMED CONDITION, FROM THE HEAD `AtMgA` AND THE THREE EQUATIONS.** -/
theorem k09_cond_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.K9Cond 𝔏 :=
  k9Cond_of_laws h 𝔏 q₁ q₂ q₃ (list_hlen h.toAtMg 𝔏 q₁ q₂ q₃)
    (k9Laws_of_listC h 𝔏 (k9ListC_of_rest h 𝔏 q₁ q₂ q₃ (k9RestC_of_sorts h 𝔏
      (k9SortsC_of_left h 𝔏 q₁ q₂ q₃ (k9LeftC_of_last h 𝔏 (k9LastC_at_head h 𝔏))))))

end P5J

#print axioms P5J.k09_cond_of_head
