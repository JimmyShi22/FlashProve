-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AttThirdVector.lean: THE PREMISE hU OF THE TWO ATTENTION CLAUSES
"entsFirst" AND "entsSecond" (EntsAtt.lean, PlainOfPromise.lean) IS A THEOREM AT EVERY STATE REACHED
IN FRONT OF AN ATTENTION SEGMENT's BATCHING: the fixed structure names, for the third vector, the
very array that the segment's numbers `parCOf a` name. In the goals' scope. Statements and proofs:
calls.

The road. What is fixed reads the state's structure through a planned reading (`posRead`,
PosAtBatch.lean; `planned_batch_rch`): so its ix.U is the built segment's; the built
segment's structure is the plan's (`IM.ground_tails`, Johnson/IMR/K8Seat.lean); the plan's ix.U is
#[none, none, some 0, none] and its iU3 is 0 (`ofPlan_U`, `ofPlan_u3_tree`, at
`public_ofPlan`: Johnson/Desc/First/Att/Claims/OfPlan.lean).

  `att_plan_U`: g < 12 ⊢ there are the plan a at g and the built segment Xl at 2 g + 1, with
    Xl.tl.ix.U.getD 2 none = some (parCOf a).iU3.
  `hU_att`: **reached (`RchAt`) at 14 (2 g + 1) + 9; a the plan at g ⊢ ∀ tlb, (π (fixed9 φ
    a'.1.2).1).1 = some tlb → tlb.ix.U.getD 2 none = some (parCOf a).iU3.**
Limits. The other premises of the two clauses stay as they were. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.PosAtBatch
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.SeatC
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (parCOf)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open Johnson.Desc.First.Walk.Tied (RchAt)
open K5Law
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The plan's and the built segment's word on the third vector's array. -/
theorem att_plan_U (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ a Xl, Bs.G₀.W.A[g]? = some a ∧ Bs.G₀.built[2 * g + 1]? = some Xl ∧
      Xl.tl.ix.U.getD 2 none = some (parCOf a).iU3 := by
  obtain ⟨_, a, _, Xl, _, ha, _, _, _, _, _, _, hX, ht, _⟩ :=
    (IM.ground_tails hS hR O.pub O.blank).1 g hg
  have hO : OfPlan a := public_ofPlan (IM.ground_publicK O.pub O.blank) g a ha
  refine ⟨a, Xl, ha, hX, ?_⟩
  rw [ht, ofPlan_U hO]
  show some 0 = some a.iU3
  rw [(ofPlan_u3_tree hO).1]

/-- **hU.** -/
theorem hU_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) {Str : Type}
    (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (2 * g + 1) + 9) x)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    ∀ tlb, (π (fixed9 φ x.1.2).1).1 = some tlb →
      tlb.ix.U.getD 2 none = some (parCOf a).iU3 := by
  obtain ⟨a', Xl, ha', hX, hU⟩ := att_plan_U hS hR O hg
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  have hr := of_readTl (planned_batch_rch planned_pos hS hR O hx hX x h)
  intro tlb e1
  have e1' : x.1.2.tl?.map (blank u) = some tlb := (congrArg Prod.fst (hπ x.1.2)).symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  have e : posRead (blank u tl) = posRead Xl.tl := (posRead_blank u tl).trans (hr tl htl)
  have eU : (blank u tl).ix.U = Xl.tl.ix.U := congrArg (·.2.2) e
  rw [eU]
  exact hU

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.att_plan_U
#print axioms VerifiableInference.Desc.LinkJoin.hU_att
