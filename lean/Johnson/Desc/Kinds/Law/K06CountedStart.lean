-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06CountedStart.lean: OVER THE PROOF FILE'S ENTRY TESTS (lawsAsk):
THE KIND K6 IN THE FORM IN WHICH A KIND'S LAW IS COUNTED (P5J.AtMgA.Kind h L K6:
Johnson/P5J/RowsAtAll.lean), UNDER THE HEAD AtMgA AND TWO NAMED TESTS ON PUBLIC DATA: startB AND
callsC. A joining of two calls.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  k6Cond_of_start: the named condition for this kind (P5J.AtMgA.K6Cond h L, in
      Johnson/Goal/Skeleton/Kinds/K6Bridge.lean: K06AtConst.lean's
      K6Cond under "there are", at "reached, at a typed instance's public part, and no mark") holds.
  k06_counted_start: h.Kind L K6.

BY CALLS OF Law/K06AtHeadStart.lean's cond_at_head_start at the fence h.rchU (in
Johnson/Goal/Skeleton/Kinds/Unmarked.lean) and of P5J.k06_kind_all.
THE GROUND: as Law/K06AtHeadTwo.lean's: of the entry tests lawsAsk at least madeRow and cutRow.
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ · startB · callsC.
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtHeadStart
import Johnson.Goal.Skeleton.Kinds.K6Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **The named condition P5J.AtMgA.K6Cond (K6Bridge.lean) holds.** -/
theorem k6Cond_of_start (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hs : First.FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.K6Cond L := by
  obtain ⟨Lp, Lk, C⟩ := cond_at_head_start h L q₁ q₂ q₃ h.rchU (fun _ _ hr => hr.1.1) hs callsC
  exact ⟨4, Lk, Lp, _, C⟩

/-- **THE KIND, IN THE COUNTED FORM.** -/
theorem k06_counted_start (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hs : First.FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.Kind L KindName.K6 :=
  P5J.k06_kind_all h L q₁ q₂ q₃ (k6Cond_of_start h L q₁ q₂ q₃ hs callsC)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6Cond_of_start
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_start
