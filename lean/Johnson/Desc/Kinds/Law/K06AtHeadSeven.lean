-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtHeadSeven.lean: THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE
SECOND HASH FUNCTION ITSELF, UNDER THE HEAD AtMgA (P5J/MgAtAll.lean), AtMgR (P5J/AtMgR.lean), ONE
NAMED PIN AND SEVEN NAMED FIELDS: two of the nine that Law/K06AtHead.lean leaves are paid here, by
calls.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  tok_at_head: the field tokSmall: at every state reached at border 341 without a mark, what is
      heard as the reply is an entry of the vocabulary.
  left_at_head: K6LeftMg at the closed term from the pin and K6LeftSeven.
  cond_at_head_seven, k06_kind_head_seven: Law/K06AtHead.lean's cond_at_head and k06_kind_head with
      K6LeftSeven and the pin in K6LeftMg's place.

BY CALLS OF: K6's file Johnson/P4R/K6TokAtRchAt.lean (tokSmall_rchAt)
with fd_is · Law/K6PlanCAtHead.lean (planC_at_head: under hy).
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ · AtMgR (six of its facts on every reached state are spent, at
border 341) · hy : madePinnedAt ... = true (a test with code on the public part: the planner's
record is the written one) · K6LeftSeven: seatsC, namedC, callsC, maskC, book, fenceT (tests with
code on public data) · numbers (two equations on public numbers).
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing at another function for the second
hash function. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtHead
import Johnson.Desc.Kinds.Law.K6LeftSeven
import Johnson.Desc.Kinds.Law.K6PlanCAtHead
import Johnson.P4R.K6TokAtRchAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifiableInference.PlanWritten (madePinnedAt)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **The field tokSmall, without the table's promise in front.** -/
theorem tok_at_head {Str : Type} (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a →
      a.1.2.failed = none → TokSmall (P5J.At.X Zp).hS.V a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P4.tokSmall_rchAt h.scope h.reads O h.pubOne

/-- **What is left, from the pin and the seven.** -/
theorem left_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) (Fr : Sound.Frame)
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a)
    (Lp : K12.Door.Laid) (Mm : List OracleShape) (bs : List (Block (ProofFile.InstPub × S) Claim))
    (L7 : K6LeftSeven (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x Lp Mm bs) :
    K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp) Fr x Rch Lp Mm bs :=
  left_of_seven (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp) Fr x Rch Lp Mm bs
    (planC_at_head h hy) (fun a _ hr hm => tok_at_head h a (hRch a hr) hm) L7

/-- **THE ONE CONDITION, AT THE HEAD, FROM THE PIN AND THE SEVEN.** -/
theorem cond_at_head_seven (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a)
    (Lp : K12.Door.Laid) (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (L7 : K6LeftSeven (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x Lp (K12.Door.msgsOfChain
        Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    ∃ Lk : Link S Claim, K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_at_head h L q₁ q₂ q₃ Rch hRch Lp hF
    (left_at_head h hy
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) Rch hRch Lp _ _ L7)

/-- **The kind's share at bare "reached", from the pin and the seven.** -/
theorem k06_kind_head_seven (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF
      (RchAt (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
      (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) (fun a
                      => a.1) Lp)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (L7 : K6LeftSeven (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x Lp (K12.Door.msgsOfChain
        Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    h.toAtMg.Kind (dAt h) L .K6 := by
  obtain ⟨Lk, C⟩ := cond_at_head_seven h L q₁ q₂ q₃ _ (fun _ hr => hr) Lp hF hy L7
  exact k06_kind h L 4 Lk Lp _ C

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tok_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.left_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_seven
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_head_seven
