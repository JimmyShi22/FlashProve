-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06CountedHead.lean: THE KIND K6 IN THE FORM IN WHICH A KIND'S LAW IS COUNTED
(P5J.AtMgA.Kind h L K6), UNDER THE HEAD AtMgA. Main names: cond_at_head_none: there are Lp, Lk with
Law/K06AtConst.lean's K6Cond: GENERAL IN "REACHED" above bare RchAt · k6Cond_of_head: the named
condition for this kind (P5J.AtMgA.K6Cond h L) holds · k06_counted_head: h.Kind L K6. The one test
that Law/K06CountedCalls.lean leaves, callsC, is paid here, BY A CALL OF callsC_at_head_all
(Johnson/HB/LLHARD/K6CallsAtHeadAll.lean: its text at written values by the kernel, off the pins;
and, for the eight names that the built segment 24's list of arrays bears, names_tie_head_all,
Johnson/Desc/AtSeats/NamesTieHeadStream.lean). THE GROUND: as Law/K06AtHeadTwo.lean's: over the
proof file's entry tests (Desc/Laid/ProofAsks.lean: lawsAsk), of which its payers spend at least the
rows madeRow and cutRow (Goal/Skeleton/PinsOfLaid.lean); AND at least these fields of the head,
asked by no entry test: plan.named, laid, fit, groups, shape · opts.laid · headAt. WHAT IS LEFT IN
FRONT: the head h · q₁ q₂ q₃: L's three lists are the IOP's own. What it does not say. THAT THERE IS
A HEAD: NO EXAMPLE. NO STATE IS SHOWN BY A THEOREM AT WHICH THE PROMISE, "REACHED" AND "NO MARK"
HOLD TOGETHER AT THIS PLACE: FIVE OF THE SEVEN TIES (Desc/Sound/ChainOfPromisesR.lean: TiedAtR) MAY
HOLD IDLY. THE WEIGHTS' RANGE COSTS THIS LAW NOTHING: its guard InRange (Law/K6CutGuarded.lean: the
witness's cells hold an index) is met by the decoder's make (Law/DecInRange.lean), not by a test
that the proof file's verifier runs at this place; that the decoder answers is not said. At theta =
C, cap = T the policy admits any tokens of the request; Desc/Kinds/Head.lean's statement keeps (c)
even so. Nothing at another function for the second hash function. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06CountedCalls
import Johnson.HB.LLHARD.K6CallsAtHeadAll

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

/-- **K6Cond (Law/K06AtConst.lean), at the head.** -/
theorem cond_at_head_none (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hR : ∀ k a, Rch k a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) k a) :
    ∃ (Lp : K12.Door.Laid) (Lk : Link S Claim), K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_at_head_one h L q₁ q₂ q₃ Rch hR (callsC_at_head_all h)

/-- **The named condition P5J.AtMgA.K6Cond (Johnson/Goal/Skeleton/Kinds/K6Bridge.lean) holds.** -/
theorem k6Cond_of_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    h.K6Cond L :=
  k6Cond_of_calls h L q₁ q₂ q₃ (callsC_at_head_all h)

/-- **THE KIND, IN THE COUNTED FORM, FROM THE HEAD.** -/
theorem k06_counted_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    h.Kind L KindName.K6 :=
  k06_counted_calls h L q₁ q₂ q₃ (callsC_at_head_all h)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_none
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6Cond_of_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_head
