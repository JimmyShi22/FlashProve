-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtHeadTwo.lean: OVER THE PROOF FILE'S ENTRY TESTS (lawsAsk): THE
SHARE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE SECOND HASH FUNCTION ITSELF, UNDER THE HEAD
AtMgA, AtMgR AND TWO NAMED FIELDS: five of the seven that Law/K06AtHeadSeven.lean leaves, and
its pin, are paid here, by calls.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  seven_at_head: K6LeftSeven at the closed term from "the listed seats are Lp" and K6LeftTwo.
  cond_at_head_two, k06_kind_head_two: Law/K06AtHeadSeven.lean's cond_at_head_seven and
      k06_kind_head_seven with K6LeftTwo in the place of K6LeftSeven and the pin.

BY CALLS OF. NO PIN: book: book_at_const (Law/BookAtConst.lean: by the make of the
numbers) with its atRow_told · namedC: namedC_at_head
(Johnson/HB/LLHARD/K6NamedAtHead.lean: from the head's own field on the seats' names). OVER THE
PINS: fenceT: P5J.LaidAt.fence (Johnson/P5T/CoreAtMg.lean) · numbers:
P5J.numbers_at_head (Johnson/HB/LLHARD/K6NumbersAtName.lean) · seatsC:
seatsC_at_head (Johnson/HB/LLHARD/K6SeatsAtHead.lean, over seatsK6C_in_scope), whose
two premises are AtMgR's field listed and Law/K6ReadsNameAtConst.lean's reads_name_at_const · the
pin itself: the first half of P5J.pins_of_laid
(Johnson/Goal/Skeleton/PinsOfLaid.lean).
THE GROUND. pins_of_laid STANDS OVER THE PROOF FILE'S ENTRY TESTS (Desc/Laid/ProofAsks.lean:
lawsAsk), OF WHICH IT SPENDS AT LEAST THE ROWS madeRow AND cutRow (they compare the plan with
written values), AND COMPILES OVER NO LIST THAT LACKS THEM: so does this file. Whether a value is
laid at any public files under these tests is shown by none of them.
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ · AtMgR (six of its facts on every reached state are spent, at
border 341, and its field listed) · K6LeftTwo: callsC, maskC (tests with code on public data: the
lookup on the head's calls sits as the table has it; the mask row's message meets the table's).
ON callsC: where the layout names no array for a matrix its test says yes. Under the head no matrix
of segment 24 takes that branch: the head's field laid (Meaning.laidThere) says no there.
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing at another function in the second
hash function's place. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtHeadSeven
import Johnson.Desc.Kinds.Law.K6LeftTwo
import Johnson.Desc.Kinds.Law.K6ReadsNameAtConst
import Johnson.Desc.Kinds.Law.BookAtConst
import Johnson.HB.LLHARD.K6NamedAtHead
import Johnson.HB.LLHARD.K6SeatsAtHead
import Johnson.HB.LLHARD.K6NumbersAtName
import Johnson.P5T.CoreAtMg

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

/-- **The seven, from the two.** -/
theorem seven_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x) (Lp : K12.Door.Laid)
    (hLp : P5J.At.laid? Zp = some Lp)
    (L2 : K6LeftTwo (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x) :
    K6LeftSeven (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x Lp (K12.Door.msgsOfChain
        Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub))) :=
  seven_of_two (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x Lp (K12.Door.msgsOfChain
      Zp.made.proof.1) _
    (seatsC_at_head h Lp hLp (reads_name_at_const h))
    (by rw [atRow_told]; exact book_at_const h) (h.laid.fence h.scope) (P5J.numbers_at_head h)
    (namedC_at_head h) L2

/-- **THE ONE CONDITION, AT THE HEAD, FROM THE TWO.** -/
theorem cond_at_head_two (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a)
    (Lp : K12.Door.Laid) (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (L2 : K6LeftTwo (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x) :
    ∃ Lk : Link S Claim, K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_at_head_seven h L q₁ q₂ q₃ Rch hRch Lp hF (P5J.pins_of_laid h.scope h.laid).1
    (seven_at_head h Lp hF.listed L2)

/-- **The kind's share at bare "reached", from the two.** -/
theorem k06_kind_head_two (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF
      (RchAt (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
      (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) (fun a
                      => a.1) Lp)
    (L2 : K6LeftTwo (dAt h) (P5J.At.layout Zp) (P5J.At.num Zp) x) :
    h.toAtMg.Kind (dAt h) L .K6 :=
  k06_kind_head_seven h L q₁ q₂ q₃ Lp hF (P5J.pins_of_laid h.scope h.laid).1
    (seven_at_head h Lp hF.listed L2)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seven_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_two
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_head_two
