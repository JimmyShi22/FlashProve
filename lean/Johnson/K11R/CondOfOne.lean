-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfOne.lean: THE KIND K11's OWN SENTENCE (the merge of the claims on the committed
table) WITH ONE FACT LEFT BESIDE THE HEAD: the closed test pendAll. Two theorems: calls and
joinings.

What is said.
  `k11Two_of_pend`: at an opening O: pendAll gives `K11Two` (CondOfTwo.lean): slots by
    `slots_le` (Johnson/Desc/Sound/K11Tests/SlotsInScope.lean): in scope the
    merge has 3570 slots.
  `k11_kind_one`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean) FROM: the head h; the three lists'
    heads; and, at every opening, `pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true`. The premise tm
    of `k11_kind` is drawn from the head by `k11AtRB_at_head`
    (Johnson/Desc/Sound/MgAt/K11MembersAtHead.lean).

Limits. pendAll IS NOT SHOWN HERE: it is a test with code on the public parameters; Lean's kernel
does not carry its closed fact; it has been evaluated true at the stored full-size files, with
negative tests of it that reject there. It is a theorem under the head in KindAtFree.lean,
through a lighter test that is the same Bool. THE HEAD IS THE HEAD WITH THE FOURTEEN ENTRY TESTS:
`pins_of_laid`, on which tm, hc, madeRow, low, laid, start, the six facts on the mask row, the seven
on the letters and the payers of frontWa and weights rest along this chain of files
(CondOfRest.lean to this one), stands over the form of the proof file's entry tests with
fourteen rows, two of which are the comparisons with the written plan; the head's field laid says
that every entry test accepts. A verifier whose entry tests lack these two rows gives no such head.
A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.K11R.CondOfTwo
import Johnson.Desc.Sound.K11Tests.SlotsInScope
import Johnson.Desc.Sound.MgAt.K11MembersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape ceilLog2)
open OnBytes.PscRun (Sized)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)
open Johnson.Desc.First.Walk.Tied (Reach rowsBefore)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open P5J (AtMgA mgAtAll TS F0T Free)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **slots, in scope.** -/
theorem k11Two_of_pend (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hp : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true) : K11Two h Bs :=
  { pendAll := hp
    slots := LT28.K11Tests.slots_le h.scope h.reads h.pubOne O.blank }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM THE HEAD, THE THREE LISTS' HEADS AND ONE
CLOSED TEST.** -/
theorem k11_kind_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_two h 𝔏 q₁ q₂ q₃ (k11AtRB_at_head h.toAtMg) fun Bs base O =>
    k11Two_of_pend h Bs O (K Bs base O)

end K11

#print axioms K11.k11Two_of_pend
#print axioms K11.k11_kind_one
