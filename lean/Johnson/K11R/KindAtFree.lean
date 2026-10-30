-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/KindAtFree.lean: THE KIND K11's SHARE (the merge of the claims on the committed table) AT
THE HEAD's OWN VALUE OF THE TOWER's LETTERS, FROM THE HEAD ALONE: `h.Kind h.free K11`: the form in
which `owedAll_of_free` (Johnson/P5J/FreeAll.lean) takes a kind. Four
theorems: calls.

What is said.
  `pendAll_paid`: at the head h and an opening O: `pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true`:
    the last closed test of the chain of files CondOfRest.lean to CondOfPend.lean. It is
    `pendAll_in_scope` (Johnson/Desc/Sound/K11Tests/PendAllInScope.lean);
    its premise on the first pin by `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean); the
    ground by the opening's own field blank.
  `k11_kind_head`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean) from the head and the three lists'
    heads: `k11_kind_one` (CondOfOne.lean) at `pendAll_paid`.
  **`k11_kind_free`**: `h.Kind h.free K11`, WITH NO PREMISE BUT THE HEAD h: the three lists' heads
    are `free_q₁`, `free_q₂`, `free_q₃` (Johnson/P5J/FreeAll.lean).
  `k11CondAll_free`: `P5J.AtMgA.K11Cond h h.free` (Johnson/Goal/Skeleton/Kinds/K11Bridge.lean),
    with no premise but the head.

Limits. THE HEAD IS THE HEAD WITH THE FOURTEEN ENTRY TESTS: `pins_of_laid`, on which most of what
the chain draws from the head rests (see CondOfOne.lean's Limits), stands over the form of the
proof file's entry tests with fourteen rows, two of which are the comparisons with the written plan;
the head's field laid says that every entry test accepts. A member of the head is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). Conditions along the chain are laws from
accepts: idle where nothing is reached (see
Johnson/K11R/LeavesAt346.lean's Limits). A kind's law in the counted form is no soundness of the
verifier. Nothing on soundness.

-/
import Johnson.K11R.CondOfPend
import Johnson.Desc.Sound.K11Tests.PendAllInScope
import Johnson.P5J.FreeAll

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

/-- **The last closed test, under the head.** -/
theorem pendAll_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) :
    pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true :=
  LT28.K11Tests.pendAll_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1 O.blank

/-- The kind K11's share from the head and the three lists' heads. -/
theorem k11_kind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_one h 𝔏 q₁ q₂ q₃ fun Bs _ O => pendAll_paid h Bs O

/-- **THE KIND K11's SHARE AT THE HEAD's OWN VALUE, FROM THE HEAD ALONE.** -/
theorem k11_kind_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.Kind h.free KindName.K11 :=
  k11_kind_head h h.free h.free_q₁ h.free_q₂ h.free_q₃

/-- The form in which the join of the kinds takes K11's premises, at that value: from the head
alone. -/
theorem k11CondAll_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.K11Cond h.free :=
  k11CondAll_of_pend h h.free fun Bs _ O => pendAll_paid h Bs O

end K11

#print axioms K11.pendAll_paid
#print axioms K11.k11_kind_head
#print axioms K11.k11_kind_free
#print axioms K11.k11CondAll_free
