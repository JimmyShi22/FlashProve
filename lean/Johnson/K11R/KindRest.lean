-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/KindRest.lean: THE KIND K11's OWN SENTENCE (the merge of the claims on the committed
table), FROM WHAT IS LEFT BENEATH ITS CONDITIONS, ENDS IN THE FORM IN WHICH A KIND's LAW IS COUNTED:
`P5J.AtMgA.Kind h 𝔏 K11` (Johnson/P5J/RowsAtAll.lean). One theorem: `k11_kind` (KindAtMg.lean,
frozen: it is not changed) over `k11Cond_of_rest` (CondOfRest.lean).

What is said. `k11_kind_rest`: as `k11_kind`, with `K11Rest` in the place of `K11Cond`: at every
opening, at the member that sits at (73, 2) and the one at the index masks' place, there are k, ni,
free0, O', m, V', fvs, L, M, sh, shW with `K11Rest` at the head's own "reached". That the segment's
message with mask rows has the place (73, 2) is `AtMg.mask_place`
(Johnson/HB/LLHARD/MaskSeatWritten.lean).

Limits. Those of the two files. NO CONDITION IS SHOWN HERE. The head is the head with the fourteen
entry tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which `mask_place` rests,
stands over the form of the proof file's entry tests with fourteen rows, two of which are the
comparisons with the written plan; the head's field laid says that every entry test accepts. A
member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/).
Nothing on soundness.

-/
import Johnson.K11R.KindAtMg
import Johnson.K11R.CondOfRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape)
open OnBytes.Params (ReqShape)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K12.Door (Laid)
open P5J (AtMgA TS F0T Free)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM WHAT IS LEFT BENEATH ITS CONDITIONS.** -/
theorem k11_kind_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (tm : k11AtRB Zp 24 = true)
    (hc : VerifiableInference.PlanWritten.cutOf (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      ∀ (xM xI : Mem),
      xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
      xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI →
      ∃ (k ni free0 O' m V' : ℕ) (fvs : List Bool) (L : Laid) (M : List OracleShape)
        (sh : ReqShape) (shW : OnBytes.Model.WsShape),
        K11Rest (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
          h Bs h.toAtMg.rch xM xI k ni free0 O' m V' fvs L M sh shW) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind h 𝔏 q₁ q₂ q₃ tm hc fun Bs base O pM xM xI e1 e2 e3 => by
    obtain rfl : (73, 2) = pM := Option.some.inj (h.toAtMg.mask_place.symm.trans e1)
    obtain ⟨k, ni, free0, O', m, V', fvs, L, M, sh, shW, Q⟩ := K Bs base O xM xI e2 e3
    have hxM : seatOf xM = (73, 2) := of_decide_eq_true
      (List.find?_some (p := fun y => decide (seatOf y = (73, 2))) e2)
    have hxI : seatOf xI = (P5J.At.N Zp cF).index := of_decide_eq_true
      (List.find?_some (p := fun y => decide (seatOf y = (P5J.At.N Zp cF).index)) e3)
    exact ⟨posMask k, ni, 0, _,
      k11Cond_of_rest h Bs O h.laid.planOk _ (fun _ h' => h'.1) xM xI hxM hxI k ni free0 O' m V' fvs
        L M sh shW Q⟩

end K11

#print axioms K11.k11_kind_rest
