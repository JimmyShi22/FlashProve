-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfPend.lean: THE CHAIN OF FILES FROM CondOfRest.lean TO CondOfOne.lean, TYPED
AS ONE: the frozen conditions of the kind K11's own sentence (the merge of the claims on the
committed table), `K11Cond` (LawAtMg.lean), from the head and the one closed test pendAll. Two
theorems: joinings.

What is said.
  `k11Cond_of_pend`: at the head h, an opening O, and the members that `xAt` finds at (73, 2) and at
    the index masks' place: `pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true` gives `K11Cond` at the
    head's own "reached", at posI := `posMask 0`, ni := 256, R := 0 and Wa := `WaSeat …` at the
    public parameters' own size of the vocabulary. Nine calls, a link each.
  `k11CondAll_of_pend`: pendAll at every opening gives `P5J.AtMgA.K11Cond h 𝔏`
    (Johnson/Goal/Skeleton/Kinds/K11Bridge.lean): the form in which the
    join of the kinds takes K11's premises: its first two conjuncts by `k11AtRB_at_head`
    and `hc_paid`.

Limits. pendAll IS NOT SHOWN HERE: it is a test with code on the public parameters; Lean's kernel
does not carry its closed fact; it has been evaluated true at the stored full-size files, and three
negative tests of it have rejected there. It is a theorem under the head in KindAtFree.lean,
through a lighter test that is the same Bool. THE HEAD IS THE HEAD WITH THE FOURTEEN ENTRY TESTS
(see CondOfOne.lean's Limits). A member of the head is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.K11R.CondOfOne
import Johnson.Goal.Skeleton.Kinds.K11Bridge

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

open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaSeat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **THE FROZEN CONDITIONS, FROM THE HEAD AND ONE CLOSED TEST.** -/
theorem k11Cond_of_pend (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (xM xI : Mem) (hxM : xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM)
    (hxI : xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI)
    (hp : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true) :
    K11Cond (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h Bs h.toAtMg.rch xM xI (posMask 0) 256 0
      (WaSeat h.𝔇.arr h.𝔇.N (P5J.At.X Zp) (P5J.At.num Zp 24 0) 0 (P5J.At.X Zp).P.h.V) := by
  have Q2 := k11Two_of_pend h Bs O hp
  have Q8 := k11Eight_of_two h Bs xM xI hxM hxI Q2
  have Qp := k11Pub_of_eight h Bs O xM xI hxM 0 256 Q8
  have Qb := k11Bare_of_pub h Bs xM xI 0 256 181 0 _ Qp
  have Ql := k11Last_of_bare h Bs O xM xI 0 256 181 0 _ Qb
  have Qf := k11Few_of_last h Bs O xM xI 0 256 181 0 _ Ql
  obtain ⟨shW, Qc⟩ := k11Closed_of_few h Bs xM xI 0 256 181 0 _ _ Qf
  have Qr := k11Rest_of_closed h Bs xM xI 0 256 181 0 _ _ shW Qc
  have sM : seatOf xM = (73, 2) := of_decide_eq_true
    (List.find?_some (p := fun y => decide (seatOf y = (73, 2))) hxM)
  have sI : seatOf xI = (P5J.At.N Zp cF).index := of_decide_eq_true
    (List.find?_some (p := fun y => decide (seatOf y = (P5J.At.N Zp cF).index)) hxI)
  exact k11Cond_of_rest h Bs O h.laid.planOk _ (fun _ h' => h'.1) xM xI sM sI 0 256 _ 181 0 _ _ _ _
    _ shW Qr

set_option maxRecDepth 100000 in
/-- **The form in which the join of the kinds takes K11's premises.** -/
theorem k11CondAll_of_pend (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true) :
    h.K11Cond 𝔏 :=
  ⟨k11AtRB_at_head h.toAtMg, hc_paid h, fun Bs base O pM xM xI e1 e2 e3 => by
    obtain rfl : (73, 2) = pM := Option.some.inj (h.toAtMg.mask_place.symm.trans e1)
    exact ⟨posMask 0, 256, 0, _, k11Cond_of_pend h Bs O xM xI e2 e3 (K Bs base O)⟩⟩

end K11

#print axioms K11.k11Cond_of_pend
#print axioms K11.k11CondAll_of_pend
