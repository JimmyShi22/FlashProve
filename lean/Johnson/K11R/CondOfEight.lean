-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfEight.lean: WHAT IS LEFT BENEATH THE KIND K11's OWN SENTENCE (the merge of the
claims on the committed table) when laid, start and the six facts on numbers for the test on the
mask row are drawn from the head too. One structure, two theorems: calls and joinings. The frozen
K11/LawAtMg.lean and K11/KindAtMg.lean do not turn.

What is said.
  `K11Eight h Bs xM xI k ni`: EIGHT NAMED CONDITIONS, NONE OF WHICH READS A STATE: one closed test
    with code (pendAll) and seven facts on the letters (roomLeft, idxSeat, idxShape, idxRows, niIs,
    ellPow, inM), at L := the written layout `LFull` (Johnson/HB/LLHARD/LaidWritten.lean).
  `k11Pub_of_eight`: at an opening O and the member xM that `xAt` finds at (73, 2): `K11Eight` gives
    `K11Pub` (K11/CondOfPub.lean) at O' := 181, m := 0, L := `LFull`: laid by `laid_in_scope`
    (Johnson/HB/LLHARD/PlanInScope.lean); start by `startB_at_head` (Johnson/P5J/StartAtHead.lean);
    maskNo, maskLt, maskBits, maskSeat, maskOwn by the theorems of those names in
    Johnson/Desc/Sound/K11Tests/MaskSixInScope.lean; maskNum by `maskNum_at_cut`
    (K11Tests/ToldAtCut.lean) at `hc_paid`; their premises on the first pin
    and on the laid value out of the head's field laid.
  `k11_kind_eight`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean) from the three lists' heads, tm, and
    `K11Eight` at every opening.

Limits. NO CONDITION OF `K11Eight` IS SHOWN HERE. What is left here is laid further in
K11/CondOfTwo.lean; the whole chain is typed as one in K11/CondOfPend.lean. The head is the head
with the fourteen entry tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which what
falls here rests (maskOwn is handed the laid value too, by `laidPOf_of`), stands over the form of
the proof file's entry tests with fourteen rows, two of which are the comparisons with the written
plan; the head's field laid says that every entry test accepts. A verifier whose entry tests lack
these two rows gives no such head. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.K11R.CondOfPub
import Johnson.Desc.Sound.K11Tests.ToldAtCut
import Johnson.HB.LLHARD.PlanInScope
import Johnson.P5J.StartAtHead

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

/-- **WHAT IS LEFT: EIGHT FACTS, NONE OF WHICH READS A STATE.** -/
structure K11Eight (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni : ℕ) : Prop where
  /-- a closed test, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  /-- facts on the letters, which read no state -/
  roomLeft : 0 < (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull).free0 -
    rowsBefore (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull).fvs 24
  idxSeat : VerifiableInference.Desc.K13.Law.LFull.places[h.𝔇.N.indexNo]? = some h.𝔇.N.index
  idxShape : (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull).M[h.𝔇.N.indexNo]? =
    some (xI.1.l.get xI.2).1
  idxRows : (xI.1.l.get xI.2).1.maskRows = 2 ^ k
  niIs : 2 ^ (k + (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll) = ni
  ellPow : (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).ell =
    2 ^ (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll
  inM : ∀ j, j < (parOf Zp Bs.G₀).nMsg → InMsg h.𝔇.cs (xM.1.l.get xM.2).1 (posMask 0 j).1
    (posMask 0 j).2.1 (posMask 0 j).2.2

set_option maxRecDepth 100000 in
/-- **With laid, start and the six on the mask row drawn from the head.** -/
theorem k11Pub_of_eight (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (xM xI : Mem) (hxM : xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM) (k ni : ℕ)
    (Q : K11Eight h Bs xM xI k ni) :
    K11Pub h Bs xM xI k ni 181 0 VerifiableInference.Desc.K13.Law.LFull :=
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hl := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  { laid := VerifiableInference.Desc.K13.Law.laid_in_scope h.scope h.laid.pub hy
    start := P5J.startB_at_head h.toAtMg
    pendAll := Q.pendAll
    roomLeft := Q.roomLeft
    idxSeat := Q.idxSeat
    idxShape := Q.idxShape
    idxRows := Q.idxRows
    niIs := Q.niIs
    ellPow := Q.ellPow
    inM := Q.inM
    maskNo := LT28.K11Tests.maskNo_in_scope h.scope h.laid.pub hy
    maskLt := LT28.K11Tests.maskLt_in_scope h.scope h.laid.pub hy
    maskNum := LT28.K11Tests.maskNum_at_cut h.scope h.laid.pub hy (congrArg (·.shape) O.first) _
      (hc_paid h)
    maskSeat := LT28.K11Tests.maskSeat_at hxM
    maskOwn := LT28.K11Tests.maskOwn_in_scope h.scope h.laid.pub hy hl hxM _ _ _ _ _
    maskBits := LT28.K11Tests.maskBits_in_scope h.scope h.laid.pub hy }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM `K11Eight`.** -/
theorem k11_kind_eight (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (tm : k11AtRB Zp 24 = true)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      ∀ (xM xI : Mem),
      xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
      xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI →
      ∃ (k ni : ℕ), K11Eight h Bs xM xI k ni) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_pub h 𝔏 q₁ q₂ q₃ tm fun Bs base O xM xI e2 e3 => by
    obtain ⟨k, ni, Q⟩ := K Bs base O xM xI e2 e3
    exact ⟨k, ni, 181, 0, _, k11Pub_of_eight h Bs O xM xI e2 k ni Q⟩

end K11

#print axioms K11.k11Pub_of_eight
#print axioms K11.k11_kind_eight
