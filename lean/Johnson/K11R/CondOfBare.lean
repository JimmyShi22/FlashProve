-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfBare.lean: WHAT IS LEFT BENEATH THE CONDITIONS OF THE KIND K11's OWN SENTENCE (the
merge of the claims on the committed table), with the last fact along "reached" laid in: NOTHING
THAT IS LEFT READS A STATE.
One structure, two theorems: joinings.

What is said.
  `K11Bare h Bs xM xI k ni O' m L`: EIGHTEEN NAMED CONDITIONS, NONE OF WHICH READS A STATE: three
    tests with code on the public part (laid, start, madeRow); two closed tests with code (pendAll,
    low); seven facts on the letters (roomLeft, idxSeat, idxShape, idxRows, niIs, ellPow, inM); six
    facts on numbers for the test on the mask row (maskNo, maskLt, maskNum, maskSeat, maskOwn,
    maskBits).
  `k11Last_of_bare`: at an opening O, `K11Bare` gives `K11Last` (CondOfLast.lean): sized340 by
    `sized_at_340` (LeavesPaid.lean).
  `k11_kind_bare`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean), as `k11_kind_last`, with `K11Bare`
    in the place of `K11Last`.

Limits. NO CONDITION IS SHOWN HERE; that the eighteen can be met together is shown nowhere. They
follow from the head along this chain of files; a member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). In front of
the eighteen stand, as in `k11_kind`: the three lists' heads, tm, hc and the head h itself; hc is
drawn from the head in CondOfPub.lean, tm in CondOfOne.lean. What is left here is laid
further in CondOfPub.lean; the whole chain is typed as one in CondOfPend.lean. The head: see
CondOfRest.lean's Limits. Nothing on soundness.

-/
import Johnson.K11R.CondOfLast
import Johnson.K11R.LeavesPaid

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

/-- **WHAT IS LEFT: EIGHTEEN FACTS, NONE OF WHICH READS A STATE.** -/
structure K11Bare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni O' m : ℕ) (L : Laid) : Prop where
  /-- three tests with code on the public part, for the eight facts at 346 -/
  laid : P5J.At.laid? Zp = some L
  start : VerifiableInference.Desc.First.FillP1.startB Zp (msgsOfChain Zp.made.proof.1)
    (P5J.At.N Zp cF).indexNo = true
  madeRow : VerifiableInference.PlanWritten.madeRow Zp = true
  /-- closed tests, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  low : lowAtB h.𝔇.N open346 (treesInFront VerifiableInference.PlanWritten.cutFirstFull 346) = true
  /-- facts on the letters, which read no state -/
  roomLeft : 0 < (P5J.At.foldD Zp cF L).free0 - rowsBefore (P5J.At.foldD Zp cF L).fvs 24
  idxSeat : L.places[h.𝔇.N.indexNo]? = some h.𝔇.N.index
  idxShape : (P5J.At.foldD Zp cF L).M[h.𝔇.N.indexNo]? = some (xI.1.l.get xI.2).1
  idxRows : (xI.1.l.get xI.2).1.maskRows = 2 ^ k
  niIs : 2 ^ (k + (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll) = ni
  ellPow : (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).ell =
    2 ^ (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll
  inM : ∀ j, j < (parOf Zp Bs.G₀).nMsg → InMsg h.𝔇.cs (xM.1.l.get xM.2).1 (posMask 0 j).1
    (posMask 0 j).2.1 (posMask 0 j).2.2
  /-- six facts on numbers, for the test on the mask row -/
  maskNo : maskNoOf (P5J.At.shape Zp) 24 = some m
  maskLt : m < firstCount (P5J.At.shape Zp) 24
  maskNum : O' + (firstCount (P5J.At.shape Zp) 24 + 1) +
    (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
      h.𝔇.N.msgsAt (some mergeAt) + m
  maskSeat : L.places[O']? = some (seatOf xM)
  maskOwn : seatOf xM ∈ h.𝔇.N.group 24
  maskBits : ((P5J.At.foldD Zp cF L).M[O']?).map (fun y => ceilLog2 y.maskRows) = some 0

set_option maxRecDepth 100000 in
/-- **With the last fact along "reached" laid in.** -/
theorem k11Last_of_bare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (xM xI : Mem) (k ni O' m : ℕ) (L : Laid) (Q : K11Bare h Bs xM xI k ni O' m L) :
    K11Last h Bs xM xI k ni O' m L :=
  { laid := Q.laid
    start := Q.start
    madeRow := Q.madeRow
    pendAll := Q.pendAll
    low := Q.low
    roomLeft := Q.roomLeft
    idxSeat := Q.idxSeat
    idxShape := Q.idxShape
    idxRows := Q.idxRows
    niIs := Q.niIs
    ellPow := Q.ellPow
    inM := Q.inM
    maskNo := Q.maskNo
    maskLt := Q.maskLt
    maskNum := Q.maskNum
    maskSeat := Q.maskSeat
    maskOwn := Q.maskOwn
    maskBits := Q.maskBits
    sized340 := sized_at_340 h.scope h.reads O }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM `K11Bare`.** -/
theorem k11_kind_bare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
      ∃ (k ni O' m : ℕ) (L : Laid), K11Bare h Bs xM xI k ni O' m L) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_last h 𝔏 q₁ q₂ q₃ tm hc fun Bs base O xM xI e2 e3 => by
    obtain ⟨k, ni, O', m, L, Q⟩ := K Bs base O xM xI e2 e3
    exact ⟨k, ni, O', m, L, k11Last_of_bare h Bs O xM xI k ni O' m L Q⟩

end K11

#print axioms K11.k11Last_of_bare
#print axioms K11.k11_kind_bare
