-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfPub.lean: WHAT IS LEFT BENEATH THE KIND K11's OWN SENTENCE (the merge of the claims
on the committed table) WHEN WHAT THE HEAD ITSELF GIVES IS DRAWN FROM IT: the premise hc of
`k11_kind` and the fields madeRow and low fall.
One structure, four theorems: calls and joinings.

What is said.
  `hc_paid`: under the head, the first chain's rows are the written ones: `k11_kind`'s premise hc,
    to the letter: the second half of `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean):
    the proof file's entry tests ask that comparison, and the head's field laid
    says that they accept.
  `low_paid`: under the head, the field low of `K11Cond`: `low_in_scope`
    (Johnson/Desc/Sound/K11Tests/LowInScope.lean), its premise on the first
    pin by `pins_of_laid`, its premise on the laid value by `laidPOf_of`.
  `K11Pub h Bs xM xI k ni O' m L`: SIXTEEN NAMED CONDITIONS, NONE OF WHICH READS A STATE:
    `K11Bare`'s (CondOfBare.lean) without madeRow and low.
  `k11Bare_of_pub` (madeRow by `madeRow_at_head`, Johnson/P5J/AtMgRAtHead.lean);
    `k11_kind_pub`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean) from the three lists' heads,
    tm, and `K11Pub` at every opening: NO hc IN FRONT.

Limits. NO CONDITION OF `K11Pub` IS SHOWN HERE. What is left here is laid further in
CondOfEight.lean; the whole chain is typed as one in CondOfPend.lean. The head is the head
with the fourteen entry tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which hc,
madeRow and low rest, stands over the form of the proof file's entry tests with fourteen rows, two
of which are the comparisons with the written plan; the head's field laid says that every entry test
accepts. A verifier whose entry tests lack these two rows gives no such head. A member of the head
is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on
soundness.

-/
import Johnson.K11R.CondOfBare
import Johnson.Desc.Sound.K11Tests.LowInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.AtMgRAtHead

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

/-- **`k11_kind`'s premise hc, under the head.** -/
theorem hc_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    VerifiableInference.PlanWritten.cutOf (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull :=
  (P5J.pins_of_laid h.scope h.laid).2

set_option maxRecDepth 100000 in
/-- **The field low, under the head.** -/
theorem low_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    lowAtB h.𝔇.N open346 (treesInFront VerifiableInference.PlanWritten.cutFirstFull 346) = true :=
  LT28.K11Tests.low_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks) _ _ _ _ _

/-- **WHAT IS LEFT: SIXTEEN FACTS, NONE OF WHICH READS A STATE.** -/
structure K11Pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni O' m : ℕ) (L : Laid) : Prop where
  /-- two tests with code on the public part, for the eight facts at 346 -/
  laid : P5J.At.laid? Zp = some L
  start : VerifiableInference.Desc.First.FillP1.startB Zp (msgsOfChain Zp.made.proof.1)
    (P5J.At.N Zp cF).indexNo = true
  /-- a closed test, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
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
/-- **With what the head gives drawn from it.** -/
theorem k11Bare_of_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni O' m : ℕ) (L : Laid) (Q : K11Pub h Bs xM xI k ni O' m L) :
    K11Bare h Bs xM xI k ni O' m L :=
  { laid := Q.laid
    start := Q.start
    madeRow := P5J.madeRow_at_head h.toAtMg
    pendAll := Q.pendAll
    low := low_paid h
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
    maskBits := Q.maskBits }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM `K11Pub`, WITH NO hc IN FRONT.** -/
theorem k11_kind_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
      ∃ (k ni O' m : ℕ) (L : Laid), K11Pub h Bs xM xI k ni O' m L) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_bare h 𝔏 q₁ q₂ q₃ tm (hc_paid h) fun Bs base O xM xI e2 e3 => by
    obtain ⟨k, ni, O', m, L, Q⟩ := K Bs base O xM xI e2 e3
    exact ⟨k, ni, O', m, L, k11Bare_of_pub h Bs xM xI k ni O' m L Q⟩

end K11

#print axioms K11.hc_paid
#print axioms K11.low_paid
#print axioms K11.k11Bare_of_pub
#print axioms K11.k11_kind_pub
