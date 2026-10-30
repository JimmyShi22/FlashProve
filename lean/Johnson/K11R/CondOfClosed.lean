-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfClosed.lean: WHAT IS LEFT BENEATH THE CONDITIONS OF THE KIND K11's OWN SENTENCE (the
merge of the claims on the committed table),
with the eight facts along "reached" at 346 laid in.
One structure, two theorems: joinings.

What is said.
  `K11Closed h Bs xM xI k ni O' m V' L shW`: TWENTY-SEVEN NAMED CONDITIONS. TWENTY-FIVE READ NO
    STATE: the twenty-two of `K11Rest` (K11/CondOfRest.lean), at the closed term's own letters (M,
    free0, fvs := `At.foldD Zp cF L`'s; sh := `At.shape Zp`), and three tests with code on the
    public part, which the eight facts' payer asks (laid, start, madeRow). TWO ARE FACTS ALONG
    "REACHED": waK6, at 346, at the head's own "reached"; sized340, at 340.
  `k11Rest_of_closed`: `K11Closed` gives `K11Rest` at the head's own "reached" and these letters:
    its eight facts at 346 by `eight_at346` (K11/EightAt346.lean).
  `k11_kind_closed`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean), as `k11_kind_rest`
    (K11/KindRest.lean), with `K11Closed` in the place of `K11Rest`.

Limits. NO CONDITION IS SHOWN HERE; that they can be met together is shown nowhere. They follow from
the head along this chain of files; a member of the head is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). What is left here is
laid further in K11/CondOfFew.lean (the seven facts for "weights") and K11/CondOfPub.lean (madeRow);
the whole chain is typed as one in K11/CondOfPend.lean. The head: see K11/CondOfRest.lean's Limits.
Nothing on soundness.

-/
import Johnson.K11R.KindRest
import Johnson.K11R.EightAt346

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

/-- **WHAT IS LEFT, WITH THE EIGHT FACTS AT 346 LAID IN**: twenty-five facts that read no state; two
along "reached". -/
structure K11Closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni O' m V' : ℕ) (L : Laid) (shW : OnBytes.Model.WsShape) : Prop where
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
  /-- seven facts on the public parameters, for the lemma that joins the two sentences for
  "weights" -/
  plan : (VerifiableInference.Desc.Kinds.Head.parOf (P5J.At.X Zp).hS
    (workOf (P5J.At.X Zp))).ok = true
  tokens : (P5J.At.X Zp).T = (P5J.At.X Zp).hS.T
  sized : OnBytes.Road.SizedW shW ppref
  wsLay : OnBytes.Model.wsLayOf shW true kRef = .ok (P5J.At.X Zp).layers.wsLay
  lam : (P5J.At.X Zp).H.lamS = 13
  vocab : (P5J.At.X Zp).hS.V = 202048
  dim : (P5J.At.X Zp).hS.d = 5120
  /-- the two facts along "reached" that are left -/
  waK6 : ∀ (z : ProofFile.InstPub)
    (a : S × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    h.toAtMg.rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → WaK6 (P5J.At.X Zp) V' a.1
  sized340 : ∀ a, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 340 a → ∀ G, a.2.fork? = some G → Sized G

set_option maxRecDepth 100000 in
/-- **With the eight facts at 346 laid in.** -/
theorem k11Rest_of_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (k ni O' m V' : ℕ) (L : Laid) (shW : OnBytes.Model.WsShape)
    (Q : K11Closed h Bs xM xI k ni O' m V' L shW) :
    K11Rest (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h Bs h.toAtMg.rch xM xI k ni (P5J.At.foldD Zp cF L).free0 O' m V'
      (P5J.At.foldD Zp cF L).fvs L (P5J.At.foldD Zp cF L).M (P5J.At.shape Zp) shW :=
  have E := eight_at346 h Q.laid Q.start Q.madeRow
  { pendAll := Q.pendAll
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
    plan := Q.plan
    tokens := Q.tokens
    sized := Q.sized
    wsLay := Q.wsLay
    lam := Q.lam
    vocab := Q.vocab
    dim := Q.dim
    room := E.room
    pileWithin := E.pileWithin
    msgShapes := E.msgShapes
    codes := E.codes
    bookInOrder := E.bookInOrder
    seatsCarried := E.seatsCarried
    bookFits := E.bookFits
    liveShape := E.liveShape
    waK6 := Q.waK6
    sized340 := Q.sized340 }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM `K11Closed`.** -/
theorem k11_kind_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
      ∃ (k ni O' m V' : ℕ) (L : Laid) (shW : OnBytes.Model.WsShape),
        K11Closed h Bs xM xI k ni O' m V' L shW) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_rest h 𝔏 q₁ q₂ q₃ tm hc fun Bs base O xM xI e2 e3 => by
    obtain ⟨k, ni, O', m, V', L, shW, Q⟩ := K Bs base O xM xI e2 e3
    exact ⟨k, ni, _, O', m, V', _, L, _, _, shW, k11Rest_of_closed h Bs xM xI k ni O' m V' L shW Q⟩

end K11

#print axioms K11.k11Rest_of_closed
#print axioms K11.k11_kind_closed
