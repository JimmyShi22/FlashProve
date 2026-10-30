-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfRest.lean: WHAT IS LEFT BENEATH THE CONDITIONS OF THE KIND K11's OWN SENTENCE (the
merge of the claims on the committed table), when every payment at hand is laid in.
One structure, one theorem of the form "rest gives the condition":
a joining.

What is said.
  `K11Rest h Bs Rch xM xI k ni free0 O' m V' fvs L M sh shW`: THIRTY-TWO NAMED CONDITIONS.
    TWENTY-TWO READ NO STATE: two closed tests with code (pendAll, low); seven facts on the letters
    (roomLeft; idxSeat, idxShape, idxRows, niIs, ellPow; inM at 0 bits of a row's index); six facts
    on numbers for the test on the mask row (maskNo, maskLt, maskNum, maskSeat, maskOwn, maskBits);
    seven facts on the public parameters for the lemma that joins the two sentences for "weights"
    (plan, tokens, sized, wsLay, lam, vocab, dim). TEN ARE FACTS ALONG "REACHED": at the border 346:
    room, pileWithin, msgShapes, codes, bookInOrder, seatsCarried, bookFits, liveShape (the words of
    Johnson/Desc/First/FoldFacts.lean) and waK6 (the output head's condition on the state); at 340:
    sized340 (the open ledger has its sizes).
  `k11Cond_of_rest`: at an opening O whose description passes its test on the plan, for a "reached"
    within the description's own, where xM sits at (73, 2) and xI at the index masks' place:
    `K11Rest` gives `K11Cond` (LawAtMg.lean) at posI := `posMask k`, R := 0 and Wa := `WaSeat …`
    (the output head's condition with its eighth clause).

By what. `k11Cond_of_tight` (CondOfTight.lean) at a `K11Tight` whose fields mask, frontWa,
weights and leaves are laid: mask by `mask_paid` (MaskPaid.lean); frontWa and weights by
`frontWa_at` and `weights_at` (WaSeatAtMg.lean): SO THAT THEIR ENDS ARE THESE FIELDS' TEXT IS
LEAN's WORD HERE; leaves by `leaves_at346` (LeavesAt346.lean); the field front, which frontWa_at
spends, by `mergeFront_346` (Johnson/Top/H0/MergeLaw/FrontReached.lean).

Limits. NO CONDITION IS SHOWN HERE; that they can be met together is shown nowhere. They follow from
the head along this chain of files. The letters are tied by the facts that read no state alone; sh
and Bs.G₀.first.shape by nothing. What is left here is laid further in CondOfClosed.lean; the
whole chain is typed as one in CondOfPend.lean. The head is the head with the fourteen entry
tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which the payers of frontWa and
weights rest, stands over the form of the proof file's entry tests with fourteen rows, two of which
are the comparisons with the written plan; the head's field laid says that every entry test accepts.
A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.K11R.CondOfTight
import Johnson.K11R.MaskPaid
import Johnson.K11R.WaSeatAtMg
import Johnson.K11R.LeavesAt346

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape ceilLog2)
open OnBytes.Params (ReqShape)
open OnBytes.PscRun (Sized)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K13 (pileWithinC)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstFits atFirstShapes)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6 WaSeat)
open Johnson.Desc.First.Walk.Tied (Reach RchAt roomIsB rowsBefore)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open P5J (AtMgA mgAtAll TS)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT BENEATH THE KIND K11's CONDITIONS**: facts that read no state; and ten facts
along "reached". -/
structure K11Rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (xM xI : Mem) (k ni free0 O' m V' : ℕ)
    (fvs : List Bool) (L : Laid) (M : List OracleShape) (sh : ReqShape)
    (shW : OnBytes.Model.WsShape) : Prop where
  /-- closed tests, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  low : lowAtB h.𝔇.N open346 (treesInFront VerifiableInference.PlanWritten.cutFirstFull 346) = true
  /-- facts on the letters, which read no state: the index masks' message; the mask row's table -/
  roomLeft : 0 < free0 - rowsBefore fvs 24
  idxSeat : L.places[h.𝔇.N.indexNo]? = some h.𝔇.N.index
  idxShape : M[h.𝔇.N.indexNo]? = some (xI.1.l.get xI.2).1
  idxRows : (xI.1.l.get xI.2).1.maskRows = 2 ^ k
  niIs : 2 ^ (k + (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll) = ni
  ellPow : (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).ell =
    2 ^ (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll
  inM : ∀ j, j < (parOf Zp Bs.G₀).nMsg → InMsg h.𝔇.cs (xM.1.l.get xM.2).1 (posMask 0 j).1
    (posMask 0 j).2.1 (posMask 0 j).2.2
  /-- six facts on numbers, for the test on the mask row -/
  maskNo : maskNoOf sh 24 = some m
  maskLt : m < firstCount sh 24
  maskNum : O' + (firstCount sh 24 + 1) +
    (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
      h.𝔇.N.msgsAt (some mergeAt) + m
  maskSeat : L.places[O']? = some (seatOf xM)
  maskOwn : seatOf xM ∈ h.𝔇.N.group 24
  maskBits : (M[O']?).map (fun y => ceilLog2 y.maskRows) = some 0
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
  /-- the facts along "reached", at 346 -/
  room : ∀ (a : (ProofFile.InstPub × S) × Fr.E.Str) p' m', Rch 346 a → a.1.2.failed = none →
    (flatPlacesOf linksFull true)[346]? = some p' → p'.link = some m' → 2 ≤ p'.piece →
    roomIsB free0 fvs m' a.1.2 = true
  pileWithin : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    pileWithinC a.1.2 = true
  msgShapes : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstShapes M a.1.2 = true
  codes : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    a.1.2.st.codes = h.𝔇.cs
  bookInOrder : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstBook 0 a.1.2 = true
  seatsCarried : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstSeats L a.1.2 = true
  bookFits : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    atFirstFits a.1.2 = true
  liveShape : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
    a.1.2.live.frame.shape = sh
  waK6 : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → WaK6 (P5J.At.X Zp) V' a.1
  /-- and one at 340: the open ledger has its sizes -/
  sized340 : ∀ a, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 340 a → ∀ G, a.2.fork? = some G → Sized G

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **What is left gives the kind's conditions.** -/
theorem k11Cond_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {F : FileDescription ProofFile.Inst} {base : List (Block S Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {Fr : Frame} (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (FD Zp A B cF) 346 a)
    (xM xI : Mem) (hxM : seatOf xM = (73, 2)) (hxI : seatOf xI = h.𝔇.N.index)
    (k ni free0 O' m V' : ℕ) (fvs : List Bool) (L : Laid) (M : List OracleShape) (sh : ReqShape)
    (shW : OnBytes.Model.WsShape)
    (Q : K11Rest h Bs Rch xM xI k ni free0 O' m V' fvs L M sh shW) :
    K11Cond h Bs Rch xM xI (posMask k) ni 0
      (WaSeat h.𝔇.arr h.𝔇.N (P5J.At.X Zp) (P5J.At.num Zp 24 0) 0 V') := by
  have hmask := mask_paid h O Rch hsub xM 0 O' L M sh m Q.maskNo Q.maskLt Q.maskNum Q.maskSeat
    Q.maskOwn Q.maskBits Q.seatsCarried Q.msgShapes Q.liveShape
  have hfront := mergeFront_346 h.𝔇 mgBase rfl Rch h.𝔇.N (h.𝔇.N.group 24) xM 0 ni free0 fvs M
    h.𝔇.cs (xI.1.l.get xI.2).1 Q.roomLeft Q.idxShape
    (by
      rw [Q.idxRows, Fmt.Places.logUp_two_pow]
      exact Q.niIs)
    hmask Q.room Q.pileWithin Q.msgShapes Q.codes
  exact k11Cond_of_tight h Bs O hOk Rch hsub xM xI hxI 0 k ni free0 fvs L M _
    { pendAll := Q.pendAll
      low := Q.low
      roomLeft := Q.roomLeft
      idxSeat := Q.idxSeat
      idxShape := Q.idxShape
      idxRows := Q.idxRows
      niIs := Q.niIs
      ellPow := Q.ellPow
      inM := Q.inM
      room := Q.room
      pileWithin := Q.pileWithin
      msgShapes := Q.msgShapes
      codes := Q.codes
      bookInOrder := Q.bookInOrder
      seatsCarried := Q.seatsCarried
      bookFits := Q.bookFits
      mask := hmask
      frontWa := frontWa_at h Rch V' ni xM hxM Q.waK6 hfront
      weights := weights_at h Bs ni V' O.blank Q.plan Q.tokens Q.sized Q.wsLay Q.lam Q.vocab Q.dim
      leaves := fun z a _ hR hm =>
        leaves_at346 h.scope h.reads O hOk Rch hsub Q.sized340 ((z, a.1), a.2) hR
          (Classical.not_not.1 hm) }

end K11

#print axioms K11.k11Cond_of_rest
