-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfTight.lean: THE CONDITIONS OF THE KIND K11's OWN SENTENCE (the merge of the claims
on the committed table), IN THE TIGHT FORM: which facts along "reached" the kind spends, each by
name, at which border. One structure, one theorem: a joining.

What is said.
  `K11Tight h Bs Rch xM xI R k ni free0 fvs L M Wa`: TWENTY NAMED CONDITIONS, by sort: two closed
    tests with code, off the public parameters alone (pendAll, low); seven facts that read no state
    (roomLeft; idxSeat, idxShape, idxRows, ellPow, niIs: what the index masks' message is, that its
    mask rows and its mask code's length are powers of two, and that ni is its mask table's size;
    inM: the reading of the mask row's table); SEVEN FACTS ALONG "REACHED", AT THE BORDER 346 ALONE,
    in the words of Johnson/Desc/First/FoldFacts.lean: room, pileWithin, msgShapes, codes,
    bookInOrder, seatsCarried, bookFits; mask: the two readings of the segment's mask row meet,
    there (`maskAtB`); frontWa: the letter Wa holds there; weights: the lemma that joins the two
    sentences for "weights", under Wa; leaves (`leavesLenB`): a test with code at a reached state in
    front of the merge.
  `k11Cond_of_tight`: at an opening O whose description passes its test on the plan, for a "reached"
    that lies within the description's own (hsub), where xI sits at the index masks' place,
    `K11Tight` gives `K11Cond` (LawAtMg.lean) at posI := `posMask k`: its field front by
    `mergeFront_346` (Johnson/Top/H0/MergeLaw/FrontReached.lean), behindIdx by `idx_behind`
    (IdxBehind.lean), inI by `inMsg_whole_table` (SlotsWhole.lean);
    digThere by `digThere_in_scope` (DigThere.lean); speaks by `speaks_paid` (SpeaksPaid.lean) at
    `tablesLaid_at_346_pub` (TablesAt346.lean); nums and oneClaim by
    `numsB_head_of_public` and `nclB_head_of_public` (Johnson/Desc/Sound/K11Tests/),
    the first at the head's field cols13; niPos from niIs; the six others are
    fields of both.

Limits. NO CONDITION IS SHOWN HERE; that they can be met together is shown nowhere. The letters R,
k, ni, free0, fvs, L, M, Wa are tied by these facts alone. mask's known payer speaks of no state in
two of three cases at number 339 (not shown here). Nothing on soundness.

-/
import Johnson.K11R.LawAtMg
import Johnson.Top.H0.MergeLaw.FrontReached
import Johnson.Top.H0.MergeLaw.IdxBehind
import Johnson.Top.H0.MergeLaw.SlotsWhole
import Johnson.K11R.DigThere
import Johnson.K11R.SpeaksPaid
import Johnson.K11R.TablesAt346
import Johnson.Desc.Sound.K11Tests.NclHeadInScope
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Fmt.PlacesLaws
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape ceilLog2)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Fmt.Places (logUp)
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K13 (pileWithinC)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstFits atFirstShapes)
open Johnson.Desc.First.Walk.Tied (roomIsB rowsBefore)
open Johnson.Desc.First.ForkMerge (headMergeDecide)
open P5J (AtMgA mgAtAll TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE KIND K11's CONDITIONS IN THE TIGHT FORM**: facts that read no state; and facts at a
reached state in front of the merge, at the border 346 alone, each by name. -/
structure K11Tight (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (xM xI : Mem) (R k ni free0 : ℕ)
    (fvs : List Bool) (L : Laid) (M : List OracleShape) (Wa : S → Prop) : Prop where
  /-- closed tests, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  low : lowAtB h.𝔇.N open346 (treesInFront VerifiableInference.PlanWritten.cutFirstFull 346) = true
  /-- facts on the letters, which read no state -/
  roomLeft : 0 < free0 - rowsBefore fvs 24
  idxSeat : L.places[h.𝔇.N.indexNo]? = some h.𝔇.N.index
  idxShape : M[h.𝔇.N.indexNo]? = some (xI.1.l.get xI.2).1
  idxRows : (xI.1.l.get xI.2).1.maskRows = 2 ^ k
  niIs : 2 ^ (k + (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll) = ni
  ellPow : (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).ell =
    2 ^ (Johnson.Pack.pMask h.𝔇.cs (xI.1.l.get xI.2).1).logEll
  inM : ∀ j, j < (parOf Zp Bs.G₀).nMsg → InMsg h.𝔇.cs (xM.1.l.get xM.2).1 (posMask R j).1
    (posMask R j).2.1 (posMask R j).2.2
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
  mask : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → a.1.failed = none →
    maskAtB (h.𝔇.N.group 24) (seatOf xM) R a.1 = true
  frontWa : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Wa a.1
  /-- the lemma that joins the two sentences for "weights" -/
  weights : ∀ a y w, Wa a.2 → VerifiableInference.Desc.First.FillP1.wtP1 (parOf Zp Bs.G₀) ni
    (fun w => VerifiableInference.Desc.K13.Law.cellAtNo w.cells)
    (maskRowAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N 24) a y w → h.𝔇.wt 24 a y w
  /-- a test with code at a reached state in front of the merge -/
  leaves : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
    Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → leavesLenB a.1 = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The tight form gives the kind's conditions.** -/
theorem k11Cond_of_tight (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    {base : List (VerifiableInference.Desc.Block S ProofFile.Cl)} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B)
    (hOk : F.planOk = true)
    {Fr : Frame} (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hsub : ∀ a, Rch 346 a → Johnson.Desc.First.Walk.Tied.RchAt (FD Zp A B cF) 346 a)
    (xM xI : Mem) (hxI : seatOf xI = h.𝔇.N.index)
    (R k ni free0 : ℕ) (fvs : List Bool) (L : Laid) (M : List OracleShape) (Wa : S → Prop)
    (T : K11Tight h Bs Rch xM xI R k ni free0 fvs L M Wa) :
    K11Cond h Bs Rch xM xI (posMask k) ni R Wa where
  nums := LT28.K11Tests.numsB_head_of_public h.scope h.reads h.laid.pub h.pubOne
    (Nat.pow_right_injective (le_refl 2) (h.cols13.trans (by decide +kernel)))
  oneClaim := LT28.K11Tests.nclB_head_of_public h.scope h.reads h.laid.pub h.pubOne
  pendAll := T.pendAll
  niPos := by
    rw [← T.niIs]
    exact Nat.pow_pos (by decide)
  inM := T.inM
  inI := by
    rw [← T.niIs]
    exact inMsg_whole_table h.𝔇.cs xI k T.idxRows T.ellPow
  low := T.low
  weights := T.weights
  front := mergeFront_346 h.𝔇 mgBase rfl Rch h.𝔇.N (h.𝔇.N.group 24) xM R ni free0 fvs M h.𝔇.cs
    (xI.1.l.get xI.2).1 T.roomLeft T.idxShape
    (by
      rw [T.idxRows, Fmt.Places.logUp_two_pow]
      exact T.niIs)
    T.mask T.room T.pileWithin T.msgShapes T.codes
  frontWa := T.frontWa
  behindIdx := idx_behind h.𝔇 mgBase rfl (parOf Zp Bs.G₀) h.𝔇.N Rch L M xI k ni k T.bookInOrder
    T.seatsCarried T.bookFits T.msgShapes T.codes T.idxSeat T.idxShape hxI T.idxRows T.niIs
    (by rw [T.idxRows, OnBytes.Slice.ceilLog2_two_pow])
  speaks := speaks_paid h O Rch fun z a _ hR _ =>
    tablesLaid_at_346_pub h.scope h.reads O Rch hsub ((z, a.1), a.2) hR
  leaves := T.leaves
  digThere := K11Live.digThere_in_scope h.scope h.reads O hOk

end K11

#print axioms K11.k11Cond_of_tight
