-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadModelAt.lean: THE KIND "LOOKUP" (K3): THE FIELD model AT THE OUTPUT HEAD's
CALLS (`HeadModelR`, Johnson/Desc/First/Look/K3HeadModelR.lean; `HeadShortR.model`,
Johnson/P5J/K03HeadAt.lean) AT THE CLOSED CONSTANT: what the joint in front of the lookup says of
the caller's messages at the heard token gives the two items `constr 24 lookCallsHeard` and
`constr 24 rider` of the composed meaning. Five theorems: joinings of two other authors' laws; one
example, a test of fit.
The chain. `HeadSays` gives the two parts on THE CALLER's cells (Johnson/P5J/HeadSaysParts.lean).
The caller's cells and the law's cells, off one witness, agree inside the ranges
(`sameCells_caller`, Johnson/Desc/Kinds/Law/HeadCellsAtCaller.lean); both parts read no cell
beyond the ranges (`lookCalls_same`, `rider_same`, Law/CellsAlike.lean): so they hold on THE LAW's
cells: these are `LookCallsAt` and `RiderAt`; from them `constr_heard_of_at` and
`constr_rider_of_at` (Law/KeysNoToken.lean) give the two items.
  `k03_token`: under the promise in front of the head's calls, "reached" and no mark: a token y0
    below the vocabulary's size is heard; the state's reader answers it. From the
    public item tokenSmall, which is open at that border (`k3_open_token`), and the fact replyNat
    of `FoldFacts`.
  `k03_sameCells`: the caller's cells and the law's at the constant's own terms, at a witness
    whose cells are in range (`InRange w.cells`), under the tests hk6 and hcalls.
  `k03_model_core`: the two items. `k03_head_model`: the field, to the letter; the example lays it
    into `HeadShortR`'s own place beside letters for the two other fields (an example leaves no
    name: no answer on axioms speaks of it). `k03_floor`: the floor at which `HeadOK` is asked
    here is `k3FloorAt`: by unfolding.
WHAT STAYS IN FRONT: FIVE BINDERS, EACH ON PUBLIC DATA ALONE. Three are tests with code: hk6 :
`planK6AtZ Zp = true` · hcalls : `callsSeatedC … = true` at the constant's terms · hrows : `rowsOk
(rowH x) = true`. Two are sentences: hOK : `HeadOK ‹the setting› x ‹the floor›`, a structure of
four sentences (another author's `headOK_at`, Johnson/Desc/First/Look/K3HeadStated.lean, gives it
from the test `headB ‹the floor› x.fs = true` at `headAt`'s place) · hbits : each of the six
calls' tables has the kind's number of rows. AND FF: the facts on reached states (the counted
head's own field). THE ITEM `constr 24 small` IS NOT SPENT: the integers of segment 24 are small
by their make (`smallH_own`).
On instances. `HeadSays` and `HeadOK` stand at `k3SizesAt`, `k3PolicyAt` and the parameters'
request; the other author's two items stand at `sizesOf`, its plan's policy (at two numbers of
work) and the request off the state's words. The first two pairs are one by unfolding, which Lean
checks without a word; the requests are one by `rqX_at_const`, `requestOf_words` and the fact
reqIs.
Limits: joinings: ALL THE WEIGHT LIES IN THE TWO OTHER AUTHORS' FILES. The head h is a premise.
The full size alone. No soundness is claimed.

-/
import Johnson.P5J.HeadSaysParts
import Johnson.P5J.K03HeadAt
import Johnson.P5J.FoldAt
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.KeysNoToken
import Johnson.Desc.Kinds.Law.HeadCellsAtCaller
import Johnson.Desc.Kinds.Law.HeadWeightsMeet
import Johnson.Desc.Kinds.Law.DecInRange
import Johnson.Desc.Kinds.Law.PlanK6AtAll
import Johnson.Desc.Kinds.Law.K6CallsTest
import Johnson.Desc.Kinds.Law.FillK6K7Says
import Johnson.Desc.Kinds.Law.HeadRangesOfNumbers
import Johnson.Desc.First.Look.K3HeadStated
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.Desc.Sound.OnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (FoldFacts Pub)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (reqW_at_const rqX_at_const inRange_of_pin)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Lp : VerifiableInference.Desc.K12.Door.Laid}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "WT" => Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Lp) At.reqW At.links At.ps)

include FF in
/-- **A token below the vocabulary's size is heard in front of the head's calls.** -/
theorem k03_token (z : ProofFile.InstPub) (a : TS × (FrD).E.Str)
    (ha : onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
      (fun s => (z, s)) (k3K 24 false) a)
    (hr : h.toAtMg.rch (k3K 24 false) ((z, a.1), a.2)) (hm : a.1.failed = none) :
    ∃ y0, a.1.replyTok? = some y0 ∧ y0 < (At.X Zp).hS.V := by
  have OP := onParts_of_on _ _ _ _ (fun s : TS => (z, s)) _ a ha hm
  have hopen : Pub.tokenSmall ∈ pubQ (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS
      (k3K 24 false) := by
    rw [mgAll_more_closed _ _ rfl]
    exact MgAt.k3_open_token
  have htB : tokenHeardB (At.X Zp).hS (readsOf (At.X Zp)) a.1 = true :=
    OP.pub .tokenSmall (List.mem_append_left _ hopen)
  obtain ⟨y0, hy0, hyV⟩ := tokenHeardB_says (At.X Zp) a.1 htB
  refine ⟨y0, ?_, hyV⟩
  have hy1 : a.1.out.reply.map OnBytes.Desc.Reply.tokOf = some y0 := hy0
  unfold VerifiableInference.Desc.First.S.replyTok?
  cases hg : a.1.out.reply with
  | none =>
    rw [hg] at hy1
    cases hy1
  | some g =>
    rw [hg] at hy1
    have e := FF.replyNat (k3K 24 false) ((z, a.1), a.2) hr hm g hg
    show (if OnBytes.Model.ofNat g.c0.toNat == g then some g.c0.toNat else none) = some y0
    rw [e, if_pos (beq_self_eq_true _)]
    exact hy1

/-- **The caller's cells and the law's, at the constant's own terms**, at a witness whose stored
table is in range. -/
theorem k03_sameCells (hk6 : OffPad.planK6AtZ Zp = true)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (w : WT) (hR : VerifiableInference.OnPublicFiles.Flat.InRange w.cells) :
    @SameCells (parOf (At.X Zp).hS (workOf (At.X Zp))).sizes
      (headCells (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent
        (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf
        (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
        (layMs x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
          (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
          (h.toAtMg.𝔇 h.𝔇).l3.msgW w))
      (compCut (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
        (_root_.Meaning.sizesOf (At.X Zp)) (seatLay (At.X Zp) (At.layout Zp) (At.num Zp))
        (At.X Zp) (plAt (At.num Zp 24 0) 0) w).1 := by
  letI := (parOf (At.X Zp).hS (workOf (At.X Zp))).sizes
  letI := (parOf (At.X Zp).hS (workOf (At.X Zp))).policy
  letI : Request := ⟨fun _ => 0, 0, 0⟩
  have hN := InScope.numbers_in_scope h.scope h.reads h.pubOne
  exact Came.sameCells_caller (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
    (At.layout Zp) (At.num Zp) (plAt (At.num Zp 24 0) 0) x (h.toAtMg.𝔇 h.𝔇).sent
    (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf
    (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
    (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.msgW w
    (Came.inRanges_in_scope h.scope h.reads h.pubOne _)
    (fun a r c => Came.inSizes_in_scope h.scope h.reads h.pubOne a r c) h.plan.laid rfl rfl
    (OffPad.planK6_atAll h.toAtMg hk6).1
    (AtFold.calls_of_C hcalls
      (ColFour (At.X Zp).hS (At.X Zp).HLy (OnBytes.Model.Verify.borderOf (At.X Zp).y))
      (fun a c hc => by
        have e := OffPad.four_matrix hc
        omega))
    (Came.smallH_own (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) _ _ (At.X Zp) w
      (by rw [Came.beta_landed]; norm_num) (by rw [Came.beta_landed]; norm_num))
    fun k v hk hv => Came.weights_stored x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent
      (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.arr
      (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (k3AdrAt (At.X Zp)) w hR k v
      (hN.d ▸ hk) (hN.V ▸ hv)

include FF in
/-- **The two items, from what the joint in front says.** -/
theorem k03_model_core (hk6 : OffPad.planK6AtZ Zp = true)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (hOK : @HeadOK (k3SizesAt (At.X Zp)) (OnBytes.Params.settingOf (At.X Zp).P.frame) x
      (parOf (At.X Zp).hS 0).floor)
    (hrows : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      rowsOk (rowH x) = true)
    (hbits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c)
    (z : ProofFile.InstPub) (a : TS × (FrD).E.Str) (w : WT)
    (ha : onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
      (fun s => (z, s)) (k3K 24 false) a)
    (hr : h.toAtMg.rch (k3K 24 false) ((z, a.1), a.2)) (hm : a.1.failed = none)
    (hS : @HeadSays (k3SizesAt (At.X Zp)) (k3PolicyAt (At.X Zp)) ((h.toAtMg.𝔇 h.𝔇).rq z)
      (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
      (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr
      (h.toAtMg.𝔇 h.𝔇).l3.nc (a.1.replyTok?.getD 0)
      (layMs x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (h.toAtMg.𝔇 h.𝔇).l3.msgW w))
    (hpin : (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pinW (z, a.1) (strsOf FrD a.2) w) :
    (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).constr 24 .lookCallsHeard (z, a.1) (strsOf FrD a.2) w ∧
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).constr 24 .rider (z, a.1) (strsOf FrD a.2) w := by
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have OP := onParts_of_on _ _ _ _ (fun s : TS => (z, s)) _ a ha hm
  have hb : (_root_.Meaning.backReq z.request).isSome = true := OP.order
  have hw : a.1.req = OnBytes.Flat.requestWordsOf (h.𝔇.H.req (z, a.1)).val :=
    (FF.reqIs (k3K 24 false) ((z, a.1), a.2) hr hm).trans (reqW_at_const h (z, a.1) hb)
  have hrq : h.𝔇.rq z = reqX (h.𝔇.H.req (z, a.1)).val := rqX_at_const h (z, a.1) hb
  have hq : requestOf a.1 = reqX (h.𝔇.H.req (z, a.1)).val := Came.requestOf_words a.1 _ hw
  have hFull : OnBytes.Road.Hd.FullH (At.X Zp).hS :=
    (OnBytes.Road.Hd.public_of_core h.pubOne
      (OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne)).full
  have hplan : (parOf (At.X Zp).hS (workOf (At.X Zp))).ok = true :=
    InScope.ok_in_scope h.scope h.reads h.pubOne _
  obtain ⟨y0, hy0, hyV⟩ := k03_token h FF z a ha hr hm
  rw [hy0] at hS
  have hS0 : @HeadSays (k3SizesAt (At.X Zp)) (k3PolicyAt (At.X Zp)) ((h.toAtMg.𝔇 h.𝔇).rq z)
      (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
      (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr
      (h.toAtMg.𝔇 h.𝔇).l3.nc y0
      (layMs x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (h.toAtMg.𝔇 h.𝔇).l3.msgW w) := hS
  have hyP : y0 < ppref.V := by
    have hv := hyV
    rw [hFull.V] at hv
    exact hv
  have htok : (tokHOf (z, a.1)).val = y0 := by
    rw [tokHOf_of_heard (z, a.1) y0 hy0 hyP]
  have hR : VerifiableInference.OnPublicFiles.Flat.InRange w.cells :=
    inRange_of_pin h (z, a.1) (strsOf FrD a.2) w hpin
  have sC := k03_sameCells h hk6 hcalls w hR
  -- the two parts on the law's cells, at the request as the state's words spell it
  have key : ∀ Rq : Request, Rq = reqX (h.𝔇.H.req (z, a.1)).val →
      @HeadSays (k3SizesAt (At.X Zp)) (k3PolicyAt (At.X Zp)) Rq
        (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
        (h.toAtMg.𝔇 h.𝔇).l3.oW (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr
        (h.toAtMg.𝔇 h.𝔇).l3.nc y0
        (layMs x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
          (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
          (h.toAtMg.𝔇 h.𝔇).l3.msgW w) →
      LookCallsAt (At.X Zp) (At.tabH x) a.1 y0
          (compCut (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
            (_root_.Meaning.sizesOf (At.X Zp)) (seatLay (At.X Zp) (At.layout Zp) (At.num Zp))
            (At.X Zp) (plAt (At.num Zp 24 0) 0) w).1 ∧
        RiderAt (At.X Zp) a.1 y0
          (compCut (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
            (_root_.Meaning.sizesOf (At.X Zp)) (seatLay (At.X Zp) (At.layout Zp) (At.num Zp))
            (At.X Zp) (plAt (At.num Zp 24 0) 0) w).1 := by
    intro Rq e hs
    subst e
    unfold LookCallsAt RiderAt
    rw [hq]
    letI : Sizes := Law.sizesOf (At.X Zp).hS
    letI : Policy := (parOf (At.X Zp).hS (workOf (At.X Zp))).policy
    letI : Request := reqX (h.𝔇.H.req (z, a.1)).val
    letI : Token := ⟨y0⟩
    have P : PlanFacts := planFacts (sT := (At.X Zp).hS.tabS) hplan
    have hreq : Request.ok = true :=
      Came.okStart_atX (At.X Zp).hS (workOf (At.X Zp)) (h.𝔇.H.req (z, a.1)).val hFull
        (_root_.Meaning.head3_of_req (h.𝔇.H.req (z, a.1)))
    exact ⟨Came.lookCalls_same sC P hreq hyV _ _
        (says_lookCalls (sT := (At.X Zp).hS.tabS) hOK ⟨hplan, hrows, hbits⟩ hs),
      Came.rider_same sC P (says_guests hs)⟩
  obtain ⟨hl, hrd⟩ := key _ hrq hS0
  have hdec : ∀ M, (oneDec h.𝔇.decT h.𝔇.H).dec (z, a.1) (strsOf FrD a.2) = some M →
      M = w.cells := fun M hM => Option.some.inj (hM.symm.trans hpin)
  refine ⟨?_, ?_⟩
  · show constrQAt (headLink (At.X Zp)) h.𝔇.put (oneDec h.𝔇.decT h.𝔇.H) h.𝔇.headPart
      h.𝔇.digitsPart 24 .lookCallsHeard (z, a.1) (strsOf FrD a.2) w
    rw [h24]
    exact Came.constr_heard_of_at (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) _ _
      (At.X Zp) _ (At.tabH x) (oneDec h.𝔇.decT h.𝔇.H) tokHOf h.𝔇.digitsPart 24 (z, a.1)
      (strsOf FrD a.2) w hFull hplan (htok ▸ hl) hw hdec
  · show constrQAt (headLink (At.X Zp)) h.𝔇.put (oneDec h.𝔇.decT h.𝔇.H) h.𝔇.headPart
      h.𝔇.digitsPart 24 .rider (z, a.1) (strsOf FrD a.2) w
    rw [h24]
    exact Came.constr_rider_of_at (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) _ _
      (At.X Zp) _ (At.tabH x) (oneDec h.𝔇.decT h.𝔇.H) tokHOf h.𝔇.digitsPart 24 (z, a.1)
      (strsOf FrD a.2) w y0 hplan hrd hw

include FF in
/-- **THE FIELD model AT THE HEAD's CALLS, AT THE CONSTANT**: `HeadShortR.model`'s own text. -/
theorem k03_head_model (hk6 : OffPad.planK6AtZ Zp = true)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (hOK : @HeadOK (k3SizesAt (At.X Zp)) (OnBytes.Params.settingOf (At.X Zp).P.frame) x
      (parOf (At.X Zp).hS 0).floor)
    (hrows : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      rowsOk (rowH x) = true)
    (hbits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c)
    {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ))
    (s₀ : VerifiableInference.Desc.First.S)
    (q : Piece (Run.ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S) Cl WT)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl) :
    ∀ B', SeatOf b' B' → ∀ z : ProofFile.InstPub,
      letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      letI := (h.toAtMg.𝔇 h.𝔇).rq z
      HeadModelR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).G (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl
        (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
        (OnBytes.Params.settingOf (At.X Zp).P.frame)
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (smpCalls seats (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
          (h.toAtMg.𝔇 h.𝔇).l3.seat x)
        (Stored.smpWc (rows := numsFull.rows) (cols := colsAt numsFull))
        (Stored.strWc (h.toAtMg.𝔇 h.𝔇).decT s₀ z) (h.toAtMg.𝔇 h.𝔇).l3.msgW k3QAny
        (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
        (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) claim (h.toAtMg.𝔇 h.𝔇).N
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) := by
  intro _ _ z
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  letI := (h.toAtMg.𝔇 h.𝔇).rq z
  exact ⟨fun a w ha hr hm hS _ hpin =>
    k03_model_core h FF hk6 hcalls hOK hrows hbits z a w ha hr hm hS hpin⟩

/-- A test of fit: the field goes into `HeadShortR`'s own place, beside letters for the two
others. -/
example (hk6 : OffPad.planK6AtZ Zp = true)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (hOK : @HeadOK (k3SizesAt (At.X Zp)) (OnBytes.Params.settingOf (At.X Zp).P.frame) x
      (parOf (At.X Zp).hS 0).floor)
    (hrows : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      rowsOk (rowH x) = true)
    (hbits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c)
    (seats : List (ℕ × ℕ)) (s₀ : VerifiableInference.Desc.First.S) (q) (b')
    (arrs : Array (Nat × String)) (pl pl' : VerifiableInference.Desc.Place)
    (told : List (List VerifiableInference.Desc.Oracle)) :=
  fun parts rides =>
    (⟨parts, k03_head_model h FF hk6 hcalls hOK hrows hbits K3Lot.ofForm seats s₀ q b', rides⟩ :
      HeadShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm seats s₀ x q b'
        arrs pl pl' told)

end

/-- The floor at which `HeadOK` is asked here is the lookups' own. -/
theorem k03_floor (X : OnBytes.Model.Verify.Public) : (parOf X.hS 0).floor = k3FloorAt X := rfl

end P5J

#print axioms P5J.k03_token
#print axioms P5J.k03_sameCells
#print axioms P5J.k03_model_core
#print axioms P5J.k03_head_model
#print axioms P5J.k03_floor
