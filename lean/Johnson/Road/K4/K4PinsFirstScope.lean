-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsFirstScope.lean: WHAT THE ASSEMBLY OF K4's LAW LEAVES AT THE FIRST GROUP, IN
THE GOALS' SCOPE AT AN OPENING OF THE IOP AS WRITTEN IN LEAN: THE END IS THE CONSEQUENT OF THE
ASSEMBLY's BINDER ON THE FIRST GROUP (`k04_law_at`, Johnson/Road/K4/K04LawAt.lean, its binder LF),
by reading. THE TWIN OF K4PinsLaterScope.lean, cut by program out of its
text: `firstAt_whole` (K4PinsFirstWhole.lean) called. AND: `K4PinsFill` AS ONE TERM AT THE COMPOSED
MEANING's CLOSED TERM. A gathering of calls. No draw, no count.

  `firstAt_scope_at`: at every group g < 12 (nothing in it asks that the group is the first).
  **`firstAt_wide_scope`**: that at g := 0: the numbers stand as "28 * 0 + 4" and "2 * 0", as the
    assembly writes them.
  **`pinsFill_const`**: `K4PinsFill (asOurs …) Zp`: out of the twelve theorems of
    K4PinsAtConstant.lean; AT THE CLOSED TERM (`P5J.At.𝔇Whole`):
      its line hid by unfolding, no scope. **`reqTies_const`**: the three ties on the
      request's letters at that term, where the wider meaning's words of the request are that
      term's own (`P5J.At.reqW`).

OBJECT: `k4DataWide Dm Ew mgBase`, `mgWide Dm Ew mgBase`; `P5J.At.𝔇All`. USER:
Johnson/Road/K4/K04LawFull.lean; meant: `k04_law_at`. LETTERS: as named; tokens := ℕ.

Limits. K04_law IS NOT PROVED BY THIS. `RefPub` and the three facts on the public
parameters are drawn inside (`refPub_in_scope`, `scope_la`: Johnson/Road/K4/RefInScope.lean;
`emb_public_in_scope`: Johnson/Goal/Meaning/EmbScope.lean). The three ties on the request's letters
(reqT), `K4Fill`, `K4NamedW`, `K4PinsFill` AND `K4PinsTests` ARE PREMISES OF THE FIRST TWO THEOREMS:
SHOWN TOGETHER AT NO PARAMETERS: NO MEMBER IS SHOWN. IT SPEAKS AT THE WIDER MEANING: it counts only
when the bridge to the meaning that counts is paid.
`pinsFill_const` is an equation of terms: the closed term's head is not
shown to be meetable.
-/
import Johnson.Road.K4.K4PinsLaterScope
import Johnson.Road.K4.K4PinsFirstWhole
import Johnson.Road.K4.K4PinsAtConstant
import Johnson.Goal.Meaning.EmbScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model (Forest.elems)
open OnBytes.Model.Verify (Public publicOf)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Riders (k4OnX_of_scope seats_at_open left_of_means)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription Wit Strs)
open VerifiableInference.Desc.First (S flatPlacesOf pubSets)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Look (Place Stored.entries)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (matOfCells)
open Meaning (seatBy fLay)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (maskFitsB recPlanOf maskPlanB arraysPlanB maskEllP openMask_mgWide
  inT_four_of_front)
open Inst.Model.Layout (kRef hRef)
open Inst.Model (ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Model.Verify (layerShape)

variable {Xi : Type} {nQ : ℕ}

variable {Fr : Frame} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In the goals' scope, at an opening: the assembly's structure for the first group has a member
  at
the wider meaning over the closed base.** -/
theorem firstAt_scope_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {Xp : Public}
    (hW : Bs.G₀.W = Xp) (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) {g : ℕ} (hg : g < 12) {x : Bool × Par}
    {b : Block S ProofFile.Cl} (h : K4Here c Z Bs.G₀ g x b) (Fl : K4Fill Dm Ew Z c)
    {told : List (List VerifiableInference.Desc.Oracle)}
    (Sn : K4NamedW Dm Ew (28 * g + 4) (2 * g) (parOf x) told (Forest.elems Xp.y.fo))
    (Pf : K4PinsFill Dm Z) (Pt : K4PinsTests Dm Ew Z (28 * g + 4) g (parOf x))
    (reqT : ReqTies (k4DataWide Dm Ew mgBase).reqB (k4DataWide Dm Ew mgBase).reqW
      (k4DataWide Dm Ew mgBase).H.req (k4DataWide Dm Ew mgBase).put)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (z : ProofFile.InstPub) :
    Nonempty (K4FirstAt (scl := sclX Xp g) x linksFull (flatPlacesOf linksFull true)
      (28 * g + 4) (2 * g) q (k4DataWide Dm Ew mgBase) (mgWide Dm Ew mgBase) z) := by
  have eX : Z.p.X = Xp := O.W.symm.trans hW
  subst eX
  have eg := h.hg
  subst eg
  have hpub : publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := hW ▸ O.public
  obtain ⟨k4, kN, _⟩ := _root_.Meaning.scope_plans hS hR hpub
  have Bp : RefPub Z.p.X x.2.g := refPub_in_scope hS hR hpub hg
  have hla := scope_la hS hR hpub
  have Ep := _root_.Meaning.Emb.emb_public_in_scope hS hR hpub
  have Sx : K4OnX Z.p.X Pb.pol Pb.KL (some ly) (2 * x.2.g) (parOf x) :=
    hW ▸ k4OnX_of_scope hS hR O hg h.mem h.link
  have Sd := k4OnD_of_fill Dm hS hR O hW hg h.mem h.link Fl
  have H := atK4_full x.2.g hg
  have Pl := k4RowPlan_wide Dm Ew H Sx Sd Sn
  obtain ⟨Lk, x', e1, e3, e5, st, _⟩ := seats_at_open hS hR O hg
  obtain rfl : x = x' := k04_sits_one h.mem e3 h.link e5
  have hH : isLay Dm.links (headLink Z.p.X) = false := by
    rw [Fl.links]
    unfold headLink
    rw [k4, kN, if_pos rfl]
    decide +kernel
  have Em := k4Means_mgWide Dm Ew
    (mgBase (P := ProofFile.InstPub) (W := Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT)) hH
    (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hlk : Dm.lk (2 * x.2.g) = some Lk := by
    rw [Fl.lk]
    exact e1
  have fit' := Em.more ▸ Pl.fit
  have hLo : ((pubSets (k4DataWide Dm Ew mgBase).moreL linksFull
      (flatPlacesOf linksFull true))[28 * x.2.g + 4]?.getD []).contains
      (.ledger (2 * x.2.g)) = true := by
    have h1 := k4_open (mgWide Dm Ew mgBase) H fit' (.ledger (2 * x.2.g)) (by simp)
    rw [Em.more] at h1
    simpa using h1
  have Kf := k4Front_of_means (Z := z) Em H Pl.linksIs Pl.pubOf Pl.notHead Pl.step Pl.plan Pl.fit
  rw [Pl.shape] at Kf
  obtain ⟨radM, Q3⟩ := Pf.ms
  obtain ⟨seats, Q7⟩ := Fl.smp
  have hP : (parOf x).P = { Z.p.X.layers with tokv := Z.p.X.layers.tokv } := hW ▸ h.P
  have hGx : Z.p.X.G[(parOf x).g]? = some (parOf x).hp := hW ▸ h.G
  have hV : (parOf x).P.V = ppref.V := by
    rw [hP]
    exact Ep.2.2.2
  have NE : EmbNums (parOf x).P.y := by
    rw [Sx.y]
    exact Ep.1
  exact firstAt_whole (scl := sclX Z.p.X x.2.g) Z Dm Ew mgBase x radM linksFull
    (flatPlacesOf linksFull true) (28 * x.2.g + 4) q hg z hpub Sx.notHead Sx.step Sx.plan
      Sx.pc2
    Sx.y k4 hGx (publicSteps_of hpub) Bp hP Pt.first hla hV NE reqT Pf.sent Pf.arr Q3 Pf.nSent
    Pf.nIndex Pf.seat3 (Pf.hid _) Q7 Fl.dec Pf.mat13 Em.msgShapes
    (fun a => by
      rw [Em.bookInOrder a, show (k4DataWide Dm Ew mgBase).d12.ft = 0 from Fl.ft])
    Em.seatsCarried (codes_of_means Em) (openMask_mgWide Dm Ew H) Pt.maskFits Pt.indexTie Em
    (VerifiableInference.Desc.K9.readersAt_some Dm.lk Z.p.X _ (2 * x.2.g) Lk hlk) Pl.runsOwn H Kf
    Pl.nsOf Pl.front (left_of_means Em H Pl.linksIs fit' (Em.more ▸ Pl.askLeft))
    (fun B' _ a τ fo o G' ha hu y =>
      inT_four_of_front Em (k4DataWide Dm Ew mgBase).sd Em.sentIs Em.treesAre z linksFull
        (flatPlacesOf linksFull true) (28 * x.2.g + 4) (2 * x.2.g) (parOf x) (twinOf q B')
        Pl.openAll hLo Pl.maskP Pl.readsP a τ fo o G' ha hu y)
    st Pl.openAll Pl.readsP Pt.maskPlan Pt.arrays Pt.ell Pf.uL

/-- **The same at the first group, the numbers as the assembly writes them.** -/
theorem firstAt_wide_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {Xp : Public}
    (hW : Bs.G₀.W = Xp) (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) {x : Bool × Par} {b : Block S ProofFile.Cl}
    (h : K4Here c Z Bs.G₀ 0 x b) (Fl : K4Fill Dm Ew Z c)
    {told : List (List VerifiableInference.Desc.Oracle)}
    (Sn : K4NamedW Dm Ew (28 * 0 + 4) (2 * 0) (parOf x) told (Forest.elems Xp.y.fo))
    (Pf : K4PinsFill Dm Z) (Pt : K4PinsTests Dm Ew Z (28 * 0 + 4) 0 (parOf x))
    (reqT : ReqTies (k4DataWide Dm Ew mgBase).reqB (k4DataWide Dm Ew mgBase).reqW
      (k4DataWide Dm Ew mgBase).H.req (k4DataWide Dm Ew mgBase).put)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (z : ProofFile.InstPub) :
    Nonempty (K4FirstAt (scl := sclX Xp 0) x linksFull (flatPlacesOf linksFull true)
      (28 * 0 + 4) (2 * 0) q (k4DataWide Dm Ew mgBase) (mgWide Dm Ew mgBase) z) :=
  firstAt_scope_at hS hR O hW Dm Ew (by decide) h Fl Sn Pf Pt reqT q z

/-- **The nine named equations, as one term, at the closed term.** -/
theorem pinsFill_const (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) {pq : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
      (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pq))
    (hs : Desc.K14.Law.fullShapeB
      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
    (lay : ByteArray)
    (hL : _root_.Meaning.laidThere (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp))
      (P5J.At.layout Zp) = true)
    (hN : SeatsNamed (P5J.At.arr Zp) (P5J.At.N Zp cF) (_root_.Meaning.sizesOf (P5J.At.X Zp))
      (_root_.Meaning.seatBy (_root_.Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp))
        (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp))))
    (hG : GroupsSeated (P5J.At.ms Zp lay) (P5J.At.N Zp cF)) (x : Place) (nR : ℕ) :
    K4PinsFill (asOurs o Zp Np cF E hs lay hL hN hG x nR) Zp where
  sent := q1_sent o Zp Np cF E hs lay hL hN hG x nR
  arr := q2_arr o Zp Np cF E hs lay hL hN hG x nR
  ms := ⟨P5J.At.rad Zp lay, q3_ms o Zp Np cF E hs lay hL hN hG x nR⟩
  nSent := q4_sent o Zp Np cF E hs lay hL hN hG x nR
  nIndex := q4_index o Zp Np cF E hs lay hL hN hG x nR
  seat3 := q6_seat3 o Zp Np cF E hs lay hL hN hG x nR
  hid := q5_hid o Zp Np cF E hs lay hL hN hG x nR
  mat13 := q10_mat13 o Zp Np cF E hs lay hL hN hG x nR
  uL := q11_uL o Zp Np cF E hs lay hL hN hG x nR

/-- **The three ties on the request's letters, at the closed term**, where the wider meaning's words
of the request are that term's own (`P5J.At.reqW`). -/
theorem reqTies_const (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) {pq : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
      (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pq))
    (hs : Desc.K14.Law.fullShapeB
      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
    (lay : ByteArray)
    (hL : _root_.Meaning.laidThere (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp))
      (P5J.At.layout Zp) = true)
    (hN : SeatsNamed (P5J.At.arr Zp) (P5J.At.N Zp cF) (_root_.Meaning.sizesOf (P5J.At.X Zp))
      (_root_.Meaning.seatBy (_root_.Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp))
        (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp))))
    (hG : GroupsSeated (P5J.At.ms Zp lay) (P5J.At.N Zp cF)) (x : Place) (nR : ℕ)
    (Ew : WideData ProofFile.InstPub)
    (hE : Ew.reqW = P5J.At.reqW) :
    ReqTies (k4DataWide (asOurs o Zp Np cF E hs lay hL hN hG x nR) Ew mgBase).reqB
      (k4DataWide (asOurs o Zp Np cF E hs lay hL hN hG x nR) Ew mgBase).reqW
      (k4DataWide (asOurs o Zp Np cF E hs lay hL hN hG x nR) Ew mgBase).H.req
      (k4DataWide (asOurs o Zp Np cF E hs lay hL hN hG x nR) Ew mgBase).put where
  words := fun z => by
    show Ew.reqW z = _
    rw [hE]
    rfl
  back := fun a r h => by
    show (_root_.Meaning.backReq (P5J.At.reqB a.1)).getD P5J.At.d₀ = r
    rw [show _root_.Meaning.backReq (P5J.At.reqB a.1) = some r from h]
    rfl
  put := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.reqTies_const
#print axioms OnBytes.Road.K4.firstAt_scope_at
#print axioms OnBytes.Road.K4.firstAt_wide_scope
#print axioms OnBytes.Road.K4.pinsFill_const
