-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLaterScope.lean: WHAT THE ASSEMBLY OF K4's LAW LEAVES AT A LATER GROUP, IN THE
GOALS' SCOPE AT AN OPENING OF THE IOP AS WRITTEN IN LEAN: THE END IS THE CONSEQUENT OF THE
ASSEMBLY's BINDER ON THE LATER GROUPS, TO THE LETTER (`k04_law_at`, Johnson/Road/K4/K04LawAt.lean,
its binder LL). `laterAt_whole` (K4PinsLaterWhole.lean) called, with its some fifty binders drawn
from: the scope and the opening · the member of K4's lot (`K4Here`) · two structures of K4's files
(`K4Fill`: twelve lines on the composed meaning's parameters; `K4NamedW`: nine named tests) · AND
TWO STRUCTURES THAT STAND HERE: `K4PinsFill` (eight more named equations and one line) ·
`K4PinsTests` (six more tests) · `WrittenAt Z` (five parts of the public parameters are the written
values; Johnson/Road/K4/K4PlanTied.lean): from it the
common test and the seam's are THEOREMS (`common_paid`, `seam_paid`,
Johnson/Road/K4/K4PlanPaid.lean). `RefPub` is drawn inside (`refPub_in_scope`,
Johnson/Road/K4/RefInScope.lean). After the pattern of `k4Row_wide_scope`
(K4RowWideScope.lean) and of the last lines of `k4Row_of_means` (K4RowOfMeans.lean). A gathering of
calls. No draw, no count.

  `K4PinsFill Dm Z`: sent · arr · ms (at some radii) · N's sent · N's index · seat3 · hid (A LINE,
    NOT AN EQUATION OF TERMS: what Dm.H reads off a witness at a group is
    the seats' own reading: so the law hangs on no text of the term that gives it) · mat13 · uL.
  `K4PinsTests Dm Ew Z k g par`: `firstFastB` · `maskFitsB` · `indexTieB` · and, at
    every place with the segment's number as its link and the plan's number of slots: `maskPlanB` ·
    `arraysPlanB` · "the number of slots is at most the mask row's length".
  **`laterAt_wide_scope`**.

OBJECT: `k4DataWide Dm Ew mgBase`, `mgWide Dm Ew mgBase`. USER:
Johnson/Road/K4/K4PinsFirstScope.lean; meant: `k04_law_at`. LETTERS: as named; tokens := ℕ.

Limits. K04_law IS NOT PROVED BY THIS. `K4Fill`, `K4NamedW`, `K4PinsFill`, `K4PinsTests` AND
`WrittenAt` ARE PREMISES: SHOWN TOGETHER AT NO PARAMETERS: NO MEMBER IS SHOWN. IT SPEAKS AT THE
WIDER MEANING: it counts only when the bridge to the meaning that counts is paid. Three fields of
`K4PinsTests` are asked at every place of a kind, not as one closed test.
-/
import Johnson.Road.K4.K4PinsLaterWhole
import Johnson.Road.K4.K4RowAtWideScope
import Johnson.Road.K4.Rec.OpenNextWide
import Johnson.Road.K4.Rec.InTFour
import Johnson.Road.K4.RefInScope
import Johnson.Road.K4.K4PlanPaid

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

variable {Xi : Type} {nQ : ℕ} {X : Public}

/-- **Eight more named equations on the composed meaning's parameters, and one line.** -/
structure K4PinsFill (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ X) (Z : ProofFile.Pub) :
    Prop where
  sent : Dm.sent = sentAt Z
  arr : Dm.arr = arrAt Z
  ms : ∃ radM : ℕ → ℕ → ℕ, Dm.ms = P5T.msAtR Z radM
  nSent : Dm.N.sent = (numbersAt Z).sent
  nIndex : Dm.N.index = (numbersAt Z).index
  seat3 : ∀ l j, Dm.seat3 l false j = P6T.seatCallsT (seatsAt Z) (sentAt Z) l j
  hid : ∀ g w, (Dm.H.hid w).MG g =
    _root_.Meaning.mgOf X.y
      (ownW Dm.arr Dm.ms Dm.N (_root_.Meaning.sizesOf X)
        (seatBy (fLay (sentAt Z).layout (numAt Z)) X (_root_.Meaning.sizesOf X)) Dm.cs w) g
  mat13 : Dm.mat13 = matOfCells nQ Dm.P13.lin.kCol
  uL : Dm.uL = uLAt X (namesOf Dm.built)

/-- **Six more tests**, at border k and group g. -/
structure K4PinsTests (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ X)
    (Ew : WideData ProofFile.InstPub) (Z : ProofFile.Pub) (k g : ℕ) (par : Par) : Prop where
  first : firstFastB Z g = true
  maskFits : maskFitsB Dm.cs Ew.d12.M Ew.d12.L
    (Dm.N.msgsAt (flatPlacesOf linksFull true)[k + 1]?)
    (Dm.N.treesAt (flatPlacesOf linksFull true)[k + 1]?) Dm.N.indexNo
    (rowsBefore Ew.dP.fvs (2 * g)) = true
  indexTie : indexTieB Dm.cs Ew.d12.M Ew.d12.L.places Dm.ms Dm.N
    (rowsBefore Ew.dP.fvs (2 * g) + 1) = true
  maskPlan : ∀ xL : Place, xL.link = 2 * g → xL.ns = par.hp.ns →
    maskPlanB (pinAt (k4DataWide Dm Ew mgBase) xL (posFree (maskRowsAt Ew.d12.M Dm.N.indexNo))
      Stored.entries) ((k4DataWide Dm Ew mgBase).N.sent (2 * g) 0)
      (recPlanOf (k4DataWide Dm Ew mgBase) (k4DataWide Dm Ew mgBase).sd)
      ((k4DataWide Dm Ew mgBase).N.msgsAt (flatPlacesOf linksFull true)[k]?) (2 * g) = true
  arrays : ∀ xL : Place, xL.link = 2 * g → xL.ns = par.hp.ns →
    arraysPlanB (pinAt (k4DataWide Dm Ew mgBase) xL
      (posFree (maskRowsAt Ew.d12.M Dm.N.indexNo)) Stored.entries) par.hp.tl
      ((k4DataWide Dm Ew mgBase).N.sent (2 * g) 0)
      (recPlanOf (k4DataWide Dm Ew mgBase) (k4DataWide Dm Ew mgBase).sd)
      ((k4DataWide Dm Ew mgBase).N.msgsAt (flatPlacesOf linksFull true)[k]?) (2 * g) = true
  ell : ∀ xL : Place, xL.link = 2 * g → xL.ns = par.hp.ns →
    xL.ns ≤ maskEllP (pinAt (k4DataWide Dm Ew mgBase) xL
      (posFree (maskRowsAt Ew.d12.M Dm.N.indexNo)) Stored.entries)

variable {Fr : Frame} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In the goals' scope, at an opening: the assembly's structure for a later group has a member at
the wider meaning over the closed base.** -/
theorem laterAt_wide_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {Xp : Public}
    (hW : Bs.G₀.W = Xp) (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) {g : ℕ} (hg : g < 12) (hg0 : (g == 0) = false) {x : Bool × Par}
    {b : Block S ProofFile.Cl} (h : K4Here c Z Bs.G₀ g x b) (Fl : K4Fill Dm Ew Z c)
    {told : List (List VerifiableInference.Desc.Oracle)}
    (Sn : K4NamedW Dm Ew (28 * g + 4) (2 * g) (parOf x) told (Forest.elems Xp.y.fo))
    (Pf : K4PinsFill Dm Z) (Pt : K4PinsTests Dm Ew Z (28 * g + 4) g (parOf x))
    (W : WrittenAt Z)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (z : ProofFile.InstPub) :
    Nonempty (K4LaterAt (scl := sclX Xp g) x linksFull (flatPlacesOf linksFull true)
      (28 * g + 4) (2 * g) q (k4DataWide Dm Ew mgBase) (mgWide Dm Ew mgBase)
      (lt_of_eq_of_lt h.hg hg) z) := by
  have eX : Z.p.X = Xp := O.W.symm.trans hW
  subst eX
  have eg := h.hg
  subst eg
  have hpub : publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := hW ▸ O.public
  obtain ⟨k4, kN, _⟩ := _root_.Meaning.scope_plans hS hR hpub
  have Bp : RefPub Z.p.X x.2.g := refPub_in_scope hS hR hpub hg
  have C := Hd.core_of_scope hS hR hpub
  have hpos : 0 < x.2.g := Nat.pos_of_ne_zero (show x.2.g ≠ 0 by simpa using hg0)
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
  exact laterAt_whole (scl := sclX Z.p.X x.2.g) Z Dm Ew mgBase x radM linksFull
    (flatPlacesOf linksFull true) (28 * x.2.g + 4) q hg z
    hpos hpub Sx.notHead Sx.step Sx.plan
      Sx.pc2
    Sx.y k4 hGx (publicSteps_of hpub) Bp hP (common_paid W hpub C) Pt.first
    (seam_paid W hpub C hpos hg) Pf.sent Pf.arr Q3 Pf.nSent
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

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laterAt_wide_scope
