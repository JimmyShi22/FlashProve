-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLaterClosed.lean: `laterAt_atWide` (Johnson/Road/K4/K4PinsLaterAtWide.lean)
WITH TWO OF ITS BINDERS PAID BY CALLS (the line on what 𝔇.H reads off a witness is
asked as it is spent, so that the law hangs on no text of the term that gives it): fit, by
`fit_wide` (K4PinsFitAtWide.lean: three closed tests and six named equations on 𝔇's parameters);
mask, by `mask_wide` (K4PinsMaskAtWide.lean: other files' tie of two readers, with three tests). A
gathering of calls. No draw, no count.

  **`laterAt_closed`**: `Nonempty (K4LaterAt x links ps k (2 * g) q (k4DataWide 𝔇 E Mg₀) Mg hg z)`,
    at X := Zp.p.X, tokens := ℕ, from: `publicOf`'s return · five
    lines on the public parameters at segment 2 g · X.p4 = true · `PublicSteps` · `RefPub` · the two
    lines on the sub-protocol's parameters · SIX TESTS: `commonFastB Zp` · `firstFastB Zp g` ·
    `seamFastB Zp g` · `openMaskB` · `maskFitsB` · `indexTieB` · what four public items say at Mg ·
      NINE NAMED EQUATIONS ON 𝔇's PARAMETERS AND ONE LINE: sent · arr · ms · N's sent · N's index ·
      seat3 · the line on H.hid (what it reads off a witness at the group is the seats' own reading)
      · smp · "the decoder does not read the verifier's state" · mat13 · AND THE BINDER forms.

THE LETTERS AS LAID: xL := the place made · enc := `Stored.entries` · sz := `Meaning.sizesOf X` ·
seat := `seatBy (fLay (sentAt Zp).layout (numAt Zp)) X (sizesOf X)` · nM, nRr, nC := the least
bounds · posI := `posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)` · v7 := nx := `rowsBefore E.dP.fvs (2
g)`.

OBJECT: `k4DataWide 𝔇 E Mg₀`. USER: `laterAt_whole` (Johnson/Road/K4/K4PinsLaterWhole.lean).
LETTERS: as named; Mg is free (meant: `mgWide 𝔇 E mgBase`).

Limits. K04_law IS NOT PROVED BY THIS. forms (OF WEIGHT) IS NOT CONCLUDED. THE FOUR LINES ON Mg's
PUBLIC ITEMS SPEAK OF NAMES THAT HAVE LEFT THE MEANING THAT COUNTS. THE TEN ARE PREMISES:
by reading they hold by unfolding, or by a lemma of the composed meaning's files, at its
closed term: NO LEAN HAS MET THAT. (Where this and
lean/THEOREM.md differ, the page holds.) TWO LETTERS STAND FOR THE PUBLIC FILES: Pb (`publicOf`) and
Zp (what the tests and the equations read): NOTHING TIES THEM HERE BUT `publicOf`'s RETURN = Zp.p.X.
NO MEMBER IS SHOWN. THE WIDER MEANING IS ONE SIDE OF A BRIDGE: a law shown at it counts only when
the bridge is paid.
-/
import Johnson.Road.K4.K4PinsLaterAtWide
import Johnson.Road.K4.K4PinsFitAtWide
import Johnson.Road.K4.K4PinsMaskAtWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public publicOf)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open VerifiableInference.OnPublicFiles (LeftQ)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Wit Strs)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place szOf pubAt stepOf Stored.entries Stored.NoRec)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)
open Meaning (seatsOf seatBy fLay laidThere)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (EShapes EBook0 ESeats ECodes openMaskB maskFitsB)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

variable [scl : Scl] {Fr : Frame} {Xi : Type} {nR : ℕ} (Zp : ProofFile.Pub)
  (𝔇 : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nR Zp.p.X) (E : WideData ProofFile.InstPub)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT)) (x : Bool × Par)

/-- the data -/
local notation "𝐃" => k4DataWide 𝔇 E Mg₀
set_option quotPrecheck false in
/-- the seats of the symbols -/
local notation "𝐬" => seatBy (fLay (sentAt Zp).layout (numAt Zp)) Zp.p.X
  (_root_.Meaning.sizesOf Zp.p.X)

set_option quotPrecheck false in
/-- where the value reads the index masks -/
local notation "𝐩" => posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)
set_option quotPrecheck false in
/-- the number of the segment's entry of the index masks -/
local notation "𝐯" => rowsBefore E.dP.fvs (2 * (parOf x).g)

/-- **`K4LaterAt` at the wider meaning's own parameters**: fit, mask and the equation on H paid. -/
theorem laterAt_closed {Pb : VerifierAndGoals.PublicFiles} {ly : Option ByteArray}
    {tk : Array Nat} (radM : ℕ → ℕ → ℕ)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (hg : (parOf x).g < 12) (z : ProofFile.InstPub) (hg0 : 0 < (parOf x).g)
    (h : publicOf Pb.pol Pb.KL ly = .ok Zp.p.X)
    (hn : 2 * (parOf x).g ≠ (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr)
    (h0 : 2 * (parOf x).g % (if Zp.p.X.p4 then 2 else 1) = 0)
    (hplan : Zp.p.X.G[2 * (parOf x).g / (if Zp.p.X.p4 then 2 else 1)]? = some (parOf x).hp)
    (hpc : VerifiableInference.Desc.K3.pieceAt Zp.p.X (2 * (parOf x).g) false = 2)
    (hy : (parOf x).P.y = Zp.p.X.y) (h4 : Zp.p.X.p4 = true)
    (hG : Zp.p.X.G[(parOf x).g]? = some (parOf x).hp)
    (St' : PublicSteps Pb.pol Pb.KL Zp.p.X) (B : RefPub Zp.p.X (parOf x).g)
    (hP : (parOf x).P = { Zp.p.X.layers with tokv := tk })
    (hc : commonFastB Zp = true) (hf : firstFastB Zp (parOf x).g = true)
    (hm : seamFastB Zp (parOf x).g = true)
    (Q1 : 𝔇.sent = sentAt Zp) (Q2 : 𝔇.arr = arrAt Zp) (Q3 : 𝔇.ms = P5T.msAtR Zp radM)
    (Q4s : 𝔇.N.sent = (numbersAt Zp).sent) (Q4i : 𝔇.N.index = (numbersAt Zp).index)
    (Q6 : ∀ l j, 𝔇.seat3 l false j = P6T.seatCallsT (seatsAt Zp) (sentAt Zp) l j)
    (Q5 : ∀ w, (𝔇.H.hid w).MG (parOf x).g =
      _root_.Meaning.mgOf Zp.p.X.y
        (ownW 𝔇.arr 𝔇.ms 𝔇.N (_root_.Meaning.sizesOf Zp.p.X) (𝐬) 𝔇.cs w) (parOf x).g)
    {seats : List (ℕ × ℕ)} (Q7 : 𝔇.smp = smpNamed 𝔇.cs seats) (Q8 : Stored.NoRec 𝔇.decT)
    (Q10 : 𝔇.mat13 = matOfCells nR 𝔇.P13.lin.kCol)
    (eS : EShapes Mg E.d12.M) (eB : EBook0 Mg) (eSe : ESeats Mg E.d12.L) (eC : ECodes Mg 𝔇.cs)
    (hO : openMaskB Mg.more links ps (k + 1) = true)
    (hF : maskFitsB 𝔇.cs E.d12.M E.d12.L (𝔇.N.msgsAt ps[k + 1]?) (𝔇.N.treesAt ps[k + 1]?)
      𝔇.N.indexNo (𝐯) = true)
    (hT : indexTieB 𝔇.cs E.d12.M E.d12.L.places 𝔇.ms 𝔇.N (𝐯 + 1) = true)
    (forms : ∀ xL : Place, xL.link = 2 * (parOf x).g → xL.ns = (parOf x).hp.ns →
      PlaceIs xL (parOf x) 0 → ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ b w,
        ((qkAt (𝐃) (parOf x) (2 * (parOf x).g) xL (𝐩) Stored.entries (szOf (parOf x).hp.tl).NM
          ((Finset.range (szOf (parOf x).hp.tl).NM).sup (szOf (parOf x).hp.tl).m)
          ((Finset.range (szOf (parOf x).hp.tl).NM).sup (szOf (parOf x).hp.tl).k) (𝐯) (𝐯)
          hg).lettersOf (Fr := Fr)
          (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N (2 * (parOf x).g)) (parOf x) 0
          (parOf x).P.y.fo (LeftQ (parOf x).hp.ns) (tableOn0 (𝐃).N Mg z links ps k)
          (keptFrom (tableOn0 (𝐃).N Mg z links ps k) (parOf x) (twinOf q B'))
          (tableCtx0 (𝐃).N Mg z (2 * (parOf x).g))
          (decOf (sentOf (𝐃)).codes (𝐃).G (𝐃).smp (𝐃).ms (𝐃).decT (𝐃).N z
            (2 * (parOf x).g))).on' b →
        onQ (𝐃).N Mg links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
        meansQ (Fr := Fr) (𝐃).N Mg (fun s => (z, s)) (.formsT (2 * (parOf x).g) 3 "own") b w →
        FormsT seatS ((qkAt (𝐃) (parOf x) (2 * (parOf x).g) xL (𝐩) Stored.entries
          (szOf (parOf x).hp.tl).NM
          ((Finset.range (szOf (parOf x).hp.tl).NM).sup (szOf (parOf x).hp.tl).m)
          ((Finset.range (szOf (parOf x).hp.tl).NM).sup (szOf (parOf x).hp.tl).k) (𝐯) (𝐯)
          hg).semOf (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N (2 * (parOf x).g))
          (parOf x).hp.tl) (frontRun (parOf x)) formsBack b.1 w) :
    Nonempty (K4LaterAt x links ps k (2 * (parOf x).g) q (𝐃) Mg hg z) := by
  exact laterAt_atWide 𝔇 E Mg₀ Mg x links ps k (2 * (parOf x).g) q hg z h hn h0 hplan
    (Nat.mul_mod_right 2 _) hpc hy B (𝐩) (_root_.Meaning.sizesOf Zp.p.X) (𝐬) _ _ _ (𝐯) (𝐯) Q5 Q7 Q8
    Q10
    (fun xL hl _ P0 => fit_wide Zp radM 𝔇 E Mg₀ (parOf x) Q1 Q2 Q3 Q4s Q4i Q6 hc hf hm hg0 hg xL hl
      hG (𝐩) St' B hP P0 (group_at h4 _) hn)
    (fun xL _ _ => mask_wide 𝔇 E Mg₀ Mg z links ps k (2 * (parOf x).g) (parOf x) hg xL _ _ _ eS eB
      eSe eC hO hF hT)
    forms

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laterAt_closed
