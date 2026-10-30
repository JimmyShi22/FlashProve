-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLaterAtWide.lean: WHAT THE ASSEMBLY OF K4's LAW LEAVES AT A LATER GROUP (its
structure `K4LaterAt`, Johnson/Road/K4/K04LawOf.lean: ten letters and eight fields) AT THE DATA OFF
THE WIDER MEANING's OWN PARAMETERS (`k4DataWide 𝔇 E Mg₀`, Johnson/Road/K4/K4MeansAtWide.lean).
The binder forms is handed `PlaceIs` too. FOUR OF THE EIGHT FIELDS ARE CONCLUDED
(tiesM, rides, encIs, rwMat: K4PinsAtWide.lean) AND ONE LETTER IS MADE (the lookup's place:
`ties_of_plan`, K4PinsScope.lean); B, fit, mask AND forms STAY BINDERS, the last three asked at
every place with the segment's number as its link. A gathering of calls. No draw, no count.

  **`laterAt_atWide`**: `Nonempty (K4LaterAt x links ps k m q (k4DataWide 𝔇 E Mg₀) Mg hg z)`, from:
    `publicOf`'s return and six lines on the public parameters at segment m (as another of K4's
    files draws them in the goals' scope) · `RefPub` · FOUR NAMED EQUATIONS ON 𝔇's PARAMETERS (what
    𝔇.H reads off a witness · 𝔇.smp is `smpNamed` · the decoder does not read the verifier's state ·
    𝔇.mat13 is `matOfCells`) · fit, mask, forms.

THE LETTERS AS LAID: xL := the place made · enc := `Stored.entries`; posI, sz, seat, nM, nRr, nC,
nx, v7 stay the caller's.

OBJECT: `k4DataWide 𝔇 E Mg₀`. USER: Johnson/Road/K4/K4PinsLaterClosed.lean; meant: the top theorem
of K4's law at the wider meaning (its binder on the later groups). LETTERS: as named; Mg is free
(meant: `mgWide 𝔇 E mgBase`).

Limits. K04_law IS NOT PROVED BY THIS. fit (nine conditions on public letters: a closed test's yes
gives them at named terms), mask (a tie of two readers of one witness) AND forms (OF WEIGHT) ARE NOT
CONCLUDED HERE. NO MEMBER IS SHOWN: that the binders can hold together is shown at no parameters.
THE WIDER MEANING IS ONE SIDE OF A BRIDGE: a law shown at it counts only
when the bridge is paid.
-/
import Johnson.Road.K4.K04LawOf
import Johnson.Road.K4.K4PinsAtWide
import Johnson.Road.K4.K4PinsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model (Verify.publicOf)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open VerifiableInference.OnPublicFiles (LeftQ)
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place pubAt stepOf Stored.entries Stored.NoRec)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)
open Cb.Pv.Tail (Size)

variable [scl : Scl] {Fr : Frame} {Xi Tok : Type} {nR : ℕ} {X : Public}

/-- **`K4LaterAt` at the wider meaning's own parameters**. -/
theorem laterAt_atWide {pol KL : ByteArray} {layout : Option ByteArray}
    (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nR X) (E : WideData ProofFile.InstPub)
    (Mg₀ Mg : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)) (x : Bool × Par)
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k m : ℕ)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT))
    (hg : (parOf x).g < 12) (z : ProofFile.InstPub)
    (h : Verify.publicOf pol KL layout = .ok X) (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some (parOf x).hp) (h2 : m % 2 = 0)
    (hpc : VerifiableInference.Desc.K3.pieceAt X m false = 2) (hy : (parOf x).P.y = X.y)
    (B : RefPub X (parOf x).g) (posI : ℕ → Bool × ℕ × ℕ) (sz : ℕ → Size)
    (seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (nM nRr nC nx v7 : ℕ)
    (hH : ∀ w, (𝔇.H.hid w).MG (parOf x).g =
      _root_.Meaning.mgOf X.y (ownW 𝔇.arr 𝔇.ms 𝔇.N sz seat 𝔇.cs w) (parOf x).g)
    {seats : List (ℕ × ℕ)} (hsmp : 𝔇.smp = smpNamed 𝔇.cs seats) (hN : Stored.NoRec 𝔇.decT)
    (hm : 𝔇.mat13 = matOfCells nR 𝔇.P13.lin.kCol)
    (fit : ∀ xL : Place, xL.link = m → xL.ns = (parOf x).hp.ns → PlaceIs xL (parOf x) 0 →
      K4PlanFit (X := X) (p := parOf x) xL (pubAt X (m / stepOf X))
        (sentOf (k4DataWide 𝔇 E Mg₀)) (k4DataWide 𝔇 E Mg₀).L3.rad
        (fun j => (k4DataWide 𝔇 E Mg₀).L3.seat xL.link false j.1) posI
        (k4DataWide 𝔇 E Mg₀).L3.oW Stored.entries (k4DataWide 𝔇 E Mg₀).L3.wOf
        (k4DataWide 𝔇 E Mg₀).arr (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m nM nRr nC 0 sz
        seat (k4DataWide 𝔇 E Mg₀).hd)
    (mask : ∀ xL : Place, xL.link = m → xL.ns = (parOf x).hp.ns →
      ∀ (b : S × Fr.E.Str) w,
        onQ (k4DataWide 𝔇 E Mg₀).N Mg links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
        ((k4DataWide 𝔇 E Mg₀).rw13 (z, b.1) w).mask
            ⟨(k4DataWide 𝔇 E Mg₀).N.indexNo,
              Rec.nextNoP (k4DataWide 𝔇 E Mg₀).d12.M ((k4DataWide 𝔇 E Mg₀).N.msgsAt ps[k + 1]?)
                (k4DataWide 𝔇 E Mg₀).N.indexNo (k4DataWide 𝔇 E Mg₀).fvs m⟩ =
          (qkAt (k4DataWide 𝔇 E Mg₀) (parOf x) m xL posI Stored.entries nM nRr nC nx v7
            hg).toL.plan.full.msg
            (partOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).arr
              (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m w)
            (qkAt (k4DataWide 𝔇 E Mg₀) (parOf x) m xL posI Stored.entries nM nRr nC nx v7
              hg).toL.plan.full.c7)
    (forms : ∀ xL : Place, xL.link = m → xL.ns = (parOf x).hp.ns → PlaceIs xL (parOf x) 0 →
      ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ b w,
        ((qkAt (k4DataWide 𝔇 E Mg₀) (parOf x) m xL posI Stored.entries nM nRr nC nx v7
          hg).lettersOf (Fr := Fr)
          (partOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).arr
            (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m) (parOf x) 0 (parOf x).P.y.fo
          (LeftQ (parOf x).hp.ns) (tableOn0 (k4DataWide 𝔇 E Mg₀).N Mg z links ps k)
          (keptFrom (tableOn0 (k4DataWide 𝔇 E Mg₀).N Mg z links ps k) (parOf x) (twinOf q B'))
          (tableCtx0 (k4DataWide 𝔇 E Mg₀).N Mg z m)
          (decOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).G
            (k4DataWide 𝔇 E Mg₀).smp (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).decT
            (k4DataWide 𝔇 E Mg₀).N z m)).on' b →
        onQ (k4DataWide 𝔇 E Mg₀).N Mg links ps (fun s => (z, s)) (k + 1) b →
        b.1.failed = none →
        meansQ (Fr := Fr) (k4DataWide 𝔇 E Mg₀).N Mg (fun s => (z, s)) (.formsT m 3 "own") b w →
        FormsT seatS ((qkAt (k4DataWide 𝔇 E Mg₀) (parOf x) m xL posI Stored.entries nM nRr nC nx
          v7 hg).semOf
          (partOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).arr
            (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m) (parOf x).hp.tl)
          (frontRun (parOf x)) formsBack b.1 w) :
    Nonempty (K4LaterAt x links ps k m q (k4DataWide 𝔇 E Mg₀) Mg hg z) := by
  obtain ⟨xL, hl, hns, P0, hW⟩ :=
    ties_of_plan (k4DataWide 𝔇 E Mg₀).L3 (parOf x) h hn h0 hplan h2 hpc hy rfl rfl
  exact ⟨{
    xL := xL
    posI := posI
    enc := Stored.entries
    sz := sz
    seat := seat
    nM := nM
    nRr := nRr
    nC := nC
    nx := nx
    v7 := v7
    B := B
    tiesM := ties_wide 𝔇 E Mg₀ hW hH
    fit := fit xL hl hns P0
    rides := rides_wide 𝔇 E Mg₀ z hsmp hN
    encIs := encIs_wide 𝔇 E Mg₀
    rwMat := rwMat_wide 𝔇 E Mg₀ hm
    mask := mask xL hl hns
    forms := forms xL hl hns P0 }⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laterAt_atWide
