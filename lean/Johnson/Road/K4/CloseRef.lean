-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRef.lean: Johnson/Road/K4/CloseK5.lean's TOP AT ONE NAMED VALUE: the value at
the library's reference sizes (`refL`, Johnson/Road/K4/RefValue.lean) with its letters read off a
seat as `Plan4K` reads them (Johnson/Road/K4/ValueSeat.lean), at a public record X of which
`PublicSteps pol KL X` (Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean: the steps of the public part
that take no hash) holds, in a group that is not the first. THE TOP's PREMISES ON PUBLIC NUMBERS ARE
CONCLUDED FROM THESE STEPS AND ONE RECORD OF SENTENCES ON X, `RefPub X p.g`
(Johnson/Road/K4/RefPub.lean). A record, six definitions and four theorems. Glue: the statements of
RefValue.lean, MemberFront.lean, RefPub.lean, RefPubSteps.lean, RefPubStepsFront.lean laid into
`Plan4K.k04LawAt_K5`. No draw, no count.

  `RefSeat M T`: the letters that stay: the layout y; bounds on the matrices' numbers, rows and
  columns; how a tuple of messages is read as matrices (raw; the value reads 0 outside the bounds:
  `RefSeat.mats`), as the own mask row, as the committed matrix of weights and as the index-mask
  message; the seat; n0; a lower bound for ns; nx; v7.
  `RefSeat.toK`, `RefSeat.letters`, `RefSeat.toL_eq`: the value as a `Plan4K`; its letters as
  `RefLetters`; the two roads give one value (by unfolding).
  `nTX`, `nIX`, `RefSeat.atRec`: the two numbers of end values at a record and a place; the value
  there. `RefSeat.atRec_toL`. `RefSeat.meets`: `Plan4.Meets` holds of it.
  `RefSeat.k04LawAt_ref`: `K04LawAt U.L Sm Lt part p bk pc` at a piece whose errors are the cap.
  CONCLUDED INSIDE, from `PublicSteps`, `RefPub` and the premises on the place: `Meets` · C ·
  hk · `ValueIs` · `ValueMore` · the public lines · the rotary tables' fit · of `FrontIs` the lines
  fo, pub, ok · the matrices' zeros (by make). `FrontIs`' line n0 is the premise hn, handed through.

WHO PAYS `RefPub`: two theorems elsewhere: `refPub_of_tests` (RefPub.lean): from three computable
tests that say true and one equation of numbers: for a run · `refPub_in_scope`
(Johnson/Road/K4/RefInScope.lean): at all public files in the goals' scope, for every group below
12, with no test.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE: `PublicSteps pol KL X` (paid by
`publicSteps_of` where `publicOf` returns X, by `publicSteps_of_O` where `publicOfO o` does, at
every o) · `RefPub X p.g` · the section's table of scales is the record's · the place holds the
record's layers and the group's plan; g is not 0 and below 12 · the value's layout is the record's ·
the seat's two laws wherever the seat finds the lookup's return · pc.ds, pc.back, that the errors
are the cap · n0 is first + the number of elements that the lookup hears · THE PROMISE IN FRONT
GIVES `K3LeftAt` (Johnson/Top/H/K3LeftStatement.lean), AT THE SEAT's OWN READERS, AT THE PLAN's
SHAPE AND lmb, AND AT A LETTER Q3 THAT BOUNDS THE NUMBER OF SLOTS OF THE LEDGER IN FRONT OF THE
LOOKUP BY U.ns + 1 · EVERY LINE OF `LettersAre` · EVERY LINE OF `ReadsAre` (CloseReads.lean: the
reads are true by make, at the group's plan's numbers of the smallness test and the value's own
matrices) · kept · THE LINE ON `Lt.wo` (it gives the row's sentence `WoRow`, CloseK5.lean). Nothing
shows that these can be met together. The letters `Sem`, `Letters`, part, fe, Ex, nu, first, Q3 and
those of `RefSeat` are filled by nobody. The reference sizes alone. USER: `RefSeat.k04LawAt_refFill`
(CloseRefFill.lean).
-/
import Johnson.Road.K4.CloseK5
import Johnson.Road.K4.RefPubSteps
import Johnson.Road.K4.RefPubStepsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Layer (Lay nEndT)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters K04LawAt)
open VerifiableInference.OnPublicFiles (K3LeftAt)
open Inst.Model (Scl tbRef)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (Dim LW ref_chOK)

/-- The letters that stay at the reference sizes and a seat. -/
structure RefSeat (M T : Type) where
  y : Lay
  /-- bounds on the matrices' numbers, rows and columns; the messages as matrices -/
  nM : ℕ
  nR : ℕ
  nC : ℕ
  raw : M → Mats Cb.Gl.E
  maskAt : M → ℕ → Cb.Gl.E
  matAt : M → ℕ → ℕ → Cb.Gl.E
  idxAt : M → ℕ → Cb.Gl.E
  /-- how K4's text reads its part of the carried record -/
  L : Seat T
  n0 : ℕ
  ns : ℕ
  nx : ℕ
  v7 : ℕ

/-- The messages as matrices, read as 0 outside the bounds. -/
def RefSeat.mats {M T : Type} (U : RefSeat M T) (m : M) : Mats Cb.Gl.E := fun a b c =>
  if a < U.nM ∧ b < U.nR ∧ c < U.nC then U.raw m a b c else 0

variable [scl : Scl] {M T Wt Cl : Type} {Fr : Frame}

/-- The value at the reference sizes, its letters read off the seat. -/
noncomputable def RefSeat.toK (U : RefSeat M T) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    Plan4K M T where
  y := U.y
  D := Dim.ref
  tb := tbRef
  L0 := g * 4
  nM := U.nM
  nR := U.nR
  nC := U.nC
  mats := U.mats
  ns := max U.ns ((slotsAt Dim.ref U.n0 nT nI).f7 + 1 + (2 * kRef + 1))
  kW := kRef
  hW := hRef
  nx := U.nx
  maskAt := U.maskAt
  matAt := U.matAt
  idxAt := U.idxAt
  L := U.L
  n0 := U.n0
  nT := nT
  nI := nI
  v7 := U.v7
  numT := numA Dim.ref
  numI := num4 Dim.ref (numK Dim.ref)
  nW := nWK Dim.ref
  num := numK Dim.ref
  h5 := ref_h5
  h6 := ref_h6
  hfe := ref_hfe
  h0 := ref_h0 g
  hf := ref_hf
  hh := ref_hh
  hLay := ref_hLay hg
  hH := ref_hH

/-- The same letters in the form of RefValue.lean. -/
noncomputable def RefSeat.letters (U : RefSeat M T) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    RefLetters M T where
  Jc := Fin U.nM × Fin U.nR × Fin U.nC
  nameOf := (U.toK g hg nT nI).nameOf
  nx := U.nx
  cellAt := fun m j => U.mats m j.1 j.2.1 j.2.2
  maskAt := U.maskAt
  matAt := U.matAt
  idxAt := U.idxAt
  zOf := (U.toK g hg nT nI).toL.zOf
  kTg := (U.toK g hg nT nI).toL.kTg
  kIncS := (U.toK g hg nT nI).toL.kIncS
  n0 := U.n0
  ns := U.ns
  v7 := U.v7

/-- **The two roads give one value.** -/
theorem RefSeat.toL_eq (U : RefSeat M T) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    (U.toK g hg nT nI).toL = refL (U.letters g hg nT nI) g hg nT nI := rfl

/-- The number of the terms' end values at a record. -/
abbrev nTX (X : Public) : ℕ := nEndT X.layers.y

/-- The number of the batched sumcheck's end values at a record and a place. -/
abbrev nIX (X : Public) (p : Par) : ℕ :=
  2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))

/-- The value at a record and a place. -/
noncomputable abbrev RefSeat.atRec (U : RefSeat M T) (X : Public) (p : Par) (hg : p.g < 12) :
    Plan4K M T :=
  U.toK p.g hg (nTX X) (nIX X p)

theorem RefSeat.atRec_toL (U : RefSeat M T) (X : Public) (p : Par) (hg : p.g < 12) :
    (U.atRec X p hg).toL =
      refL (U.letters p.g hg (nTX X) (nIX X p)) p.g hg (nTX X) (nIX X p) := rfl

variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`Meets` holds of it**, at a record with `PublicSteps` and `RefPub`. -/
theorem RefSeat.meets (U : RefSeat M T) (hg : p.g < 12) (St : PublicSteps pol KL X)
    (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg0 : (p.g == 0) = false) :
    (U.atRec X p hg).toL.plan.Meets p (layerShape X.P) X.P.polCalls := by
  rw [U.atRec_toL]
  exact refS_meets _ hg St B hP hG hg0 _ _

/-- **`K04LawAt` at the reference value, at a seat, in a group that is not the first**, at a piece
whose errors are the cap: from `PublicSteps`, `RefPub`, the premises on the table of scales,
the place, the layout and the seat, the piece's rounds and back, that its errors are the cap, n0,
the bound on Q3, the promise's line, `LettersAre`, `ReadsAre`, kept and the line on `Lt.wo`. -/
theorem RefSeat.k04LawAt_ref (hscl : scl = sclX X p.g) (U : RefSeat M T) (hg : p.g < 12)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Sm : Sem Wt) (Lt : Letters T Wt Fr) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater p) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → M)
    (hback : pc.back = []) (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds))
    (lw : ℕ → LW Cb.Gl.E) {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (on : ∀ a, Lt.on a →
      K3LeftAt (fun s => some (U.L.fork s)) U.L.look p.P.y.fo p.P.y.h.lmb first Q3 a.1)
    (Ml : Plan4L.LettersAre (U.meets hg St B hP hG hg0) U.L Sm Lt Ex pc hds
      (fun a => (a.1, fe a)) part nu first)
    (R : ReadsAre p Sm nu p.hp.tl p.P.y.fo fun w => U.mats (part w))
    (kept : ∀ a τ fo o G, Lt.on a → Yes U.L p pc a τ fo o G → Lt.on' (behindOf U.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → U.L.own b.1 = some o → (U.atRec X p hg).WoRow p o (part w)) :
    K04LawAt U.L Sm Lt part p bk pc := by
  obtain ⟨s0, H, N⟩ := refS_frontIs (T := T) (Wt := Wt) (Fr := Fr)
    (U.letters p.g hg (nTX X) (nIX X p)) hg (nTX X) (nIX X p) St B hP hG
  have V : Plan4L.ValueIs (U.atRec X p hg).toL p (layerShape X.P) := by
    rw [U.atRec_toL]
    exact refS_valueIs hscl _ hg St B hP hG hg0
  have V2 : Plan4L.ValueMore (U.atRec X p hg).toL := by
    rw [U.atRec_toL]
    exact ref_valueMore _ _ hg _ _
  have hy' : (U.atRec X p hg).y = p.P.y := by
    rw [hP]
    exact hy
  exact (U.atRec X p hg).k04LawAt_K5 (U.meets hg St B hP hG hg0) Sm Lt Ex bk pc hds fe part hback
    hcap ref_chOK (fun l _ => refP_hk hscl B hG l) V V2 lw
    (fun F hF => Nat.le_trans (hQ F hF) (Nat.succ_le_succ (Nat.le_max_left _ _))) hy'
    (fun _ _ _ _ hb => if_neg hb) hseat H
    (fun a τ fo o G Y => refP_rope (U.letters p.g hg (nTX X) (nIX X p)) hg (nTX X) (nIX X p) B hP
      U.L pc a τ fo o G Y)
    Ml (N U.L Lt first Q3 hn on) R kept hwo

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.toL_eq
#print axioms OnBytes.Road.K4.RefSeat.meets
#print axioms OnBytes.Road.K4.RefSeat.k04LawAt_ref
