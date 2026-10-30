-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAllAt.lean: WHAT THE COMPOSED MEANING `mgAll` (Johnson/Desc/Sound/MgAll.lean)
SAYS IN ITS FIELD worth AT EACH OF THE LOOKUPS' PIECES, NAME BY NAME, THE OWNER's OWN SENTENCE ON
THE RIGHT; and its field more, written out. Statements and proofs.

Why. A kind's law is counted at the composed meaning; its premises on worth are stated at a letter.
These lemmas are those premises' left sides at the composed term.
  `mgAll_worth_dig_planes`, `_keys`: at the lookup on the digits (where `digAt` gives a place).
  `mgAll_worth_att_planes`, `_keys`, `_rider`: at the calls of an attention segment (`attAt`).
  `mgAll_worth_lay_planes`, `_keys`, `_rider`: at the calls of a layers' segment (where `attAt`
    gives nothing; `layAt`, `tlAt`).
  `mgAll_worth_head_planes`, `_keys`, `_rider`: at the head's calls (where `headAt` gives a place;
    segment `headLink`, piece 3):
    UNDER THE GUARD "the witness's cells are in range" in front of the sentence.
  NO RIGHT SIDE NAMES THE LETTER Mg: each arm's "else" (a name that is none of the three) has no
    lemma.
  `mgAll_more_merges`: the field more is the parts' merges over Mg.more, in the parts' order, with
    the names that leave struck.
  `mgMore`, `mgAll_more_closed`: the closed term, where Mg.more is the empty filling.
  `mgMore_start`: it lays nothing open at the chain's start.

Limits. Equations of sentences: nothing on whether a sentence holds. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First (Meaning More rowMore leavesName)
open VerifiableInference.Desc.K13.Law (wSitsMore)
open VerifiableInference.Desc.First.FillSent (sentMore sent1More)
open VerifiableInference.Desc.First.FillBare (leftMore)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-! ## 1 worth, by (segment, piece) and name -/

/-- The lookup on the digits. -/
theorem mgAll_worth_dig_planes (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m true) "planes" a y w =
      K3WorthPlanes forkR heardD tl.f9 5 x.F.next
        (digNu x tl 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr) a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "planes" a y w = _
  rw [worth_at_digits X 𝔇.sent 𝔇.l3 _ m hx]
  unfold worthDig
  rw [if_pos rfl]

theorem mgAll_worth_dig_keys (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m true) "keys" a y w =
      K3WorthKeys forkR heardD tl.f9 5 x.F.next
        (digNu x tl 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr)
        (fun w => forK Cb.Gl.E
          (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr w)))
        a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "keys" a y w = _
  rw [worth_at_digits X 𝔇.sent 𝔇.l3 _ m hx]
  unfold worthDig
  rw [if_neg (by decide), if_pos rfl]

/-- The lookup on the calls, at an attention segment. -/
theorem mgAll_worth_att_planes (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape}
    {tl : HTailF2} (hx : attAt X m = some (x, A, tl)) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "planes" a y w =
      attWorthPlanes x A tl 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr forkR
        heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "planes" a y w = _
  rw [worth_at_att X 𝔇.sent 𝔇.l3 _ m hx]
  unfold worthAtt
  rw [if_pos rfl]

theorem mgAll_worth_att_keys (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape}
    {tl : HTailF2} (hx : attAt X m = some (x, A, tl)) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "keys" a y w =
      attWorthKeys x A tl 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr forkR
        heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "keys" a y w = _
  rw [worth_at_att X 𝔇.sent 𝔇.l3 _ m hx]
  unfold worthAtt
  rw [if_neg (by decide), if_pos rfl]

theorem mgAll_worth_att_rider (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape}
    {tl : HTailF2} (hx : attAt X m = some (x, A, tl)) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "rider" a y w =
      attWorthRider x A tl 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr forkR
        heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "rider" a y w = _
  rw [worth_at_att X 𝔇.sent 𝔇.l3 _ m hx]
  unfold worthAtt
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The lookup on the calls, at a layers' segment. -/
theorem mgAll_worth_lay_planes (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt X m = none) (hx : layAt X m = some x) (ht : tlAt X m = some tl)
    (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "planes" a y w =
      layWorthPlanes x (pubAt X (m / Desc.First.Look.stepOf X)) tl 𝔇.sent 𝔇.l3.rad
        𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
        𝔇.l3.msgW forkR heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "planes" a y w = _
  rw [worth_at_lay X 𝔇.sent 𝔇.l3 _ m hna hx ht]
  unfold worthLay
  rw [if_pos rfl]

theorem mgAll_worth_lay_keys (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt X m = none) (hx : layAt X m = some x) (ht : tlAt X m = some tl)
    (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "keys" a y w =
      layWorthKeys x (pubAt X (m / Desc.First.Look.stepOf X)) tl 𝔇.sent 𝔇.l3.rad
        𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
        𝔇.l3.msgW forkR heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "keys" a y w = _
  rw [worth_at_lay X 𝔇.sent 𝔇.l3 _ m hna hx ht]
  unfold worthLay
  rw [if_neg (by decide), if_pos rfl]

theorem mgAll_worth_lay_rider (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt X m = none) (hx : layAt X m = some x) (ht : tlAt X m = some tl)
    (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth m (Desc.K3.pieceAt X m false) "rider" a y w =
      layWorthRider x (pubAt X (m / Desc.First.Look.stepOf X)) tl 𝔇.sent 𝔇.l3.rad
        𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
        𝔇.l3.msgW forkR heardC a.2 w := by
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 _).worth m _ "rider" a y w = _
  rw [worth_at_lay X 𝔇.sent 𝔇.l3 _ m hna hx ht]
  unfold worthLay
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The lookup on the calls, at the head's segment. -/
theorem mgAll_worth_head_planes {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth (headLink X) 3 "planes" a y w =
      (VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
       letI := k3SizesAt X
       letI := k3PolicyAt X
       letI := 𝔇.rq a.1
       K3WorthPlanes forkR heardC x.fs x.lm x.F.next
        (headNu (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc
          (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr 𝔇.l3.msgW) a.2 w) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 (fillK3HeadG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq
    (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells) Mg)).worth
    (headLink X) 3 "planes" a y w = _
  rw [fillAll_over_headG, worth_at_headG, worth_at_head X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq Mg hx]
  unfold worthHead
  rw [if_pos rfl]

theorem mgAll_worth_head_keys {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth (headLink X) 3 "keys" a y w =
      (VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
       letI := k3SizesAt X
       letI := k3PolicyAt X
       letI := 𝔇.rq a.1
       ∀ g F', forkR a.2 = some F' → heardC a.2 = some g →
        K3OutKeys x.fs x.lm x.F.next
        (headNu (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc
          (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr 𝔇.l3.msgW w)
        (forK Cb.Gl.E (headLay (k3AdrAt X) x.fs x.lm x.F.next x.ns X.H.tl 𝔇.l3.nr 𝔇.l3.nc)
          (a.2.replyTok?.getD 0)
          (zext (layMu x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc
            (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr 𝔇.l3.msgW w))) Reading.gl g F') := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 (fillK3HeadG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq
    (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells) Mg)).worth
    (headLink X) 3 "keys" a y w = _
  rw [fillAll_over_headG, worth_at_headG, worth_at_head X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq Mg hx]
  unfold worthHead
  rw [if_neg (by decide), if_pos rfl]

theorem mgAll_worth_head_rider {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (a : P × First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).worth (headLink X) 3 "rider" a y w =
      (VerifiableInference.OnPublicFiles.Flat.InRange w.cells →
       letI := k3SizesAt X
       letI := k3PolicyAt X
       letI := 𝔇.rq a.1
       ∀ g F', forkR a.2 = some F' → heardC a.2 = some g →
        K3OutRider
          (headRider (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr 𝔇.l3.nc extNone
            Unit) x.lm x.F.next (a.2.replyTok?.getD 0)
          (layMs x 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
            𝔇.l3.msgW w)
          g F') := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  rw [mgAll_worth]
  show (fillK3All X 𝔇.sent 𝔇.l3 (fillK3HeadG X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq
    (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells) Mg)).worth
    (headLink X) 3 "rider" a y w = _
  rw [fillAll_over_headG, worth_at_headG, worth_at_head X 𝔇.sent 𝔇.l3 (k3AdrAt X) 𝔇.rq Mg hx]
  unfold worthHead
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-! ## 2 more -/

/-- **The parts' merges, in the parts' order**, from the innermost; then the names that leave are
struck (`First.leavesName`, Johnson/Desc/First/SmallDoor.lean). -/
theorem mgAll_more_merges : (mgAll 𝔇 Mg).more =
    ((((((Mg.more.merge rowMore).merge leftMore).merge sent1More).merge sentMore).merge
      H2K5.Door.more).merge wSitsMore).strike leavesName := rfl

/-- **The closed term.** -/
def mgMore : More :=
  ((((((({} : More).merge rowMore).merge leftMore).merge sent1More).merge sentMore).merge
      H2K5.Door.more).merge wSitsMore).strike leavesName

theorem mgAll_more_closed (h : Mg.more = {}) : (mgAll 𝔇 Mg).more = mgMore := by
  rw [mgAll_more_merges, h]
  rfl

/-- The closed term lays nothing open at the chain's start. -/
theorem mgMore_start : mgMore.start = [] := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgAll_worth_dig_planes
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_dig_keys
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_att_planes
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_att_keys
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_att_rider
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_lay_planes
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_lay_keys
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_lay_rider
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_head_planes
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_head_keys
#print axioms VerifiableInference.Desc.Sound.mgAll_worth_head_rider
#print axioms VerifiableInference.Desc.Sound.mgAll_more_merges
#print axioms VerifiableInference.Desc.Sound.mgAll_more_closed
#print axioms VerifiableInference.Desc.Sound.mgMore_start
