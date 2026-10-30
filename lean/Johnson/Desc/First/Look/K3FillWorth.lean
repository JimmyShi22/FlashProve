-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3FillWorth.lean (over the layer cut in two): the kind
"lookup" (K3): ITS LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: THE FIELD worth, AND THE
WHOLE LAYER: worthK3 X D L f: what the items worth m pc "planes", "keys", "rider" say at K3's own
pieces, over whatever f says elsewhere; fillK3All X D L Mg: the layer with pub, pubP (fillK3,
Johnson/Desc/First/Look/K3Fill.lean) and worth; fillK3Wide X D L Mg: the thin layer for the door's
name «frame.liveIs» (fillK3Live) laid over it. And, AT THAT TERM, FOR EVERY Mg, the premises of the
lookups' row theorems that speak of worth, as lemmas. NO SOUNDNESS IS CLAIMED.

Main names.
  K3Letters: what the field reads beside X and D: rad (a message's radius) · arr (where an array's
    entries lie) · seat (link, sort of lookup, member's number ↦ tree and tenant: AT THE CALLS THE
    MEMBER's NUMBER RUNS OVER THE KEPT MESSAGES FIRST, THEN THE LINK's OWN OF MOMENT 0; at the
    digits over the link's own messages) · the stored table's five at a layers' link (oW, wOf, nr,
    nc, msgW).
  worthK3: by the sort of the piece (k3SortAt): on the digits, at digAt X m's (x, tl):
    K3WorthPlanes, K3WorthKeys (Johnson/Top/H/K3Worth.lean) at digNu, digMu · on the calls, at attAt
    X m's (x, A, tl): attWorthPlanes, attWorthKeys, attWorthRider (K3CallsTies.lean); else at layAt
    X m's x, tlAt X m's tl and pubAt X (m / stepOf X): layWorthPlanes, layWorthKeys, layWorthRider
    (K3LayTies.lean) · everywhere else, the head's calls among it: f.
  fillK3Worth, fillK3All, fillK3Wide; fillAll_pub, fillAll_pubP, fillAll_more · fillWide_more,
    fillWide_worth, fillWide_pubP: by rfl.
  THE ROWS' PREMISES AT THE TERM: fPl_fill, fKe_fill (the digits) · attP_fill, attK_fill, attR_fill
    · layP_fill, layK_fill, layR_fill.
  worth_other: at a piece that is none of K3's the field is left as it was.
OBJECT. No block's text: Meaning.worth (Johnson/Desc/First/Borders.lean) at the lookups' own
definitions.
USER. fillK3All: fillK3Both (Johnson/Desc/Sound/MgAll.lean) lays it in the composed meaning mgAll;
k3At_fill (K3At.lean). fillK3Wide: k3At_wide and k3AtLive_fill (K3At.lean) alone. Of this file's
theorems other files call fillAll_worth, worth_at_digits, worth_at_att and worth_at_lay alone: THE
ROWS' PREMISES AT THE TERM (fPl_fill … layR_fill) have no caller.
LETTERS. X, D, L, Mg.
IS IT EMPTY? Props on a witness: nothing to run. WHERE THE RECORD HOLDS NO LEDGER OR NOTHING HEARD
EACH ITEM IS TRUE OF EVERY WITNESS (K3Worth.lean's own limit).

Compiled with the whole library.
Limits. L IS A LETTER: which seats, which radius, which arr are meant is said nowhere here. The
layers' lemmas take hna (attAt X m = none) as a premise. The head's calls: not filled here (their
layer: fillK3Head, K3HeadFill.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.First.Look.K3CallsTies
import Johnson.Desc.First.Look.K3LayTies
import Johnson.Desc.First.Look.K3AttInst
import Johnson.Desc.First.Look.K3CallerMeans
import Johnson.Desc.First.Look.K3CallerLayTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)

/-- **What the field worth reads beside the public record and the plan's data.** -/
structure K3Letters (Cells Tok : Type) where
  /-- a message's radius -/
  rad : OracleShape → ℕ
  /-- where an array's entries lie -/
  arr : ℕ → ℕ → ℕ
  /-- link, sort of lookup (true: on the digits), member's number: its tree and tenant. AT THE CALLS
  THE NUMBER RUNS OVER THE KEPT MESSAGES FIRST, THEN THE LINK's OWN OF MOMENT 0 -/
  seat : ℕ → Bool → ℕ → ℕ × ℕ
  /-- the stored table's message, at a layers' link -/
  oW : Cb.OMsg Cb.Gl.E
  wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E
  nr : ℕ
  nc : ℕ
  msgW : Desc.Wit Cells Tok MsgT → oW.Msg

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok)

/-- The ledger's reader and the two seats' readers of what was heard. -/
abbrev forkR : Desc.First.S → Option Fork := fun s => s.fork?
abbrev heardD : Desc.First.S → Option Forest.Heard := fun s => s.tl?.bind (·.heard)
abbrev heardC : Desc.First.S → Option Forest.Heard := fun s => s.lookHeard?

/-- The digits' arm. -/
def worthDig (x : Desc.First.Look.Place) (tl : HTailF2) (r : String) (s : Desc.First.S)
    (w : Desc.Wit Cells Tok MsgT) (els : Prop) : Prop :=
  if r = "planes" then
    K3WorthPlanes forkR heardD tl.f9 5 x.F.next
      (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr) s w
  else if r = "keys" then
    K3WorthKeys forkR heardD tl.f9 5 x.F.next
      (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr)
      (fun w => forK Cb.Gl.E (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
        (zext (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w))) s w
  else els

/-- Attention's arm. -/
def worthAtt (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2) (r : String)
    (s : Desc.First.S) (w : Desc.Wit Cells Tok MsgT) (els : Prop) : Prop :=
  if r = "planes" then
    attWorthPlanes x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w
  else if r = "keys" then
    attWorthKeys x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w
  else if r = "rider" then
    attWorthRider x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w
  else els

/-- The layers' arm. -/
def worthLay (x : Desc.First.Look.Place) (q : LayPub) (tl : HTailF2) (r : String)
    (s : Desc.First.S) (w : Desc.Wit Cells Tok MsgT) (els : Prop) : Prop :=
  if r = "planes" then
    layWorthPlanes x q tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
      L.msgW forkR heardC s w
  else if r = "keys" then
    layWorthKeys x q tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
      L.msgW forkR heardC s w
  else if r = "rider" then
    layWorthRider x q tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
      L.msgW forkR heardC s w
  else els

/-- **THE FIELD worth AT K3's PIECES**, over whatever says it elsewhere. -/
def worthK3
    (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop) :
    ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop :=
  fun m pc r a y w =>
    match k3SortAt X m pc with
    | some true =>
      match digAt X m with
      | some v => worthDig D L v.1 v.2 r a.2 w (f m pc r a y w)
      | none => f m pc r a y w
    | some false =>
      match attAt X m with
      | some v => worthAtt D L v.1 v.2.1 v.2.2 r a.2 w (f m pc r a y w)
      | none =>
        match layAt X m, tlAt X m with
        | some x, some tl =>
          worthLay D L x (pubAt X (m / Desc.First.Look.stepOf X)) tl r a.2 w (f m pc r a y w)
        | _, _ => f m pc r a y w
    | none => f m pc r a y w

variable (Mg : Meaning P (Desc.Wit Cells Tok MsgT))

/-- The field's layer. -/
def fillK3Worth : Meaning P (Desc.Wit Cells Tok MsgT) :=
  { Mg with worth := worthK3 X D L Mg.worth }

/-- **K3's WHOLE LAYER** (without the door's name "frame.liveIs"). -/
def fillK3All : Meaning P (Desc.Wit Cells Tok MsgT) := fillK3Worth X D L (fillK3 X D Mg)

/-- **THE WIDER TERM**: the thin layer for that name laid over it. -/
def fillK3Wide : Meaning P (Desc.Wit Cells Tok MsgT) := fillK3Live X D (fillK3All X D L Mg)

theorem fillWide_more : (fillK3Wide X D L Mg).more = Mg.more.merge liveMore := rfl

theorem fillWide_worth : (fillK3Wide X D L Mg).worth = worthK3 X D L Mg.worth := rfl

theorem fillWide_pubP : (fillK3Wide X D L Mg).pubP = (fillK3 X D Mg).pubP := rfl

theorem fillAll_pub : (fillK3All X D L Mg).pub = pubK3 (K3Data.of X D) Mg.pub := rfl

theorem fillAll_pubP : (fillK3All X D L Mg).pubP = (fillK3 X D Mg).pubP := rfl

theorem fillAll_more : (fillK3All X D L Mg).more = Mg.more := rfl

theorem fillAll_worth : (fillK3All X D L Mg).worth = worthK3 X D L Mg.worth := rfl

/-- At a piece that is none of K3's the field is left as it was. -/
theorem worth_other (m pc : ℕ) (h : k3SortAt X m pc = none) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L Mg).worth m pc r a y w = Mg.worth m pc r a y w := by
  show worthK3 X D L Mg.worth m pc r a y w = _
  unfold worthK3
  rw [h]

/-! ## The arms at their places -/

theorem worth_at_digits (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m true) r a y w =
      worthDig D L x tl r a.2 w (Mg.worth m (Desc.K3.pieceAt X m true) r a y w) := by
  show worthK3 X D L Mg.worth m _ r a y w = _
  unfold worthK3
  rw [sort_digits, hx]

theorem worth_at_att (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X m = some (x, A, tl)) (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) r a y w =
      worthAtt D L x A tl r a.2 w (Mg.worth m (Desc.K3.pieceAt X m false) r a y w) := by
  show worthK3 X D L Mg.worth m _ r a y w = _
  unfold worthK3
  rw [sort_calls, hx]

theorem worth_at_lay (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt X m = none) (hx : layAt X m = some x) (ht : tlAt X m = some tl) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) r a y w =
      worthLay D L x (pubAt X (m / Desc.First.Look.stepOf X)) tl r a.2 w
        (Mg.worth m (Desc.K3.pieceAt X m false) r a y w) := by
  show worthK3 X D L Mg.worth m _ r a y w = _
  unfold worthK3
  rw [sort_calls, hna, hx, ht]

/-! ## The rows' premises at the term -/

/-- **fPl.** -/
theorem fPl_fill {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w) :
    ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutPlanes tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F' := by
  rw [worth_at_digits X D L Mg m hx] at h
  unfold worthDig at h
  rw [if_pos rfl] at h
  exact h

/-- **fKe.** -/
theorem fKe_fill {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X m = some (x, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w) :
    ∀ g F', (Desc.K3.seatDigits claim).fork s = some F' →
      (Desc.K3.seatDigits claim).heard s = some g →
      K3OutKeys tl.f9 5 x.F.next
        (digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w)
        (forK Cb.Gl.E (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
          (zext (digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w))) Reading.gl g F' := by
  rw [worth_at_digits X D L Mg m hx] at h
  unfold worthDig at h
  rw [if_neg (by decide), if_pos rfl] at h
  exact h

/-- **worthP, worthK, worthR at attention.** -/
theorem attP_fill (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X m = some (x, A, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "planes" (z, s) y w) :
    attWorthPlanes x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w := by
  rw [worth_at_att X D L Mg m hx] at h
  unfold worthAtt at h
  rw [if_pos rfl] at h
  exact h

theorem attK_fill (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X m = some (x, A, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "keys" (z, s) y w) :
    attWorthKeys x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w := by
  rw [worth_at_att X D L Mg m hx] at h
  unfold worthAtt at h
  rw [if_neg (by decide), if_pos rfl] at h
  exact h

theorem attR_fill (m : ℕ) {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
    (hx : attAt X m = some (x, A, tl)) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "rider" (z, s) y w) :
    attWorthRider x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr forkR heardC s w := by
  rw [worth_at_att X D L Mg m hx] at h
  unfold worthAtt at h
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
  exact h

/-- **The like at the layers.** -/
theorem layP_fill (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
    (hx : layAt X m = some x) (ht : tlAt X m = some tl) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "planes" (z, s) y w) :
    layWorthPlanes x (pubAt X (m / Desc.First.Look.stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc
      (fun j => L.seat x.link false j.1) L.arr L.msgW forkR heardC s w := by
  rw [worth_at_lay X D L Mg m hna hx ht] at h
  unfold worthLay at h
  rw [if_pos rfl] at h
  exact h

theorem layK_fill (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
    (hx : layAt X m = some x) (ht : tlAt X m = some tl) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "keys" (z, s) y w) :
    layWorthKeys x (pubAt X (m / Desc.First.Look.stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc
      (fun j => L.seat x.link false j.1) L.arr L.msgW forkR heardC s w := by
  rw [worth_at_lay X D L Mg m hna hx ht] at h
  unfold worthLay at h
  rw [if_neg (by decide), if_pos rfl] at h
  exact h

theorem layR_fill (m : ℕ) {x : Desc.First.Look.Place} {tl : HTailF2} (hna : attAt X m = none)
    (hx : layAt X m = some x) (ht : tlAt X m = some tl) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3All X D L Mg).worth m (Desc.K3.pieceAt X m false) "rider" (z, s) y w) :
    layWorthRider x (pubAt X (m / Desc.First.Look.stepOf X)) tl D L.rad L.oW L.wOf L.nr L.nc
      (fun j => L.seat x.link false j.1) L.arr L.msgW forkR heardC s w := by
  rw [worth_at_lay X D L Mg m hna hx ht] at h
  unfold worthLay at h
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
  exact h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.fillAll_pub
#print axioms VerifiableInference.OnPublicFiles.worth_other
#print axioms VerifiableInference.OnPublicFiles.fPl_fill
#print axioms VerifiableInference.OnPublicFiles.fKe_fill
#print axioms VerifiableInference.OnPublicFiles.attP_fill
#print axioms VerifiableInference.OnPublicFiles.attK_fill
#print axioms VerifiableInference.OnPublicFiles.attR_fill
#print axioms VerifiableInference.OnPublicFiles.layP_fill
#print axioms VerifiableInference.OnPublicFiles.layK_fill
#print axioms VerifiableInference.OnPublicFiles.layR_fill
