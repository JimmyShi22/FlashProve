-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WoMaskTie.lean: THE LAST TIE OF THE LINE wo OF K4's ROW: TWO READERS OF ONE WITNESS
MEET. The premise hmask of `k4Lines_wo_at` (Johnson/Road/K4/K4LinesWo.lean), in its own form, at the
reader that is meant for the rows on the committed table of weights (`rwBook arr mat`,
Johnson/Desc/K13/Law/ReaderByBook.lean): at every unmarked statement b inside the promise at a
border and every witness w:
  `(rwBook arr mat (Z, b.1) w).mask ⟨N.indexNo, nextNoP …⟩ = QK.toL.plan.full.msg (part w) c7`.
A statement as a definition of a Prop, and its proof: a joining.
THE TWO SIDES. LEFT: `maskEntryIs` (Johnson/Road/K4/Rec/MaskEntry.lean): the entry is
`w.tab cs sh (arr q.1 q.2) q.1 q.2 true (k % sh.maskRows) (k / sh.maskRows)`: k: the number of the
segments in front that leave a row; sh, q: the shape and the seat that the public parameters have at
the index masks' number. RIGHT: `Plan4.msg_c7` (Johnson/Road/K4/ValueMasks.lean): the value's
message at c7 is its letter idxAt at v7, where v7 ≤ nx. BOTH END IN THE ONE ACCESSOR `Wit.tab`.
Main names:
  `tab_of_mem`: a member's table (`memTab`, Johnson/Desc/Sound/World.lean) is `Wit.tab` at the
    member's shape and seat.
  `WoMaskTies`: **THE TIES ON PUBLIC LETTERS UNDER WHICH THE TWO MEET**, as one Lean structure:
    inNx: v7 ≤ nx · shape, seat: a member u has the shape sh and the seat q · place: THE PLACE AT
    WHICH THE VALUE READS ITS ENTRY v7 OF THE INDEX MASKS IS THE MASK TABLE's ROW k % maskRows,
    PLACE k / maskRows: the k-th free entry (`Fmt.Places.freeAt`).
  `OwedWoMaskTie`, `woMaskTie`: the statement. hidx: what `idx_of_fit`
    (Johnson/Road/K4/K4PinsIndex.lean) hands at j := v7, in its own form, where the value's idxAt is
    `A.idx N` and part is `partOf cs arr ms N m`: taken as a premise, so that this file stands
    beneath that file's cone.
What is not claimed. `WoMaskTies` and hidx are premises: `place` IS ASKED OF posI BY NOBODY ELSE;
where posI v7 is another place the two readers read two entries of one table, and hmask is false at
a witness that parts them. What Johnson/Road/K4/Rec/MaskEntryStatement.lean says is not claimed.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.Rec.MaskEntry
import Johnson.Road.K4.ValueSeat
import Johnson.Road.K4.ValueMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Slice
open Inst.Model (Scl)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.K13.Law (rwBook)
open VerifiableInference.Desc.Sound (Frame MsgT Mem onQ memTab seatOf)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (LaidP EShapes EBook0 ESeats ECodes openMaskB maskFitsB nextNoP
  maskEntryIs)

/-- A member's table is the one accessor at the member's shape and seat. -/
theorem tab_of_mem {Cells Tok : Type} (cs : Codes) (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT)
    (u : Mem) (sh : OracleShape) (q : ℕ × ℕ) (hsh : (u.1.l.get u.2).1 = sh) (hq : seatOf u = q) :
    memTab cs arr w u = w.tab cs sh (arr q.1 q.2) q.1 q.2 := by
  subst hsh hq
  rfl

variable [scl : Scl]

/-- **The ties on public letters under which the two readers meet.** k: how many entries of the
index masks' message are taken in front. pos: where the value reads its entry v7. -/
structure WoMaskTies {Mm : Type} (QK : Plan4K Mm S) (u : Mem) (sh : OracleShape) (q : ℕ × ℕ)
    (pos : Bool × ℕ × ℕ) (k : ℕ) : Prop where
  inNx : QK.toL.plan.v7 ≤ QK.toL.plan.nx
  shape : (u.1.l.get u.2).1 = sh
  seat : seatOf u = q
  place : pos = (true, k % sh.maskRows, k / sh.maskRows)

/-- **OWED.** hmask, in its own form, at the reader through the verifier's state's own book. -/
def OwedWoMaskTie : Prop :=
  ∀ {P Cells Tok Mm : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (Z : P)
    (links : List ModelPart) (ps : List Place) (j m : ℕ) (M : List OracleShape) (L : LaidP) (cs : Codes)
    (fvs : List Bool) (sh : OracleShape) (q : ℕ × ℕ) (QK : Plan4K Mm S)
    (part : Wit Cells Tok MsgT → Mm) (u : Mem) (pos : Bool × ℕ × ℕ) (nR kC : ℕ)
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE),
    EShapes Mg M → EBook0 Mg → ESeats Mg L → ECodes Mg cs →
    openMaskB Mg.more links ps j = true →
    maskFitsB cs M L (N.msgsAt ps[j]?) (N.treesAt ps[j]?) N.indexNo (rowsBefore fvs m) = true →
    M[N.indexNo]? = some sh → L.places[N.indexNo]? = some q →
    WoMaskTies QK u sh q pos (rowsBefore fvs m) →
    (∀ w, QK.toL.plan.idxAt (part w) QK.toL.plan.v7 = memTab cs arr w u pos.1 pos.2.1 pos.2.2) →
    ∀ (b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (Z, s)) j b → b.1.failed = none →
      (rwBook arr mat (Z, b.1) w).mask ⟨N.indexNo, nextNoP M (N.msgsAt ps[j]?) N.indexNo fvs m⟩ =
        QK.toL.plan.full.msg (part w) QK.toL.plan.full.c7

theorem woMaskTie : OwedWoMaskTie := by
  intro P Cells Tok Mm Fr N Mg Z links ps j m M L cs fvs sh q QK part u pos nR kC arr mat eS eB eSe
    eC hO hF hsh hq T hidx b w hb hu
  rw [maskEntryIs P Cells Tok Fr N Mg Z links ps j m M L cs fvs sh q eS eB eSe eC hO hF hsh hq b hb
    hu nR kC arr mat w, Plan4.msg_c7 QK.toL.plan (part w) T.inNx, hidx w,
    tab_of_mem cs arr w u sh q T.shape T.seat, T.place]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tab_of_mem
#print axioms OnBytes.Road.K4.woMaskTie
