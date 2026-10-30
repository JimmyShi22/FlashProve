-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/CellsTie.lean: THE KEY's SIDE OF THE LAW OF "LIN point", SAID IN THE LETTERS OF
THE TABLES OF JOINTS: a collision test and a decoder that are handed the stored table as plain
functions show it (Johnson/Desc/Msg.lean: Strs.cell; from the rule's own oracles:
Johnson/Desc/Sound/MsgAt.lean: strsOf) and a record, and a reader of the record in this chain's
state.

  colsOf          the stored table's columns, of its symbols as plain functions show them.
  tabOf_cells     the columns that this kind's laws read off the oracle string (tabOf) are these.
  recAt           THE READER OF THE RECORD: the key's seeds and the record's answers, read, as the
                  library's record at the typed data ixOf2.
  collAt, dcdAt   the library's collision and decoder with the record at ixOf2, handed the stored
                  table's symbols and a record.
  badAt           the library's bad points likewise.
  coll_iff, dec_iff, bad_iff, tab_eq   point_goodInY2's hcoll, DecX2, BadX2 and TabX2 ARE these at
                  (strsOf F a.2).cell and recAt a.1.

What is not claimed. That a table of joints' guarded decoder is made of collAt and dcdAt: that is
left open; the letters err, eM, rank stay. What is made of a decoded table behind the decoder
(the cells) is not spoken of. The ties are said at strsOf F a.2, the whole oracle string: a table
that reads its shared items at an acting part's value owes one equation more: that value shows the
same stored table. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointKey2
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Sound (Frame strsOf)

/-- The stored table's columns, of its symbols as plain functions show them. -/
def colsOf (c : Nat → Option (Nat × List UInt64)) (x : Nat) : List UInt64 :=
  ((c x).map (·.2)).getD []

/-- The columns that this kind's laws read off the oracle string are these. -/
theorem tabOf_cells {F : Frame} (y : F.E.Str) : tabOf y = colsOf (strsOf F y).cell := by
  funext x
  show tabOf y x = ((VerifiableInference.Desc.Sound.cellAt F y x).map (·.2)).getD []
  unfold tabOf VerifiableInference.Desc.Sound.cellAt
  split <;> rfl

/-- **The reader of the record** in this chain's state. -/
def recAt (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (s : St) : (ixOf2 p.S.fold err eM rank).Rec :=
  (seedsFn OnBytes.Model.Reading.gl p.S.fold.index s.loc.key,
    recOf p.S.fold.index fun k => OnBytes.Model.Reading.gl.val (s.loc.key.record.getD k zeroE))

/-- The library's collision at ixOf2, handed the stored table's symbols and a record. -/
def collAt (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (c : Nat → Option (Nat × List UInt64)) (rec : (ixOf2 p.S.fold err eM rank).Rec) : Prop :=
  (ixOf2 p.S.fold err eM rank).Coll (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf c)) rec.1

/-- The library's decoder with the record at ixOf2, handed the same. -/
noncomputable def dcdAt (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (c : Nat → Option (Nat × List UInt64)) (rec : (ixOf2 p.S.fold err eM rank).Rec) :
    Option ((ixOf2 p.S.fold err eM rank).Row × Fin p.S.fold.index.code.ell → GE) :=
  (ixOf2 p.S.fold err eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf c)) rec

/-- The library's bad points of the fold at ixOf2, handed the same. -/
def badAt (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (e' : Nat) (c : Nat → Option (Nat × List UInt64)) (rec : (ixOf2 p.S.fold err eM rank).Rec)
    (gam : Fin p.S.fold.index.v → GE) : Prop :=
  (ixOf2 p.S.fold err eM rank).Bad (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf c)) rec e'
    gam

variable {F : Frame}

/-- point_goodInY2's hcoll speaks of collAt. -/
theorem coll_iff (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (a : St × F.E.Str) :
    (ixOf2 p.S.fold err eM rank).Coll
        (tabF OnBytes.Model.Reading.gl p.S.fold.index (tabOf a.2))
        (seedsFn OnBytes.Model.Reading.gl p.S.fold.index a.1.loc.key) ↔
      collAt p err eM rank (strsOf F a.2).cell (recAt p err eM rank a.1) := by
  rw [tabOf_cells]
  exact Iff.rfl

/-- DecX2 speaks of dcdAt. -/
theorem dec_iff (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (a : St × F.E.Str) :
    DecX2 p err eM rank (tabOf a.2) a.1.loc.key ↔
      (dcdAt p err eM rank (strsOf F a.2).cell (recAt p err eM rank a.1)).isSome = true := by
  rw [tabOf_cells]
  exact Iff.rfl

/-- BadX2 speaks of badAt. -/
theorem bad_iff (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (e' : Nat) (a : St × F.E.Str) (gam : Fin p.S.fold.index.v → GE) :
    BadX2 p err eM rank e' (tabOf a.2) a.1.loc.key gam ↔
      badAt p err eM rank e' (strsOf F a.2).cell (recAt p err eM rank a.1) gam := by
  rw [tabOf_cells]
  exact Iff.rfl

/-- TabX2 is what dcdAt returns: row r, place k. -/
theorem tab_eq (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (a : St × F.E.Str) (U : (ixOf2 p.S.fold err eM rank).Row × Fin p.S.fold.index.code.ell → GE)
    (h : dcdAt p err eM rank (strsOf F a.2).cell (recAt p err eM rank a.1) = some U) (r k : Nat)
    (hk : k < p.S.fold.index.code.ell) :
    TabX2 p err eM rank (tabOf a.2) a.1.loc.key r k = U (bitsOf p.S.fold.index.v r, ⟨k, hk⟩) := by
  rw [tabOf_cells]
  unfold TabX2
  have h' : (ixOf2 p.S.fold err eM rank).dec
      (tabF OnBytes.Model.Reading.gl p.S.fold.index (colsOf (strsOf F a.2).cell))
      (seedsFn OnBytes.Model.Reading.gl p.S.fold.index a.1.loc.key,
        recOf p.S.fold.index fun k =>
          OnBytes.Model.Reading.gl.val (a.1.loc.key.record.getD k zeroE)) = some U := h
  rw [h']
  show (if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0) = _
  rw [dif_pos hk]

end Desc.K14.Law
