-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/DecTie.lean: THE TYPED DATA OF THE LAW OF "LIN point" IS THE LIBRARY's OWN
FORMAT OF A STORED TABLE WITH A RECORD (OnBytes/Slice/DecoderRec.lean: DecR.ix), and this kind's
collision test and decoder on the stored table's symbols (Johnson/Desc/K14/Law/CellsTie.lean:
collAt, dcdAt) are that file's coll and dcd.

  numOf_rowNo     the two numberings of a cube's vertices, the first coordinate lowest, are one.
  decROf          the library's record of a decoder, of the public shape: the table's code; the
                  number of row variables; the radius eM; the sample map of one row; where the pads
                  begin.
  rank0           the library's fixed order of tables.
  ix_eq           ixOf2 at rank0 IS (decROf …).ix.
  tab_tie         the stored table as the library lifts it (DecR.tab) is tabF of the symbols'
                  columns.
  coll_tie, dcd_tie   collAt and dcdAt at rank0 are DecR.coll and DecR.dcd at the raw string's
                  symbols (a missing symbol read as (0, [])): what collRaw and dcdRaw call where the
                  string has its length.

What is not claimed. THE SAMPLE MAP: decROf lays this kind's sampleOf (with its letter err) as Z.
That the decoder of record at the top is laid at that Z and at this radius eM is not said
here: DecR leaves Z open. What is made of a decoded table behind the decoder is not spoken of. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.CellsTie
import OnBytes.Slice.DecoderRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- The two numberings of a cube's vertices are one. -/
theorem numOf_rowNo : ∀ (k : Nat) (b : Fin k → Bool), numOf k b = Sz.rowNo b
  | 0, b => by simp [numOf, Sz.rowNo]
  | k + 1, b => by
    unfold Sz.rowNo
    rw [numOf, numOf_rowNo k (Fin.tail b), Fin.sum_univ_succ]
    unfold Sz.rowNo
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.tail, Fin.val_succ]
    split
    · rw [pow_succ, Nat.mul_comm]
    · rfl

/-- The library's record of a decoder with a record, of the public shape. -/
noncomputable def decROf (S : FoldeqShape) (err eM : Nat) : DecR where
  T := codeOf S.index.code
  v := S.index.v
  eM := eM
  Z := sampleOf S.index (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) err
  cut := S.index.plain

/-- The library's fixed order of tables. -/
noncomputable def rank0 (S : FoldeqShape) :
    ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat :=
  fun M => (Fintype.equivFin _ M).val

/-- **The typed data is the library's own format of a stored table with a record.** -/
theorem ix_eq (S : FoldeqShape) (err eM : Nat) :
    ixOf2 S err eM (rank0 S) = (decROf S err eM).ix := rfl

/-- The stored table as the library lifts it is tabF of the symbols' columns. -/
theorem tab_tie (S : FoldeqShape) (err eM : Nat) (c : Nat → Option (Nat × List UInt64)) :
    (decROf S err eM).tab (fun p => (c p.val).getD (0, [])) =
      tabF OnBytes.Model.Reading.gl S.index (colsOf c) := by
  funext r x
  show algebraMap Cb.Gl.F Cb.Gl.E (toF (((c x.val).getD (0, [])).2.getD (Sz.rowNo r) 0)) =
    OnBytes.Model.Reading.gl.val (OnBytes.ofF ((colsOf c x.val).toArray.getD (numOf S.index.v r) 0))
  rw [gl_ofF, numOf_rowNo]
  unfold colsOf
  cases c x.val with
  | none => simp
  | some s =>
    simp
    rfl

/-- collAt at the library's order is the library's coll at the raw string's symbols. -/
theorem coll_tie (p : Par) (err eM : Nat) (c : Nat → Option (Nat × List UInt64))
    (rec : (ixOf2 p.S.fold err eM (rank0 p.S.fold)).Rec) :
    collAt p err eM (rank0 p.S.fold) c rec ↔
      (decROf p.S.fold err eM).coll (fun q => (c q.val).getD (0, [])) rec.1 := by
  unfold collAt DecR.coll
  rw [tab_tie]
  exact Iff.rfl

/-- dcdAt at the library's order is the library's dcd at the raw string's symbols. -/
theorem dcd_tie (p : Par) (err eM : Nat) (c : Nat → Option (Nat × List UInt64))
    (rec : (ixOf2 p.S.fold err eM (rank0 p.S.fold)).Rec) :
    dcdAt p err eM (rank0 p.S.fold) c rec =
      (decROf p.S.fold err eM).dcd (fun q => (c q.val).getD (0, [])) rec := by
  unfold dcdAt DecR.dcd
  rw [tab_tie]
  rfl

end Desc.K14.Law
