-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoRowAt.lean: FROM THE ROW THAT THE LINK's FRAME's READER GIVES AT A RECORD TO THE
ROW's SENTENCE `Plan4K.WoRow`. Two statements with proofs: an unfolding and a filling of letters; no
new argument.

OBJECT: `Johnson.Desc.First.Walk.Law.rowAt lay n lin s` (Johnson/Top/H0/Walk/FrameRow.lean): the
pending row that the block "cleared" will lay, as a function of the carried record s; `RowSays`
(Johnson/Top/H0/MergeLaw/WoRow.lean): "a row on the committed matrix holds of the cells and of the
index masks' entries", said plainly. USER: none yet; meant: whoever shows the line wo of `K4Lines`
(CloseAtTable.lean) at a filling of the table's meaning: that line asks, of the table's item wo m at
a statement b and a witness w, `WoRow` at every record o that the seat finds in b.

  `leftOf_of_own`: where the first chain's seat finds K4's hearing's record o in s, what the open
    link's sub-proof has left for its row is o.wo.
  `Plan4K.woRow_of_rowAt`: where the seat finds o in s, the frame's reader gives a row r at s (at
    the plan's layout, any number n of claims and any shape lin), r's mask entries read the value's
    message at c7 (hidx), and `RowSays` holds of r at the value's cells: `WoRow par o m`. THE
    LETTERS UNDER `WoRow`'s «THERE ARE» ARE THE READER's OWN: claims := n, S := lin, im :=
    s.out.indexMasks, os := s.st.oracles.

Limits. NOT A MEMBER OF `K4Lines`' LINE wo: no filling of the table's meaning is named. `RowSays` is
called a stand-in by its own file; the sentence that is meant to take its place for the item is not
in the library. hidx and that the cells of `RowSays` ARE the
value's `Wn` at the message are premises: nobody pays them. That the reader gives a row at a
statement behind K4's yes is a premise. Nothing on soundness.
-/
import Johnson.Road.K4.CloseK5
import Johnson.Desc.First.K4.SeatS
import Johnson.Top.H0.MergeLaw.WoRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Law (leftOf rowAt_some leftOf_of_lay)
open Inst.Model (Scl)

/-- Where the seat finds K4's hearing's record, what is left for the link's row is its field wo. -/
theorem leftOf_of_own {s : S} {o : Own} (h : seatS.own s = some o) : leftOf s = some o.wo := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  cases here with
  | lay a =>
    have e : a.own = some o := h
    refine leftOf_of_lay ?_
    show a.own.map (·.wo) = some o.wo
    rw [e]
    rfl
  | _ => cases h

variable [scl : Scl] {Mm : Type}

/-- **The frame's reader's row, where it holds, gives the row's sentence**: where the seat finds
K4's hearing's record o in s (ho) and the row's mask entries read the value's message at c7 (hidx: a
premise that nobody pays). -/
theorem Plan4K.woRow_of_rowAt (QK : Plan4K Mm S) {par : Par} {o : Own} {m : Mm} {s : S} {n : ℕ}
    {lin : Params.LinShape} {r : TensorRow} {idx : ℕ → Cb.Gl.E} (ho : seatS.own s = some o)
    (hr : Johnson.Desc.First.Walk.Law.rowAt par.P.wsLay n lin s = some r)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = QK.toL.plan.full.msg m QK.toL.plan.full.c7)
    (hs : VerifiableInference.Desc.First.MergeLaw.RowSays par.P.wsLay.lk lin.kRow
      (QK.toL.plan.full.Wn (QK.toL.plan.full.msg m)) idx r) :
    QK.WoRow par o m := by
  obtain ⟨w, os', hl, hp⟩ := rowAt_some.1 hr
  rw [leftOf_of_own ho] at hl
  obtain rfl := Option.some.inj hl
  exact ⟨n, lin, s.out.indexMasks, s.st.oracles, os', r, idx, hp, hidx, hs⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.leftOf_of_own
#print axioms OnBytes.Road.K4.Plan4K.woRow_of_rowAt
