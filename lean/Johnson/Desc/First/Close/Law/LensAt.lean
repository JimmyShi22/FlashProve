-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LensAt.lean: THE LAW OF THE LENS THAT K10's LAW AT A PIECE ASKS, AT
K9's READING AND WRITING OF THE RECORD. Statements and proofs.

`k10_piece_read` and what stands on it (AtPieceRead.lean, beside this file) ask hrw: what rd reads
off wr s f S' has the frame f and the statement S'.
  `lens_of_get_set`: hrw, in the letters in which PieceOf.lean's `pieceAt` fills rd and wr, from
    "get (set s r) = r".
  `recOf_putRec`: at `recOf` and `putRec` (Johnson/Desc/First/Batch/Place.lean), by which K10's
    block is lifted to the record S: the frame and the statement that are read off what was written
    are those written: at every s. By `S.live_putLive` (LaysLive.lean). (Of the third field, the
    rows owed, nothing is said: `recOf` reads "some 0" as "none".)
  `hrw_at_K9`: so hrw holds at that lens.
Limits. It is the lens of the closing alone. Inside `K9.joint` the closing reads what the block in
front of it returned, and a further block writes behind it: this file says nothing of the joint.
Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.Close.Law.LaysLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open VerifiableInference.Desc VerifiableInference.Desc.K9

/-- From "get (set s r) = r": the law of the lens in the letters of `k10_piece_read`. -/
theorem lens_of_get_set {T : Type} (get : T → Rec) (set : T → Rec → T)
    (h : ∀ s r, get (set s r) = r) (s : T) (f : OnBytes.ReqFrame) (S' : OnBytes.Statement) :
    ((get (set s ⟨none, f, S'⟩)).owed, (get (set s ⟨none, f, S'⟩)).frame,
      (get (set s ⟨none, f, S'⟩)).st).2 = (f, S') := by
  rw [h]

/-- **The frame and the statement that K9's reading reads off what K9's writing wrote are those
written.** -/
theorem recOf_putRec (s : S) (r : Rec) :
    (recOf (putRec s r)).frame = r.frame ∧ (recOf (putRec s r)).st = r.st := by
  refine ⟨?_, rfl⟩
  show (S.live { s.putLive { s.live with frame := r.frame } with
    st := r.st, rowsOwed := r.owed }).frame = r.frame
  have e : S.live { s.putLive { s.live with frame := r.frame } with
      st := r.st, rowsOwed := r.owed } = (s.putLive { s.live with frame := r.frame }).live := rfl
  rw [e, S.live_putLive]

/-- hrw at K9's lens. -/
theorem hrw_at_K9 (s : S) (f : OnBytes.ReqFrame) (S' : OnBytes.Statement) :
    ((recOf (putRec s ⟨none, f, S'⟩)).owed, (recOf (putRec s ⟨none, f, S'⟩)).frame,
      (recOf (putRec s ⟨none, f, S'⟩)).st).2 = (f, S') := by
  obtain ⟨h1, h2⟩ := recOf_putRec s ⟨none, f, S'⟩
  exact Prod.ext h1 h2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.lens_of_get_set
#print axioms VerifiableInference.Desc.First.Close.recOf_putRec
#print axioms VerifiableInference.Desc.First.Close.hrw_at_K9
