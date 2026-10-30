-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Free32.lean: ROW 3.2 OF THE KEY FILE's TABLES: THE PROMISE's LAST LETTER's STEP ACROSS THE OWN PROXIMITY TEST: Free₃ at border 2 in front gives Free₃ at border 3 behind. One statement with its proof, field by field.
OBJECT. Free₃ (Johnson/RunOne/KeyRows23At.lean: sixteen fields). USER. Johnson/RunOne/Law/K12Fwd32.lean.
LETTERS. All the tables' own, free. z: in front; (z.1, z.2 with tE's statement, book and roots): behind: what Seat.leaveOwn writes. Premises: the pins open behind are among those in front · of the test's yes: each place stands (OutK) · the statement stays in order (Johnson/RunOne/Law/K12Order.lean) · hrec | hcoll as at row 1.15 · the strings stay.
HOW EACH FIELD GOES. Ten are guarded by "k ≤ 2" or "k = 0": empty at 3 · arr · reads: no state · order: hord · shown: the words stay · maskW: each place stands; the chain's local state (loc) is not written.
Limits. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.K12.Law.OutK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Free32
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12 (T12)
open Johnson.RunOne.KeyRows23

variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (coll : Strs → Rec → Prop) (off₂ off₃ : Nat → Nat)

/-- **The promise's last letter across the own proximity test.** -/
theorem free₃_seat (hpin : ∀ j ∈ pinned (open₃ 3), j ∈ pinned (open₃ 2)) (z : P₃ × St₃) (tE : T12) (y y' : Strs)
    (hbook : BookKeeps z.2.book tE.book) (hord : Means.InOrder z.2.st → Means.InOrder tE.st)
    (hrec : G₃.recOf (z.1, { z.2 with st := tE.st, book := tE.book, roots := tE.roots }) = G₃.recOf z)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (Hy : StrsStay F at_ (open₃ 2) y y') (h : Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 2 z y) :
    Free₃ F G₃ at_ S K₁ R coll off₂ off₃ 3 (z.1, { z.2 with st := tE.st, book := tE.book, roots := tE.roots }) y' :=
  { record := by
      obtain ⟨r, hr, hc⟩ := h.record
      exact ⟨r, hrec.trans hr, fun c => hc (hcoll y y' r Hy.cell c)⟩
    arr := h.arr
    reads := h.reads
    placed := fun c => absurd c (by omega)
    omega₀ := fun c => absurd c (by omega)
    omega := fun _ c => absurd c (by omega)
    in₀ := fun c => absurd c (by omega)
    inOwn := fun c => absurd c (by omega)
    inOmega := fun _ c => absurd c (by omega)
    order := hord h.order
    order₀ := fun c => absurd c (by omega)
    shown := fun j hj => shownAt_ride F at_ j y y' (Hy.word j (hpin j hj)) (h.shown j (hpin j hj))
    maskW := by
      obtain ⟨q, p, b1, b2⟩ := h.maskW
      exact ⟨q, p, hbook.place _ _ b1, hbook.place _ _ b2⟩
    lin₀ := fun c => absurd c (by omega)
    seatW := fun c => absurd c (by omega)
    seatOmega₀ := fun c => absurd c (by omega) }

end Johnson.RunOne.Law.K12Free32

#print axioms Johnson.RunOne.Law.K12Free32.free₃_seat
