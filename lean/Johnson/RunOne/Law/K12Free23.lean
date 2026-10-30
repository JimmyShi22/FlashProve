-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Free23.lean: ROWS 2.9 AND 2.10 OF THE KEY FILE's TABLES: THE PROMISE's LAST LETTER's STEP ACROSS A PROXIMITY TEST OF THE SHARED CHAIN: Free₂ at border k in front gives Free₂ at border k' behind. One general statement with its proof, field by field.
OBJECT. Free₂ (Johnson/RunOne/KeyRows23At.lean: twenty-two fields). USER. Johnson/RunOne/Law/K12Fwd29 | K12Fwd210.lean.
LETTERS. All the tables' own, free. z: in front; (z.1, z.2 with tE's statement, book and roots): behind: what Seat.leave writes. Premises: 6 ≤ k (all the guarded fields are awake in front) · the pins open behind are among those in front · of the test's yes: the codes stand, each message stands with its shape, each place stands (OutK) · the statement stays in order (Johnson/RunOne/Law/K12Order.lean) · hrec | hcoll as at row 1.15 · the strings stay.
HOW EACH FIELD GOES. Eight speak of what was handed (z.1): untouched · key · lay: the chain's local state (loc) is not written; the codes stand · arr · reads: no state · placed · maskU: each place stands · samples · rowsIn: BY THEIR TEXTS they are fields of Means.InOrder behind · linOk: the codes stand · seatU · seatOmega: the shapes stand · shown: the words stay.
Limits. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.K12.Law.OutK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Free23
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12 (T12)
open Johnson.RunOne.KeyRows23

theorem any_shape (A B : Statement) (hs : ShapesKeep A B) (o : Nat) (sh : OracleShape) (h : (A.oracles[o]?).any (·.shape == sh) = true) :
    (B.oracles[o]?).any (·.shape == sh) = true := by
  cases hx : A.oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    obtain ⟨x', hx', e⟩ := hs o x hx
    rw [hx']
    show (x'.shape == sh) = true
    rw [e]
    exact h

variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **The promise's last letter across a proximity test of the shared chain.** -/
theorem free₂_seat (k k' : Nat) (h6 : 6 ≤ k) (hpin : ∀ j ∈ pinned (open₂ k'), j ∈ pinned (open₂ k)) (z : P₂ × St₂) (tE : T12) (y y' : Strs)
    (hcodes : tE.st.codes = z.2.st.codes) (hshapes : ShapesKeep z.2.st tE.st) (hbook : BookKeeps z.2.book tE.book)
    (hord : Means.InOrder z.2.st → Means.InOrder tE.st)
    (hrec : G₂.recOf (z.1, { z.2 with st := tE.st, book := tE.book, roots := tE.roots }) = G₂.recOf z)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (Hy : StrsStay F at_ (open₂ k) y y') (h : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k z y) :
    Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k' (z.1, { z.2 with st := tE.st, book := tE.book, roots := tE.roots }) y' := by
  have hI := hord h.order
  exact
    { record := by
        obtain ⟨r, hr, hc⟩ := h.record
        exact ⟨r, hrec.trans hr, fun c => hc (hcoll y y' r Hy.cell c)⟩
      last := h.last
      eval := h.eval
      placed₁ := h.placed₁
      in₁ := h.in₁
      order₁ := h.order₁
      key := h.key
      codes := hcodes.trans h.codes
      lay := fun _ => by
        show z.2.loc.oU.lay = vectorLay tE.st.codes S.fold.u S.fold.rowsHigh
        rw [hcodes]
        exact h.lay (by omega)
      arr := h.arr
      reads := h.reads
      placed := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := List.mem_filter.1 hj
        obtain ⟨o, t, a1, a2, a3⟩ := h.placed j (List.mem_filter.2 ⟨hpin j hj1, hj2⟩)
        exact ⟨o, t, a1, hbook.place o t a2, a3⟩
      samples := fun _ _ o _ x hx r hr => hI.samples o x hx r hr
      rowsIn := fun _ => ⟨fun G hG r hr => hI.rows _ G hG r hr, fun G hG r hr => hI.rows _ G hG r hr⟩
      order := hI
      linOk := fun _ => by
        show OnBytes.linOk tE.st.codes S = true
        rw [hcodes]
        exact h.linOk (by omega)
      seatU := fun _ => any_shape _ _ hshapes 0 _ (h.seatU (by omega))
      seatOmega := fun _ => any_shape _ _ hshapes 2 _ (h.seatOmega h6)
      shown := fun j hj => shownAt_ride F at_ j y y' (Hy.word j (hpin j hj)) (h.shown j (hpin j hj))
      fits := h.fits
      mask₁ := h.mask₁
      maskU := fun _ => by
        obtain ⟨q, p, b1, b2⟩ := h.maskU (by omega)
        exact ⟨q, p, hbook.place 0 _ b1, hbook.place 1 _ b2⟩ }

end Johnson.RunOne.Law.K12Free23

#print axioms Johnson.RunOne.Law.K12Free23.free₂_seat
