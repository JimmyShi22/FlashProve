-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/PscRoom.lean: room in the ledger of hidden scalars: which slots are free, and
what keeps them free. Definitions of Props and small laws, on the ledger (Fork) alone: no text of a
hearing, no round. The notions read which slots are marked as filled, never what lies there. Beside
Sized, Filled and Same (OnBytes/Tie/Pv/Psc/PscFork.lean) and Later
(OnBytes/Tie/Pv/Psc/PscLater.lean). It imports no library of mathematics.

  FreeAbove F     : nothing at or above the next slot is filled.
  LedgerRoom F n  : a ledger with room for n more slots: the arrays have their size; n more slots
                    fit; nothing at or above the next slot is filled. What a hearing kind keeps: in
                    front with room for what it takes and more, behind with room for the rest.
  SlotsOwed F a n : a stretch that is owed: n slots from a on, below the next slot, free: taken, not
                    yet written. It does not say that these slots are there (a + n within the number
                    of slots): see owed_returns.
  WritesAbove F G : a step that turns no mark below the next slot of the ledger in front, and does
                    not lower the next slot. It says nothing of the number of slots or the sizes.
  WritesWithin F G a n : a step that writes nowhere but inside the stretch of n slots from a on: it
                    keeps the next slot and turns no mark outside that stretch.
  ledgerRoom_iff, LedgerRoom.mono, ledgerRoom_slots : the second by the first; less room; a fresh
                    ledger.
  owed_of_writesAbove, WritesAbove.refl, WritesAbove.trans, writesAbove_bites : a stretch stays owed
                    through steps that write above; a step that fills an owed slot does not.
  owed_of_writesWithin, freeAbove_of_writesWithin : a stretch stays owed through a step that writes
                    within another stretch, apart from it: so several stretches can be owed at once;
                    such a step below the next slot keeps FreeAbove.
  Spares, SparesAlong, owed_of_spares, owed_along : a step that writes above, or within a stretch
                    apart, spares a stretch; it stays owed along a row of such steps. (The row is
                    needed: one such step after another need not be one such step.)
  filled_lt, free_getD : a filled slot is below the number of slots; a slot that is not filled reads
                    as free at either default.
  hideRun_returns : a run of values goes under slots that are there and free. It asks the marks'
                    size alone. RETURNS, NOT: IS WRITTEN: at a ledger whose two other arrays are
                    short the run returns, the slots are marked, and the values are lost. For what
                    lies under the slots see hideRun_ok (PscFork.lean), which asks all three sizes.
  hideRun_fills, hideRun_writesWithin : such a run turns no mark outside its own slots, and keeps
                    the next slot. (That its own slots are filled is hideRun_ok's.)
  takeHide, takeHide_above : n slots are taken and filled: from room for n and k more it returns and
                    leaves room for k; it writes above.
  owed_returns, owed_returns_later : a run of n values goes under a stretch that is owed and there;
                    and what a user needs beside SlotsOwed at a later ledger.
  publicPart_returns, publicPart_returns_filled : the public part of a form is given if its slots
                    are there and filled; with the marks' size, "filled" is enough.
WHY "SlotsOwed" AND NOT "Owed": OnBytes/Model/Hide.lean has a structure Owed (a claim that a routine
has left for its caller; the ledger's field owed): another notion.
LIMITS. Later does not keep a stretch owed, nor FreeAbove: a later ledger may fill any free slot.
NO GIVER HERE but a fresh ledger, the step that does nothing, a run of values and a taking: that a
given function keeps LedgerRoom, leaves a stretch owed or writes above is that function's law (for
the masked sumcheck: Johnson/Desc/Part/MaskedSumFree.lean). That two calls'
stretches lie apart is their caller's. Nothing on soundness, on an honest prover or on hiding.
-/
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-! ## The four notions -/

/-- Nothing at or above the next slot is filled. -/
def FreeAbove (F : Fork) : Prop := ∀ j, F.next ≤ j → ¬ Filled F j

/-- A ledger with room for n more slots. -/
structure LedgerRoom (F : Fork) (n : Nat) : Prop where
  sized : Sized F
  fits : F.next + n ≤ F.ns
  free : ∀ j, F.next ≤ j → ¬ Filled F j

/-- A stretch that is owed: n slots from a on, below the next slot, free. -/
def SlotsOwed (F : Fork) (a n : Nat) : Prop :=
  a + n ≤ F.next ∧ ∀ j, a ≤ j → j < a + n → ¬ Filled F j

/-- A step that turns no mark below the next slot of the ledger in front, and does not lower it. -/
def WritesAbove (F G : Fork) : Prop :=
  F.next ≤ G.next ∧ ∀ j, j < F.next → (Filled G j ↔ Filled F j)

theorem ledgerRoom_iff (F : Fork) (n : Nat) :
    LedgerRoom F n ↔ Sized F ∧ FreeAbove F ∧ F.next + n ≤ F.ns :=
  ⟨fun h => ⟨h.sized, h.free, h.fits⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

theorem LedgerRoom.mono {F : Fork} {n m : Nat} (h : LedgerRoom F n) (hm : m ≤ n) :
    LedgerRoom F m :=
  ⟨h.sized, Nat.le_trans (Nat.add_le_add_left hm _) h.fits, h.free⟩

theorem freeAbove_slots (n : Nat) : FreeAbove (({} : Fork).slots n) := by
  intro j _ hf
  have hf' : (Array.replicate n false).getD j false = true := hf
  by_cases hj : j < n
  · simp [Array.getD_eq_getD_getElem?, hj] at hf'
  · simp [Array.getD_eq_getD_getElem?, hj] at hf'

/-- A fresh ledger of n slots has room for n. -/
theorem ledgerRoom_slots (n : Nat) : LedgerRoom (({} : Fork).slots n) n :=
  ⟨slots_sized _ _, Nat.le_of_eq (Nat.zero_add n), freeAbove_slots n⟩

theorem owed_of_writesAbove {F G : Fork} {a n : Nat} (ho : SlotsOwed F a n) (hw : WritesAbove F G) :
    SlotsOwed G a n :=
  ⟨Nat.le_trans ho.1 hw.1, fun j x y hf =>
    ho.2 j x y ((hw.2 j (Nat.lt_of_lt_of_le y ho.1)).1 hf)⟩

theorem WritesAbove.refl (F : Fork) : WritesAbove F F := ⟨Nat.le_refl _, fun _ _ => Iff.rfl⟩

theorem WritesAbove.trans {F G H : Fork} (h1 : WritesAbove F G) (h2 : WritesAbove G H) :
    WritesAbove F H :=
  ⟨Nat.le_trans h1.1 h2.1, fun j hj =>
    (h2.2 j (Nat.lt_of_lt_of_le hj h1.1)).trans (h1.2 j hj)⟩

/-- A step that fills an owed slot does not write above. -/
theorem writesAbove_bites {F G : Fork} {a n j : Nat} (ho : SlotsOwed F a n) (x : a ≤ j)
    (y : j < a + n) (hf : Filled G j) : ¬ WritesAbove F G :=
  fun hw => (owed_of_writesAbove ho hw).2 j x y hf

/-- A step that writes nowhere but inside the stretch of n slots from a on: it keeps the next slot
and turns no mark outside that stretch. -/
def WritesWithin (F G : Fork) (a n : Nat) : Prop :=
  G.next = F.next ∧ ∀ j, (j < a ∨ a + n ≤ j) → (Filled G j ↔ Filled F j)

/-- A stretch stays owed through a step that writes within another stretch, apart from it. -/
theorem owed_of_writesWithin {F G : Fork} {a n b m : Nat} (ho : SlotsOwed F b m)
    (hp : WritesWithin F G a n) (hapart : b + m ≤ a ∨ a + n ≤ b) : SlotsOwed G b m :=
  ⟨by rw [hp.1]; exact ho.1, fun j x y hf => ho.2 j x y ((hp.2 j (by omega)).1 hf)⟩

/-- A step that writes within a stretch below the next slot keeps FreeAbove. -/
theorem freeAbove_of_writesWithin {F G : Fork} {a n : Nat} (hA : FreeAbove F)
    (hp : WritesWithin F G a n) (hb : a + n ≤ F.next) : FreeAbove G := by
  intro j hj hf
  rw [hp.1] at hj
  exact hA j hj ((hp.2 j (Or.inr (Nat.le_trans hb hj))).1 hf)

/-- A step that spares the stretch of n slots from a on: it writes above, or it writes within a
stretch that lies apart from that one. -/
def Spares (F G : Fork) (a n : Nat) : Prop :=
  WritesAbove F G ∨ ∃ b m, WritesWithin F G b m ∧ (a + n ≤ b ∨ b + m ≤ a)

theorem owed_of_spares {F G : Fork} {a n : Nat} (ho : SlotsOwed F a n) (h : Spares F G a n) :
    SlotsOwed G a n := by
  cases h with
  | inl hw => exact owed_of_writesAbove ho hw
  | inr hp =>
    obtain ⟨b, m, h1, h2⟩ := hp
    exact owed_of_writesWithin ho h1 h2

/-- The ledgers of a row of steps, each of which spares the stretch. -/
def SparesAlong (a n : Nat) : Fork → List Fork → Prop
  | _, [] => True
  | F, G :: l => Spares F G a n ∧ SparesAlong a n G l

/-- **A stretch stays owed along a row of steps each of which writes above or within a stretch
apart.** -/
theorem owed_along {a n : Nat} : ∀ (l : List Fork) (F : Fork), SlotsOwed F a n →
    SparesAlong a n F l → SlotsOwed (l.getLastD F) a n
  | [], _, ho, _ => ho
  | G :: l, _, ho, h => by
    have h2 := owed_along l G (owed_of_spares ho h.1) h.2
    cases l with
    | nil => exact h2
    | cons H l' => exact h2

/-! ## The marks -/

/-- A filled slot is below the number of slots. -/
theorem filled_lt {F : Fork} {j : Nat} (hs : F.gotF.size = F.ns) (hf : Filled F j) : j < F.ns := by
  by_cases hj : j < F.ns
  · exact hj
  · exfalso
    have hj' : ¬ j < F.gotF.size := by
      rw [hs]
      exact hj
    have h0 : F.gotF.getD j false = false := by
      simp [Array.getD_eq_getD_getElem?, hj']
    have h1 : F.gotF.getD j false = true := hf
    rw [h0] at h1
    cases h1

/-- A slot that is not filled reads as free, whatever the default. -/
theorem free_getD {F : Fork} {j : Nat} (hs : F.gotF.size = F.ns) (hj : j < F.ns)
    (hf : ¬ Filled F j) : F.gotF.getD j true = false := by
  have hsz : j < F.gotF.size := by
    rw [hs]
    exact hj
  have eq : F.gotF.getD j true = F.gotF.getD j false := by
    simp [Array.getD_eq_getD_getElem?, hsz]
  rw [eq]
  cases hb : F.gotF.getD j false with
  | false => rfl
  | true => exact absurd hb hf

/-! ## What returns -/

/-- One value goes under a slot that is there and free. RETURNS, NOT: IS WRITTEN: only the marks'
size is asked: where the two other arrays are short the value is lost. -/
theorem hide_returns {F : Fork} {j : Nat} (y f : E) (hs : F.gotF.size = F.ns) (hj : j < F.ns)
    (hfree : ¬ Filled F j) :
    F.hide j y f = some { F with
      gotF := F.gotF.set! j true, vp := F.vp.set! j y, mf := F.mf.set! j f } := by
  have h0 := free_getD hs hj hfree
  have hc : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) = true := by
    rw [h0, hs]
    simp [hj]
  unfold Fork.hide
  rw [if_pos hc]

theorem hideSteps_returns (f : E) : ∀ (l : List E) (first : Nat) (F : Fork),
    F.gotF.size = F.ns → (∀ i, i < l.length → first + i < F.ns ∧ ¬ Filled F (first + i)) →
    ∃ x, l.foldlM (Fork.hideStep f) (first, F) = some x
  | [], first, F, _, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, hs, h => by
    obtain ⟨h0, h1⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h0 h1
    have hstep : Fork.hideStep f (first, F) y = some (first + 1, { F with
        gotF := F.gotF.set! first true, vp := F.vp.set! first y, mf := F.mf.set! first f }) := by
      show (F.hide first y f).map _ = _
      rw [hide_returns y f hs h0 h1]
      rfl
    rw [List.foldlM_cons, hstep]
    refine hideSteps_returns f l (first + 1) _ ?_ fun i hi => ?_
    · show (F.gotF.set! first true).size = F.ns
      simp [hs]
    · obtain ⟨b0, b1⟩ := h (i + 1) (by simpa using hi)
      have e : first + 1 + i = first + (i + 1) := by omega
      rw [e]
      refine ⟨b0, fun hf => b1 ?_⟩
      have hf' : (F.gotF.set! first true).getD (first + (i + 1)) false = true := hf
      rw [getD_set_other _ _ _ _ _ (by omega)] at hf'
      exact hf'

/-- **A run of values goes under slots that are there and free.** RETURNS, NOT: IS WRITTEN: only the
marks' size is asked; for what lies under the slots see hideRun_ok, which asks all three sizes. -/
theorem hideRun_returns {F : Fork} (first : Nat) (v : Array E) (f : E) (hs : F.gotF.size = F.ns)
    (h : ∀ i, i < v.size → first + i < F.ns ∧ ¬ Filled F (first + i)) :
    ∃ G, F.hideRun first v f = some G := by
  obtain ⟨x, hx⟩ := hideSteps_returns f v.toList first F hs (by simpa using h)
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]
  exact ⟨_, rfl⟩

/-- Such a run turns no mark outside its own slots, and keeps the next slot. -/
theorem hideRun_fills {F G : Fork} {first : Nat} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) :
    G.next = F.next ∧ ∀ j, (j < first ∨ first + v.size ≤ j) → (Filled G j ↔ Filled F j) := by
  obtain ⟨hsame, _, _, b4⟩ := hideRun_ok F G first v f hF h
  exact ⟨hsame.next, fun j hj => (b4 j hj).2.2⟩

/-- Every run of values writes within its own stretch. -/
theorem hideRun_writesWithin {F G : Fork} {first : Nat} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) : WritesWithin F G first v.size :=
  hideRun_fills hF h

/-- **A run of n values goes under a stretch that is owed and there.** -/
theorem owed_returns {F : Fork} {a n : Nat} (ho : SlotsOwed F a n) (hs : F.gotF.size = F.ns)
    (hroom : a + n ≤ F.ns) (v : Array E) (hv : v.size = n) (f : E) :
    ∃ G, F.hideRun a v f = some G :=
  hideRun_returns a v f hs fun i hi =>
    ⟨by omega, ho.2 (a + i) (Nat.le_add_right _ _) (by omega)⟩

/-- The same at a later ledger, reached by steps that write above: what a user of SlotsOwed needs
beside it is said here: the next slot was within the slots, the sizes, and Later. -/
theorem owed_returns_later {F G : Fork} {a n : Nat} (ho : SlotsOwed F a n) (hn : F.next ≤ F.ns)
    (hF : Sized F) (hl : Later F G) (hw : WritesAbove F G) (v : Array E) (hv : v.size = n)
    (f : E) : ∃ H, G.hideRun a v f = some H :=
  owed_returns (owed_of_writesAbove ho hw) (hl.sized hF).2.2
    (by rw [hl.ns]; exact Nat.le_trans ho.1 hn) v hv f

/-- **n slots are taken and filled**: it returns, room for the rest is left, the n slots are filled,
and the marks below are as they were. (That the values and factors below are kept is hideRun_ok's.)
-/
theorem takeHide {F : Fork} {n k : Nat} (h : LedgerRoom F (n + k)) (v : Array E) (hv : v.size = n)
    (f : E) :
    ∃ G, ({ F with next := F.next + n } : Fork).hideRun F.next v f = some G ∧ LedgerRoom G k ∧
      G.next = F.next + n ∧ G.ns = F.ns ∧ (∀ i, i < n → Filled G (F.next + i)) ∧
      ∀ j, j < F.next → (Filled G j ↔ Filled F j) := by
  have hS : Sized ({ F with next := F.next + n } : Fork) := h.sized
  obtain ⟨G, hG⟩ := hideRun_returns (F := { F with next := F.next + n }) F.next v f hS.2.2 (by
    intro i hi
    have := h.fits
    exact ⟨by show F.next + i < F.ns; omega, h.free _ (by omega)⟩)
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok _ G F.next v f hS hG
  have hn : G.next = F.next + n := a1.next
  have hns : G.ns = F.ns := a1.ns
  refine ⟨G, hG, ⟨a2, by rw [hn, hns]; have := h.fits; omega, fun j hj hf => ?_⟩, hn, hns,
    fun i hi => (a3 i (by omega)).2.2.1, fun j hj => (a4 j (Or.inl hj)).2.2⟩
  rw [hn] at hj
  exact h.free j (by omega) ((a4 j (Or.inr (by omega))).2.2.1 hf)

/-- Such a taking writes above. -/
theorem takeHide_above {F : Fork} {n k : Nat} (h : LedgerRoom F (n + k)) (v : Array E)
    (hv : v.size = n) (f : E) :
    ∃ G, ({ F with next := F.next + n } : Fork).hideRun F.next v f = some G ∧ LedgerRoom G k ∧
      WritesAbove F G := by
  obtain ⟨G, a, b, c, _, _, e⟩ := takeHide h v hv f
  exact ⟨G, a, b, by rw [c]; exact Nat.le_add_right _ _, e⟩

theorem publicLoop_returns (F : Fork) : ∀ (l : List (Nat × E)) (v : E),
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) →
    ∃ t, l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y))
      v = some t
  | [], v, _ => ⟨v, rfl⟩
  | x :: l, v, h => by
    have hs : F.shown x.1 = some (F.vp.getD x.1 zeroE) :=
      (shown_iff F _ _).2 ⟨(h x (by simp)).1, (h x (by simp)).2, rfl⟩
    rw [List.foldlM_cons, hs]
    exact publicLoop_returns F l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **The public part of a form on slots that are there and filled is given.** -/
theorem publicPart_returns (F : Fork) (C : Aff)
    (h : ∀ x ∈ C.slots.toList, x.1 < F.ns ∧ Filled F x.1) : ∃ t, F.publicPart C = some t := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact publicLoop_returns F _ _ h

/-- With the marks' size, "filled" is enough. -/
theorem publicPart_returns_filled (F : Fork) (C : Aff) (hs : F.gotF.size = F.ns)
    (h : ∀ x ∈ C.slots.toList, Filled F x.1) : ∃ t, F.publicPart C = some t :=
  publicPart_returns F C fun x hx => ⟨filled_lt hs (h x hx), h x hx⟩

end OnBytes.PscRun

#print axioms OnBytes.PscRun.ledgerRoom_iff
#print axioms OnBytes.PscRun.ledgerRoom_slots
#print axioms OnBytes.PscRun.owed_of_writesAbove
#print axioms OnBytes.PscRun.writesAbove_bites
#print axioms OnBytes.PscRun.filled_lt
#print axioms OnBytes.PscRun.free_getD
#print axioms OnBytes.PscRun.hideRun_returns
#print axioms OnBytes.PscRun.hideRun_fills
#print axioms OnBytes.PscRun.owed_of_writesWithin
#print axioms OnBytes.PscRun.freeAbove_of_writesWithin
#print axioms OnBytes.PscRun.hideRun_writesWithin
#print axioms OnBytes.PscRun.owed_along
#print axioms OnBytes.PscRun.takeHide
#print axioms OnBytes.PscRun.takeHide_above
#print axioms OnBytes.PscRun.owed_returns
#print axioms OnBytes.PscRun.owed_returns_later
#print axioms OnBytes.PscRun.publicPart_returns
#print axioms OnBytes.PscRun.publicPart_returns_filled
