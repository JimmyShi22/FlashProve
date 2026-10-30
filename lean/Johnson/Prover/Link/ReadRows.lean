-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadRows.lean: THE CARRIED ROWS' SYMBOLS ARE MADE, FROM SIZES (Own.rowsSymbols,
Johnson/Desc/Own/Symbols.lean: the guard G16 of the reading of the old rows). No frame: on arrays
of columns; no statement, no book, no view. Where no member is kept and the rows have the old and
the fresh mask row: if at each listed position each member's column has a first row and room in the
layout's two tables, and the fresh message's column has 2 ^ h mask symbols, then the symbols are
made, and they are as many as the positions times the rows.

THE LAYING ITSELF IS THE LIBRARY's, AND CALLED: that the members' columns are laid in
(layMembers_yes, Johnson/Desc/First/Link/Law/FrontAnswers.lean) and which kept symbols come out
(kept_laid,
LongMasks.lean). That file's rowsAt_yes stands at the empty array and gives no size; the loop over
the positions wants every array, and by how much it grows: rowsAt_some.

Main names (namespace Johnson.Prover.Link).
  ColRoom, ColRoom.fits   one column's room where the member is not kept; it is the library's
    ColFits at the column's sizes.
  keptOf_none   no kept member: no kept symbol.
  FitsAt, rowsAt_some, rowsFrom_some   one position, behind any array, with the size; all positions.
  rowsSymbols_some   THE STATEMENT.

By: layMembers_yes, ColFits (Johnson/Desc/First/Link/Law/FrontAnswers.lean) · kept_laid, keptOf_cons
(Johnson/Desc/First/Link/Law/LongMasks.lean).

Limits. That it returns, and how many symbols: nothing on what the symbols are.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.FrontAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes
open VerifiableInference.Desc.Own
open VerifiableInference.Desc.LinkJoin (ColFits layMembers_yes kept_laid keptOf keptOf_cons)

/-- What a column needs to be laid in at the member w, at tables of M and Z rows, where the member
is not kept. -/
def ColRoom (L : GroupLayout) (w M Z : Nat) (col : Column) : Prop :=
  (col.mask.size = 0 ∨ ∃ f, L.maskFirst.getD w none = some f ∧ f + col.mask.size ≤ Z) ∧
    (col.main.size = 0 ∨ ∃ f, L.mainFirst.getD w none = some f ∧ f + col.main.size ≤ M)

/-- It is the library's condition, at the column's two sizes. -/
theorem ColRoom.fits {L : GroupLayout} {w M Z : Nat} {col : Column} (h : ColRoom L w M Z col) :
    ColFits L w col.main.size col.mask.size M Z :=
  ⟨h.1, Or.inr h.2⟩

/-- No kept member: no kept symbol. -/
theorem keptOf_none (L : GroupLayout) (opened : Array (Array Column)) (i : Nat)
    (hk : ∀ w, L.kept.getD w false = false) : ∀ ws : List Nat, keptOf L opened i ws = #[]
  | [] => rfl
  | w :: ws => by
    rw [keptOf_cons, hk w, keptOf_none L opened i hk ws]
    rfl

/-- The opened columns fit the carried rows at the position number i. -/
structure FitsAt (s : SingleRows) (opened : Array (Array Column)) (i : Nat) : Prop where
  member : ∀ w, w < s.layout.members.size → ∃ col, (opened[w]?).bind (·[i]?) = some col ∧
    ColRoom s.layout w (2 ^ s.layout.k) (2 ^ s.layout.h) col
  fresh : ∃ col, (opened[s.layout.members.size]?).bind (·[i]?) = some col ∧
    col.mask.size = 2 ^ s.layout.h

theorem rowsAt_some (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat)
    (hm : s.masks = 2) (hr : s.keptRows = 0) (hk : ∀ w, s.layout.kept.getD w false = false)
    (h : FitsAt s opened i) :
    ∃ y', rowsAt s opened y i = some y' ∧ y'.size = y.size + s.rows := by
  obtain ⟨t, e⟩ := layMembers_yes s.layout opened i (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩
    fun w hw => by
      obtain ⟨col, hc, hf⟩ := h.member w (List.mem_range.1 hw)
      refine ⟨col, hc, ?_⟩
      show ColFits s.layout w col.main.size col.mask.size (Array.replicate _ zeroE).size
        (Array.replicate _ zeroE).size
      rw [Array.size_replicate, Array.size_replicate]
      exact hf.fits
  obtain ⟨fr, ef, sf⟩ := h.fresh
  have hk0 : t.kept = #[] := by
    rw [kept_laid s.layout opened i _ _ t e, keptOf_none s.layout opened i hk]
    rfl
  unfold rowsAt
  simp only [e, Option.bind_some, hk0, hr, hm, ef, sf]
  refine ⟨((y.push ((foldLow t.main s.gamma).getD 0 zeroE) ++ #[]).push
    ((foldLow t.mask (List.take s.layout.h s.gamma)).getD 0 zeroE)).push
    ((foldLow fr.mask (List.take s.layout.h s.gamma)).getD 0 zeroE), ?_, ?_⟩
  · simp
  · simp [SingleRows.rows, hr, hm]

theorem rowsFrom_some (s : SingleRows) (opened : Array (Array Column)) (hm : s.masks = 2)
    (hr : s.keptRows = 0) (hk : ∀ w, s.layout.kept.getD w false = false) :
    ∀ (is : List Nat) (y : Array E), (∀ i ∈ is, FitsAt s opened i) →
      ∃ y', rowsFrom s opened is y = some y' ∧ y'.size = y.size + is.length * s.rows
  | [], y, _ => ⟨y, rfl, by simp⟩
  | i :: is, y, h => by
    obtain ⟨y1, e1, s1⟩ := rowsAt_some s opened y i hm hr hk (h i List.mem_cons_self)
    obtain ⟨y2, e2, s2⟩ := rowsFrom_some s opened hm hr hk is y1
      fun j hj => h j (List.mem_cons_of_mem _ hj)
    refine ⟨y2, ?_, ?_⟩
    · show (rowsAt s opened y i).bind (rowsFrom s opened is) = _
      rw [e1]
      exact e2
    · rw [s2, s1, List.length_cons, Nat.succ_mul]
      omega

/-- **The carried rows' symbols are made**, from the tests on their own numbers and sizes. -/
theorem rowsSymbols_some (s : SingleRows) (opened : Array (Array Column)) (n : Nat)
    (hs : shapeFits s = true) (hm : s.masks = 2) (hr : s.keptRows = 0)
    (hk : ∀ w, s.layout.kept.getD w false = false) (h : ∀ i, i < n → FitsAt s opened i) :
    ∃ y, rowsSymbols s opened n = some y ∧ y.size = n * s.rows := by
  obtain ⟨y, e, sz⟩ := rowsFrom_some s opened hm hr hk (List.range n) #[]
    fun i hi => h i (List.mem_range.1 hi)
  refine ⟨y, ?_, ?_⟩
  · unfold rowsSymbols
    rw [if_pos hs]
    exact e
  · rw [sz, List.length_range]
    simp

end Johnson.Prover.Link
