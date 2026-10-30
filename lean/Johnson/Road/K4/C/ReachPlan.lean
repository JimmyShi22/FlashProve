-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ReachPlan.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4): each of the six families of tables at the
lookup's point is found under its name, and ALL its entries are there (Reach, ReadersReturn.lean):
as many as the matrix has parts, columns and runs of rows. From the verifier's lines that make the
layout, the reads and the tables' places. The library's laws on these places:
Johnson/Road/FormsKeysTab.lean, FormsKeysWorld.lean, FormsKeysPoint.lean. Statements and proofs.

  `tab_le_total`    a family ends at or before the first free entry behind all families.
  `reach_family`    one family, known by its name, its matrix and the rows of a run.
  **`reach_six`**     the six.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. UNDER THE
LIBRARY's ELEVEN SWITCHES ALONE. That the reads' array has a column (hK) and that the last entry's
row fits 32 bits (hb) are hypotheses on the plan's tree, not on the layout. Public data alone:
whether an entry IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.ReadersReturn
import Johnson.Road.FormsKeysTab
import Johnson.Road.FormsKeysAdmit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Shape Reads TableAsk TableAt layParts layTables tableAsks layout
  readsOf)

/-- A family ends at or before the first free entry behind all families. -/
theorem tab_le_total (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    p ≤ r.2.2 ∧ ∀ x ∈ r.1, x.first + x.len ≤ r.2.2
  | [], p, r, h => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    exact ⟨Nat.le_refl _, fun x hx => by cases hx⟩
  | a :: rest, p, r, h => by
    have hle := layParts_le mats a a.parts p
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      obtain ⟨i1, i2⟩ := tab_le_total mats rest _ r' h1
      refine ⟨Nat.le_trans hle i1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with e | hx
      · subst e
        show p + ((layParts mats a a.parts p).2 - p) ≤ r'.2.2
        omega
      · exact i2 x hx

variable {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **One family**: it is found under its name, and all its entries are there. -/
theorem reach_family (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hK : v.K3 ≠ 0) (hb : r.2.2 / v.K3 < 2 ^ 32) (n : String) (mat L : ℕ) (hmat : mat ≤ 5)
    (ha : ∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
      a.parts = partsM v.y mat ∧ a.L = L) :
    ∃ tb, v.tabAt n = some tb ∧
      Reach v tb (partsM v.y mat * (colsM v.y mat * (rowsM v.y mat / L))) := by
  obtain ⟨a, ha, an, aM, ap, aL⟩ := ha
  obtain ⟨hc, hnames⟩ := layTables_chain _ _ 0 r hl
  rw [← ht] at hc hnames
  have hmem : n ∈ v.tab.map (·.name) := by
    rw [hnames, ← an]
    exact List.mem_map_of_mem (f := fun q : TableAsk => q.name) ha
  obtain ⟨x0, hx0, e0⟩ := List.mem_map.mp hmem
  obtain ⟨x, hx⟩ : ∃ x, (v.tab.find? fun t => t.name == n) = some x := by
    cases hf : v.tab.find? fun t => t.name == n with
    | some x => exact ⟨x, rfl⟩
    | none =>
      have h0 := List.find?_eq_none.mp hf x0 hx0
      rw [e0] at h0
      simp at h0
  have htb : v.tabAt n = some x.first := by
    unfold Env.tabAt
    rw [hx]
    rfl
  obtain ⟨x', hx'm, hx'n, hx'f⟩ := tabAt_mem htb
  have e1 := chain_first v.tab 0 hc x' hx'm
  rw [hx'f] at e1
  have hx'r : x' ∈ r.1 := by
    rw [← ht]
    exact hx'm
  obtain ⟨q', q1, q2, q3⟩ := layTables_len _ _ 0 r hl x' hx'r
  have e3 : q' = a := ask_of_name hrd q1 ha (q2.symm.trans (hx'n.trans an.symm))
  subst e3
  have hsz : ∀ p, p < q'.parts →
      (matsR v.y v.g).getD (q'.M0 + p) (0, 0) = (rowsM v.y mat, colsM v.y mat) := by
    intro p hp
    rw [ap] at hp
    rw [aM]
    exact tails_pair v.y hg hmat hp
  rw [layParts_eq _ q' _ _ hsz] at q3
  have q3' : x'.first + x'.len =
      x'.first + q'.parts * (colsM v.y mat * (rowsM v.y mat / q'.L)) := q3
  have hlen : x'.len = partsM v.y mat * (colsM v.y mat * (rowsM v.y mat / L)) := by
    rw [← ap, ← aL]
    omega
  have htot := (tab_le_total _ _ 0 r hl).2 x' hx'r
  rw [hx'f] at htot
  exact ⟨x.first, htb, reach_of_tab e1 (Nat.le_of_eq hlen.symm) hK
    (Nat.lt_of_le_of_lt (Nat.div_le_div_right htot) hb)⟩

/-- **THE SIX FAMILIES AT THE LOOKUP's POINT ARE FOUND, AND ALL THEIR ENTRIES ARE THERE.**
CONDITIONAL: on the verifier's lines, the switches, hK and hb. The pairs: a family's name and its
matrix's number; long tables first. -/
theorem reach_six (hy : layout h pc = .ok v.y) (S : Switches h) (hg : v.g < v.y.NGr)
    (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hK : v.K3 ≠ 0) (hb : r.2.2 / v.K3 < 2 ^ 32) :
    (∀ p ∈ [("af" ++ "@" ++ "Z", 0), ("qa" ++ "@" ++ "Z", 3), ("xbI" ++ "@" ++ "Z", 4),
        ("xbO" ++ "@" ++ "Z", 5)], ∃ tb, v.tabAt p.1 = some tb ∧
      Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / 2 ^ v.y.h.la)))) ∧
    (∀ p ∈ [("ad" ++ "@" ++ "zt", 1), ("ar" ++ "@" ++ "zt", 2)], ∃ tb, v.tabAt p.1 = some tb ∧
      Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / v.y.T)))) := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := points_of_layout hy S hrd
  obtain ⟨n0, n3, n4, n5, n1, n2⟩ := six_numbers v.y rd v.g p1 p2 p3 p4 p5 p6
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact reach_family hg hrd hl ht hK hb _ 0 _ (by omega) n0
    · exact reach_family hg hrd hl ht hK hb _ 3 _ (by omega) n3
    · exact reach_family hg hrd hl ht hK hb _ 4 _ (by omega) n4
    · exact reach_family hg hrd hl ht hK hb _ 5 _ (by omega) n5
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact reach_family hg hrd hl ht hK hb _ 1 _ (by omega) n1
    · exact reach_family hg hrd hl ht hK hb _ 2 _ (by omega) n2

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tab_le_total
#print axioms OnBytes.Road.K4.C.reach_family
#print axioms OnBytes.Road.K4.C.reach_six
