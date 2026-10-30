-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Laid.lean: CONDITIONAL.

Not shown here. That layTables returns: a hypothesis. Nothing on weights or on cells: places alone.
No example is known. No property is claimed.

THE HONEST SIDE's WALK OVER THE FAMILIES OF TABLES FINDS THE PLACE THAT THE VERIFIER HAS LAID. The
verifier lays the families of tables of the reads one behind the other, and each family's parts
likewise (layTables, layParts: OnBytes/Model/LayerForms.lean). The honest side of the sub-protocol
K4 goes from an entry's number back to its family and its part (famPart,
Johnson/Desc/K4/Honest/Cells.lean; the first family whose stretch holds the number).

  wd                the number of entries of a part's table.
  Laid              a list of families lies one behind the other from entry p on, each as layParts
                    lays it, none empty.
  laid_of_layTables what layTables returns is such a list, and its families are those asked for.
  parts_ge, parts_end, parts_first, parts_len   a family's parts: where they begin and end.
  famPart_layParts  entry j of the part (M, st) of a family: famPart finds M and j.
  famFirst, famLen  a family's first entry and its number of entries, as the honest side computes
                    them.
  find_fam          the first family whose stretch holds an entry of a part of the family q is q.
  laid_mem          a family of such a list, from its own first entry.
  parts_cover       every entry of a family's stretch lies in one of its parts.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Road.FormsKeysMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (TableAsk TableAt layParts layTables)
open OnBytes.Desc.First.K4.Honest (famPart)

/-- The number of entries of the table of the part M: one for each column and each run of L rows. -/
def wd (mats : Array (ℕ × ℕ)) (L M : ℕ) : ℕ := (mats.getD M (0, 0)).2 * ((mats.getD M (0, 0)).1 / L)

/-- A list of families lies one behind the other from entry p on. -/
def Laid (mats : Array (ℕ × ℕ)) : List (TableAsk × List (ℕ × ℕ)) → ℕ → Prop
  | [], _ => True
  | q :: l, p => q.2 = (layParts mats q.1 q.1.parts p).1 ∧ p < (layParts mats q.1 q.1.parts p).2 ∧
      Laid mats l (layParts mats q.1 q.1.parts p).2

/-- One part more. -/
theorem layParts_step (mats : Array (ℕ × ℕ)) (a : TableAsk) (n p : ℕ) :
    layParts mats a (n + 1) p =
      ((a.M0 + (a.parts - (n + 1)), p) ::
        (layParts mats a n (p + wd mats a.L (a.M0 + (a.parts - (n + 1))))).1,
       (layParts mats a n (p + wd mats a.L (a.M0 + (a.parts - (n + 1))))).2) := rfl

/-- The parts end no earlier than they begin. -/
theorem parts_end (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p, p ≤ (layParts mats a n p).2
  | 0, _ => Nat.le_refl _
  | n + 1, p => by
    rw [layParts_step]
    exact Nat.le_trans (Nat.le_add_right _ _) (parts_end mats a n _)

/-- Each part lies inside the family's stretch. -/
theorem parts_ge (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p, ∀ m ∈ (layParts mats a n p).1,
    p ≤ m.2 ∧ m.2 + wd mats a.L m.1 ≤ (layParts mats a n p).2
  | 0, _, m, hm => by cases hm
  | n + 1, p, m, hm => by
    rw [layParts_step] at hm ⊢
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨Nat.le_refl _, parts_end mats a n _⟩
    · obtain ⟨h1, h2⟩ := parts_ge mats a n _ m hm
      exact ⟨Nat.le_trans (Nat.le_add_right _ _) h1, h2⟩

/-- What layTables returns lies so, and its families are those asked for. -/
theorem laid_of_layTables (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    Laid mats r.2.1 p ∧ r.2.1.map (·.1) = asks
  | [], p, r, h => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    exact ⟨trivial, rfl⟩
  | a :: rest, p, r, h => by
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
      obtain ⟨i1, i2⟩ := laid_of_layTables mats rest _ r' h1
      have hne : (layParts mats a a.parts p).2 ≠ p := fun e =>
        hq (by rw [e]; exact beq_self_eq_true _)
      have hge := parts_end mats a a.parts p
      have hlt : p < (layParts mats a a.parts p).2 := by omega
      refine ⟨⟨rfl, hlt, i1⟩, ?_⟩
      show a :: r'.2.1.map (·.1) = a :: rest
      rw [i2]

/-- **Entry j of the part (M, st): famPart finds M and j.** n: the parts still to pass. -/
theorem famPart_layParts (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p, n ≤ a.parts →
    ∀ m ∈ (layParts mats a n p).1, ∀ j, j < wd mats a.L m.1 →
      famPart mats a.L n (a.M0 + (a.parts - n)) (m.2 - p + j) = (m.1, j)
  | 0, _, _, m, hm, _, _ => by cases hm
  | n + 1, p, hn, m, hm, j, hj => by
    rw [layParts_step] at hm
    have hs : famPart mats a.L (n + 1) (a.M0 + (a.parts - (n + 1))) (m.2 - p + j) =
        if m.2 - p + j < wd mats a.L (a.M0 + (a.parts - (n + 1))) then
          (a.M0 + (a.parts - (n + 1)), m.2 - p + j)
        else famPart mats a.L n (a.M0 + (a.parts - (n + 1)) + 1)
          (m.2 - p + j - wd mats a.L (a.M0 + (a.parts - (n + 1)))) := rfl
    rw [hs]
    rcases List.mem_cons.mp hm with rfl | hm
    · have e : p - p + j = j := by omega
      show (if p - p + j < wd mats a.L (a.M0 + (a.parts - (n + 1))) then _ else _) = _
      rw [e, if_pos hj]
    · obtain ⟨h1, -⟩ := parts_ge mats a n _ m hm
      rw [if_neg (by omega)]
      have e1 : a.M0 + (a.parts - (n + 1)) + 1 = a.M0 + (a.parts - n) := by omega
      have e2 : m.2 - p + j - wd mats a.L (a.M0 + (a.parts - (n + 1))) =
          m.2 - (p + wd mats a.L (a.M0 + (a.parts - (n + 1)))) + j := by omega
      rw [e1, e2]
      exact famPart_layParts mats a n _ (by omega) m hm j hj

/-- A family's first entry, as the honest side computes it. -/
def famFirst (q : TableAsk × List (ℕ × ℕ)) : ℕ := (q.2.head?.map (·.2)).getD 0

/-- A family's number of entries, as the honest side computes it. -/
def famLen (mats : Array (ℕ × ℕ)) (q : TableAsk × List (ℕ × ℕ)) : ℕ :=
  q.2.foldl (fun s m => let mk := mats.getD m.1 (0, 0); s + mk.2 * (mk.1 / q.1.L)) 0

/-- The parts' numbers of entries add up to the family's stretch. -/
theorem parts_len (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p s,
    (layParts mats a n p).1.foldl
      (fun s m => let mk := mats.getD m.1 (0, 0); s + mk.2 * (mk.1 / a.L)) s + p =
      s + (layParts mats a n p).2
  | 0, p, s => rfl
  | n + 1, p, s => by
    rw [layParts_step, List.foldl_cons]
    have ih := parts_len mats a n (p + wd mats a.L (a.M0 + (a.parts - (n + 1))))
      (s + wd mats a.L (a.M0 + (a.parts - (n + 1))))
    show (layParts mats a n (p + wd mats a.L (a.M0 + (a.parts - (n + 1))))).1.foldl _
      (s + wd mats a.L (a.M0 + (a.parts - (n + 1)))) + p = _
    omega

/-- A family that is not empty begins at p. -/
theorem parts_first (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p, p < (layParts mats a n p).2 →
    (((layParts mats a n p).1.head?).map (·.2)).getD 0 = p
  | 0, _, h => absurd h (Nat.lt_irrefl _)
  | _ + 1, _, _ => rfl

/-- **The first family whose stretch holds an entry of the family q is q.** mk: what the honest side
makes of a family; of it the first entry and the number of entries are read. -/
theorem find_fam {β : Type} (mats : Array (ℕ × ℕ)) (mk : TableAsk × List (ℕ × ℕ) → β)
    (first len : β → ℕ) (h1 : ∀ q, first (mk q) = famFirst q)
    (h2 : ∀ q, len (mk q) = famLen mats q) : ∀ (l : List (TableAsk × List (ℕ × ℕ))) (p : ℕ),
    Laid mats l p → ∀ q ∈ l, ∀ m ∈ q.2, ∀ j, j < wd mats q.1.L m.1 →
      ((l.map mk).find? fun f => decide (first f ≤ m.2 + j) && decide (m.2 + j < first f + len f)) =
        some (mk q) ∧ famFirst q ≤ m.2 ∧ p ≤ famFirst q
  | [], _, _, q, hq, _, _, _, _ => by cases hq
  | x :: l, p, hL, q, hq, m, hm, j, hj => by
    obtain ⟨e1, e2, e3⟩ := hL
    have f1 : famFirst x = p := by
      unfold famFirst
      rw [e1]
      exact parts_first mats x.1 x.1.parts p e2
    have f2 : famLen mats x + p = (layParts mats x.1 x.1.parts p).2 := by
      have := parts_len mats x.1 x.1.parts p 0
      unfold famLen
      rw [e1]
      omega
    rw [List.map_cons, List.find?_cons, h1, h2, f1]
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [e1] at hm
      obtain ⟨g1, g2⟩ := parts_ge mats q.1 q.1.parts p m hm
      have c : (decide (p ≤ m.2 + j) && decide (m.2 + j < p + famLen mats q)) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        omega
      rw [c]
      exact ⟨rfl, by omega, by omega⟩
    · obtain ⟨i1, i2, i3⟩ := find_fam mats mk first len h1 h2 l _ e3 q hq m hm j hj
      have c : (decide (p ≤ m.2 + j) && decide (m.2 + j < p + famLen mats x)) = false := by
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        right
        omega
      rw [c]
      exact ⟨i1, i2, by omega⟩

/-- A family of such a list is laid by layParts from its own first entry, and is not empty. -/
theorem laid_mem (mats : Array (ℕ × ℕ)) : ∀ (l : List (TableAsk × List (ℕ × ℕ))) (p : ℕ),
    Laid mats l p → ∀ q ∈ l, q.2 = (layParts mats q.1 q.1.parts (famFirst q)).1 ∧
      famFirst q + famLen mats q = (layParts mats q.1 q.1.parts (famFirst q)).2
  | [], _, _, q, hq => by cases hq
  | x :: l, p, hL, q, hq => by
    obtain ⟨e1, e2, e3⟩ := hL
    rcases List.mem_cons.mp hq with rfl | hq
    · have f1 : famFirst q = p := by
        unfold famFirst
        rw [e1]
        exact parts_first mats q.1 q.1.parts p e2
      have f2 := parts_len mats q.1 q.1.parts p 0
      rw [f1]
      refine ⟨e1, ?_⟩
      unfold famLen
      rw [e1]
      omega
    · exact laid_mem mats l _ e3 q hq

/-- Every entry of a family's stretch lies in one of its parts. -/
theorem parts_cover (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ n p e, p ≤ e →
    e < (layParts mats a n p).2 → ∃ m ∈ (layParts mats a n p).1, m.2 ≤ e ∧ e < m.2 + wd mats a.L m.1
  | 0, p, e, h1, h2 => by
    have : e < p := h2
    omega
  | n + 1, p, e, h1, h2 => by
    rw [layParts_step] at h2 ⊢
    by_cases c : e < p + wd mats a.L (a.M0 + (a.parts - (n + 1)))
    · exact ⟨_, List.mem_cons_self, h1, c⟩
    · obtain ⟨m, hm, g1, g2⟩ := parts_cover mats a n _ e (by omega) h2
      exact ⟨m, List.mem_cons_of_mem _ hm, g1, g2⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.layParts_step
#print axioms OnBytes.Road.K4.C.parts_end
#print axioms OnBytes.Road.K4.C.parts_ge
#print axioms OnBytes.Road.K4.C.laid_of_layTables
#print axioms OnBytes.Road.K4.C.famPart_layParts
#print axioms OnBytes.Road.K4.C.parts_len
#print axioms OnBytes.Road.K4.C.parts_first
#print axioms OnBytes.Road.K4.C.find_fam
#print axioms OnBytes.Road.K4.C.laid_mem
#print axioms OnBytes.Road.K4.C.parts_cover
