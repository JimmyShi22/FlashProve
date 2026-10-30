-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LongTables.lean: WHAT STANDS IN THE TABLES THAT THE TEXT LAYS OF THE
MEMBERS' COLUMNS AT ONE POSITION (`layMembers`, Johnson/Desc/Own/Symbols.lean): entry by entry.
Theorems. No text already in the library turns.

  `layFrom_get`, `layFrom_off`: behind `layFrom table f es`: row f + j holds es's entry j; every row
    outside [f, f + |es|) holds what it held.
  `layRows_get`, `layRows_off`: the like of a yes of `layRows`.
  `OffMain L n w i`: row i lies outside member w's block of n rows (a kept member has none).
  `colAt opened i w`: member w's column at position number i. `layMember_get`, `layMember_off`.
  `main_off`: a row outside every laid member's block holds what it held.
  `main_laid`: **behind a yes of layMembers over the members ws (no number twice): at an unkept
    member w ∈ ws, at a row first w + j that lies outside every other member's block: that row
    holds w's column's main symbol j.**
Limits. The main table alone (the mask table's law is the same text with maskFirst and every member;
not typed here). «Outside every other member's block» is a premise: the layout's blocks are apart.
Nothing on the typed arrangement. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LongText

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (Tables layFrom layRows layMember layMembers)

/-! ## 1 One column into one table -/

theorem layFrom_off : ∀ (es : List E) (table : Array E) (f i : ℕ), (i < f ∨ f + es.length ≤ i) →
    (layFrom table f es).getD i zeroE = table.getD i zeroE
  | [], _, _, _, _ => rfl
  | e :: es, table, f, i, h => by
    show (layFrom (table.setIfInBounds f e) (f + 1) es).getD i zeroE = _
    rw [layFrom_off es _ (f + 1) i (by
      rw [List.length_cons] at h
      omega)]
    have hne : f ≠ i := by
      rw [List.length_cons] at h
      omega
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne]

theorem layFrom_get : ∀ (es : List E) (table : Array E) (f j : ℕ), j < es.length →
    f + es.length ≤ table.size → (layFrom table f es).getD (f + j) zeroE = es.getD j zeroE
  | [], _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | e :: es, table, f, 0, _, hs => by
    show (layFrom (table.setIfInBounds f e) (f + 1) es).getD (f + 0) zeroE = e
    rw [layFrom_off es _ (f + 1) (f + 0) (Or.inl (by omega))]
    rw [List.length_cons] at hs
    simp only [Nat.add_zero, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
    rfl
  | e :: es, table, f, j + 1, h, hs => by
    show (layFrom (table.setIfInBounds f e) (f + 1) es).getD (f + (j + 1)) zeroE = es.getD j zeroE
    rw [List.length_cons] at h hs
    rw [show f + (j + 1) = f + 1 + j by omega]
    exact layFrom_get es _ (f + 1) j (by omega) (by rw [Array.size_setIfInBounds]; omega)

theorem layRows_get {table : Array E} {f : ℕ} {col t' : Array E}
    (h : layRows table (some f) col = some t') {j : ℕ} (hj : j < col.size) :
    t'.getD (f + j) zeroE = col.getD j zeroE := by
  unfold layRows at h
  split at h
  · rename_i e
    have : col.size = 0 := by rw [← Array.length_toList, e]; rfl
    omega
  · rename_i e
    exact nomatch e
  · rename_i x xs f' e1 e2
    obtain rfl : f = f' := Option.some.inj e2
    split at h
    · rename_i hs
      rw [← Option.some.inj h, layFrom_get _ _ _ _ (by rw [← e1, Array.length_toList]; exact hj) hs,
        ← e1, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    · exact nomatch h

theorem layRows_off {table : Array E} {first : Option ℕ} {col t' : Array E}
    (h : layRows table first col = some t') {i : ℕ}
    (hi : ∀ f, first = some f → i < f ∨ f + col.size ≤ i) :
    t'.getD i zeroE = table.getD i zeroE := by
  unfold layRows at h
  split at h
  · rw [← Option.some.inj h]
  · exact nomatch h
  · rename_i x xs f' e1
    split at h
    · rw [← Option.some.inj h]
      refine layFrom_off _ _ _ _ ?_
      have := hi f' rfl
      rw [← e1, Array.length_toList]
      exact this
    · exact nomatch h

/-! ## 2 All members -/

/-- Row i lies outside member w's block of the main table (a kept member has none). -/
def OffMain (L : GroupLayout) (n : ℕ) (w i : ℕ) : Prop :=
  L.kept.getD w false = true ∨ ∀ f, L.mainFirst.getD w none = some f → i < f ∨ f + n ≤ i

theorem layMember_off {L : GroupLayout} {w : ℕ} {col : Column} {t t' : Tables}
    (h : layMember L w col t = some t') {i : ℕ} (hi : OffMain L col.main.size w i) :
    t'.main.getD i zeroE = t.main.getD i zeroE := by
  unfold layMember at h
  obtain ⟨mask, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rw [← Option.some.inj h]
  · rename_i hk
    obtain ⟨main, hn, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases hi with hi | hi
    · exact absurd hi hk
    · exact layRows_off hn hi

theorem layMember_get {L : GroupLayout} {w : ℕ} {col : Column} {t t' : Tables}
    (h : layMember L w col t = some t') (hk : L.kept.getD w false = false) {f : ℕ}
    (hf : L.mainFirst.getD w none = some f) {j : ℕ} (hj : j < col.main.size) :
    t'.main.getD (f + j) zeroE = col.main.getD j zeroE := by
  unfold layMember at h
  obtain ⟨mask, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [hk] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨main, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [hf] at hn
  exact layRows_get hn hj

/-- The column of member w at position number i. -/
def colAt (opened : Array (Array Column)) (i w : ℕ) : Option Column :=
  (opened[w]?).bind (·[i]?)

/-- A row outside every laid member's block holds what it held. -/
theorem main_off (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' → ∀ r,
      (∀ w ∈ ws, ∀ c, colAt opened i w = some c → OffMain L c.main.size w r) →
      t'.main.getD r zeroE = t.main.getD r zeroE
  | [], t, t', h, _, _ => by rw [← Option.some.inj h]
  | w :: ws, t, t', h, r, ho => by
    unfold layMembers at h
    obtain ⟨col, hc, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h⟩ := Option.bind_eq_some_iff.1 h
    rw [main_off L opened i ws t₁ t' h r fun w' hw' => ho w' (List.mem_cons_of_mem _ hw'),
      layMember_off h1 (ho w List.mem_cons_self col hc)]

/-- **WHAT STANDS IN THE MAIN TABLE.** -/
theorem main_laid (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' → ws.Nodup →
      ∀ w ∈ ws, L.kept.getD w false = false → ∀ f, L.mainFirst.getD w none = some f →
      ∀ c, colAt opened i w = some c → ∀ j, j < c.main.size →
      (∀ w' ∈ ws, w' ≠ w → ∀ c', colAt opened i w' = some c' →
        OffMain L c'.main.size w' (f + j)) →
      t'.main.getD (f + j) zeroE = c.main.getD j zeroE
  | [], _, _, _, _, _, hw, _, _, _, _, _, _, _, _ => nomatch hw
  | v :: ws, t, t', h, nd, w, hw, hk, f, hf, c, hc, j, hj, ho => by
    unfold layMembers at h
    obtain ⟨col, hcol, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h3⟩ := Option.bind_eq_some_iff.1 h2
    obtain ⟨nv, nd'⟩ := List.nodup_cons.1 nd
    rcases List.mem_cons.1 hw with rfl | hw'
    · obtain rfl : col = c := Option.some.inj (hcol.symm.trans hc)
      rw [main_off L opened i ws t₁ t' h3 (f + j) fun w' hw' c' hc' =>
        ho w' (List.mem_cons_of_mem _ hw') (fun e => nv (e ▸ hw')) c' hc']
      exact layMember_get h1 hk hf hj
    · exact main_laid L opened i ws t₁ t' h3 nd' w hw' hk f hf c hc j hj fun w' hw'' hne =>
        ho w' (List.mem_cons_of_mem _ hw'') hne

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layFrom_get
#print axioms VerifiableInference.Desc.LinkJoin.layRows_get
#print axioms VerifiableInference.Desc.LinkJoin.layRows_off
#print axioms VerifiableInference.Desc.LinkJoin.main_off
#print axioms VerifiableInference.Desc.LinkJoin.main_laid
