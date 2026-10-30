-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Renamed.lean: what a row that is renamed to another oracle message says of
words. Theorems; no definition. It reads no block and no record of a chain.

Why. The last chain's first block takes Omega over from the shared chain's statement: its sample
rows come in renamed to Omega's number here (`Row.renamed`, OnBytes/Iop/Ground.lean).

Main names.
  `oracles_renamed`: a renamed row names n alone.
  `coefficient_renamed`: a row that names o alone, renamed to n, reads at n as the row reads at o.
  `coefficient_off_names`: a row reads as 0 on every message that it does not name.
  `tableSize_same`: two messages of one shape, in two statements with one codes, have tables of one
    size.
  `value_one`: a row that names one message alone is worth what it gives on that message's tables.
  `says_renamed`: a row that names o alone says at T, of words m, just what the row renamed to n
    says at T', of words m', where the two messages have tables of one size and m' reads at n what
    m reads at o.

`coefficient_off_names` states over a commutative ring what `Desc.K14.Law.coefficient_off`
(Johnson/Desc/K14/Law/Carry.lean) states over a field; this file reads no block's text and does not
import that one. `Means.coefficient_off` (Johnson/Desc/Means/Lays.lean) asks `Means.RowIn` of the
row.

Limits. Nothing on which rows name one message alone. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Means.Keeps
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-! ## A renamed row -/

/-- A renamed row names n alone. -/
theorem oracles_renamed (r : OnBytes.Row) (n : Nat) : ∀ x ∈ (r.renamed n).oracles, x = n := by
  intro x hx
  simp only [Row.oracles, Row.renamed, List.mem_append, Array.toList_map, List.mem_map,
    List.map_map] at hx
  rcases hx with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> rfl

/-- **A row that names o alone, renamed to n, reads at n as the row reads at o.** -/
theorem coefficient_renamed (r : OnBytes.Row) (o n : Nat) (h : ∀ x ∈ r.oracles, x = o) (pt : Part)
    (i : Nat) : ρ.val ((r.renamed n).coefficient n pt i) = ρ.val (r.coefficient o pt i) := by
  have h1 : ∀ t ∈ r.terms.toList, t.oracle = o := fun t ht => h _ (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩)))
  have h2 : ∀ u ∈ r.units.toList, u.oracle = o := fun u hu => h _ (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨u, hu, rfl⟩)))
  have h3 : ∀ w ∈ r.runs.toList, w.oracle = o := fun w hw => h _ (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inr ⟨w, hw, rfl⟩))
  have h4 : ∀ f ∈ r.forms.toList, f.oracle = o := fun f hf => h _ (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inr ⟨f, hf, rfl⟩)
  rw [Row.coefficient_val, Row.coefficient_val]
  simp only [Row.renamed, Array.toList_map, List.map_map]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        apply List.map_congr_left
        intro t ht
        simp [Function.comp, h1 t ht]
      · congr 1
        apply List.map_congr_left
        intro u hu
        simp [Function.comp, h2 u hu]
    · congr 1
      apply List.map_congr_left
      intro w hw
      simp [Function.comp, h3 w hw, Run.val]
  · congr 1
    apply List.map_congr_left
    intro f hf
    simp [Function.comp, h4 f hf]

/-- A row has the coefficient 0 on every message that it does not name. -/
theorem coefficient_off_names (r : OnBytes.Row) (o : Nat) (h : o ∉ r.oracles) (pt : Part)
    (i : Nat) : ρ.val (r.coefficient o pt i) = 0 := by
  have h1 : ∀ t ∈ r.terms.toList, t.oracle ≠ o := fun t ht c => h (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht, c⟩)))
  have h2 : ∀ u ∈ r.units.toList, u.oracle ≠ o := fun u hu c => h (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨u, hu, c⟩)))
  have h3 : ∀ w ∈ r.runs.toList, w.oracle ≠ o := fun w hw c => h (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inl (Or.inr ⟨w, hw, c⟩))
  have h4 : ∀ f ∈ r.forms.toList, f.oracle ≠ o := fun f hf c => h (by
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map]
    exact Or.inr ⟨f, hf, c⟩)
  rw [Row.coefficient_val]
  have add4 : ∀ a b c d : K, a = 0 → b = 0 → c = 0 → d = 0 → a + b + c + d = 0 := by
    intro a b c d ha hb hc hd
    rw [ha, hb, hc, hd]
    simp
  apply add4
  · apply Means.sum_map_zero
    intro t ht
    simp only [h1 t ht, false_and, if_false]
  · apply Means.sum_map_zero
    intro u hu
    simp only [h2 u hu, false_and, if_false]
  · apply Means.sum_map_zero
    intro w hw
    simp only [h3 w hw, false_and, if_false]
  · apply Means.sum_map_zero
    intro f hf
    simp only [h4 f hf, false_and, if_false]

/-- Two messages of one shape, in two statements with one codes, have tables of one size. -/
theorem tableSize_same (T T' : Statement) (o n : Nat) (x x' : OnBytes.Oracle)
    (hx : T.oracles[o]? = some x) (hx' : T'.oracles[n]? = some x') (hs : x'.shape = x.shape)
    (hc : T'.codes = T.codes) (pt : Part) : Means.tableSize T' n pt = Means.tableSize T o pt := by
  simp [Means.tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
    Statement.placeBits, hx, hx', hs, hc]

/-- A row that names one message alone: its value is what it gives on that message's two tables. -/
theorem value_one (T : Statement) (r : OnBytes.Row) (o : Nat) (ho : o < T.oracles.size)
    (hr : ∀ x ∈ r.oracles, x = o) (m : Means.Words K) :
    Means.value ρ T r m = Means.onTable ρ T r m o .main + Means.onTable ρ T r m o .mask := by
  unfold Means.value
  rw [Finset.sum_eq_single o]
  · intro b _ hb
    have hoff : b ∉ r.oracles := fun h => hb (hr b h)
    unfold Means.onTable
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      rw [coefficient_off_names ρ r b hoff, zero_mul]
    · intro i _
      rw [coefficient_off_names ρ r b hoff, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 ho) h

/-- **What a renamed row says.** -/
theorem says_renamed (T T' : Statement) (r : OnBytes.Row) (o n : Nat) (ho : o < T.oracles.size)
    (hn : n < T'.oracles.size) (hr : ∀ x ∈ r.oracles, x = o)
    (hts : ∀ pt, Means.tableSize T' n pt = Means.tableSize T o pt) (m m' : Means.Words K)
    (hm : ∀ pt i, m' n pt i = m o pt i) :
    Means.Says ρ T' (r.renamed n) m' ↔ Means.Says ρ T r m := by
  have e : ∀ pt, Means.onTable ρ T' (r.renamed n) m' n pt = Means.onTable ρ T r m o pt := by
    intro pt
    unfold Means.onTable
    rw [hts pt]
    exact Finset.sum_congr rfl fun i _ => by rw [coefficient_renamed ρ r o n hr pt i, hm pt i]
  have t : (r.renamed n).target = r.target := rfl
  unfold Means.Says
  rw [value_one ρ T' (r.renamed n) n hn (oracles_renamed r n), value_one ρ T r o ho hr, e, e, t]

end VerifiableInference.Desc.Third.Law
