-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeedReadsBack.lean: off the sample row that a sending of kind K1 lays for answer
0 (`sampleRow`, Johnson/Desc/K1/Own.lean) the reader `seedOf` (Johnson/Desc/SmpRows.lean) reads some
seed back. Which seed is not asked.

Main names: `foldl_addUnit`, `pad_length`, `e_pos`, `sampleRow_make`, `pads_pos` (the row's make:
no term before the tables' own, at least one unit); `head_flatMap`, `pad_head` (the pad's first
place lies on the mask table where there is one, else on the main table); `SeedReadsBack` (the
statement, as a definition); `seedReadsBack` (its proof).

What is not claimed. That the seed read back is the seed of which the row was made. Nothing at a
shape without an answer, without a pad, or with neither table. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.SmpRows
import Johnson.Desc.K1.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes

/-- Laying units leaves a row's terms, and adds one unit for each member of the list. -/
theorem foldl_addUnit {α : Type} (o : Nat) (part : Part) (f : α → Nat) (g : α → E) :
    ∀ (l : List α) (r : OnBytes.Row),
      (l.foldl (fun r x => r.addUnit o part (f x) (g x)) r).terms = r.terms ∧
        (l.foldl (fun r x => r.addUnit o part (f x) (g x)) r).units.size =
          r.units.size + l.length
  | [], r => ⟨rfl, rfl⟩
  | a :: l, r => by
      obtain ⟨h1, h2⟩ := foldl_addUnit o part f g l (r.addUnit o part (f a) (g a))
      refine ⟨h1, ?_⟩
      rw [List.foldl_cons, h2]
      show (r.units.push _).size + l.length = r.units.size + (l.length + 1)
      rw [Array.size_push]
      omega

/-- A pad has `Msg.e` entries. -/
theorem pad_length (m : Msg) (i : Nat) : (m.pad i).length = m.e := by
  unfold Msg.pad
  split
  simp

/-- `Msg.e` is 1 or 3. -/
theorem e_pos (m : Msg) : 0 < m.e := by
  unfold Msg.e
  split <;> omega

/-- The row's make: units alone are laid first; then the main table's term, then the mask
table's. -/
theorem sampleRow_make (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) :
    ∃ (r₀ : OnBytes.Row) (A B : Tensor), r₀.terms = #[] ∧
      r₀.units.size =
        ((List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)).length ∧
      sampleRow m o z β i y =
        { (if m.Kzk != 0 then (if m.K != 0 then r₀.add o .main A else r₀).add o .mask B
            else (if m.K != 0 then r₀.add o .main A else r₀)) with target := y } := by
  refine ⟨_, _, _, ?_, ?_, rfl⟩
  · exact (foldl_addUnit o _ _ _ _ _).1
  · rw [(foldl_addUnit o _ _ _ _ _).2]
    exact Nat.zero_add _

/-- With an answer there is at least one entry of a pad. -/
theorem pads_pos (m : Msg) (ha : 0 < m.answers) :
    0 < ((List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)).length := by
  have h0 : 0 < (m.pad 0).length := by rw [pad_length]; exact e_pos m
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h0
  exact List.length_pos_of_mem
    (List.mem_flatMap.2 ⟨0, List.mem_range.2 ha, List.mem_map.2 ⟨x, hx, rfl⟩⟩)

/-- The first member of a list made row by row. -/
theorem head_flatMap {β : Type} (n each : Nat) (hn : 0 < n) (he : 0 < each) (f : Nat → Nat → β) :
    ((List.range n).flatMap fun i => (List.range each).map fun t => f i t).head? =
      some (f 0 0) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', each = e' + 1 := ⟨each - 1, by omega⟩
  simp [List.range_succ_eq_map]

/-- The pad's places: there is a first, and its part is the mask table where there is one. -/
theorem pad_head (cs : Codes) (s : OracleShape) (places : List PadPlace) (ha : 0 < s.answers)
    (h : OnBytes.Send.pad cs s = some places) :
    ∃ p, places.head? = some p ∧
      p.part = if (OnBytes.Send.cube cs s).hasMask then Part.mask else Part.main := by
  unfold OnBytes.Send.pad at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, head_flatMap _ _ ha (by omega) _, by simp [*]⟩)

/-- The statement. -/
def SeedReadsBack : Prop :=
  ∀ (cs : Codes) (s : OracleShape) (o : Nat) (z : List E) (β y : E), 0 < s.answers →
    (OnBytes.Send.pad cs s).isSome = true → (0 < s.mainRows ∨ 0 < s.maskRows) →
    (seedOf cs s (sampleRow (Msg.of cs s) o z β 0 y)).isSome = true

/-- **Off the sample row for answer 0 some seed is read back.** -/
theorem seedReadsBack : SeedReadsBack := by
  intro cs s o z β y ha hp hr
  obtain ⟨places, hpl⟩ := Option.isSome_iff_exists.1 hp
  obtain ⟨p, hp0, hpp⟩ := pad_head cs s places ha hpl
  obtain ⟨r₀, A, B, ht, hu, hrow⟩ := sampleRow_make (Msg.of cs s) o z β 0 y
  have hu0 : 0 < r₀.units.size := by rw [hu]; exact pads_pos _ ha
  obtain ⟨u, hu1⟩ : ∃ u, r₀.units[0]? = some u := ⟨r₀.units[0], Array.getElem?_eq_getElem hu0⟩
  rw [hrow]
  unfold seedOf
  rw [hpl]
  have hc1 : (OnBytes.Send.cube cs s).hasMain = decide (0 < s.mainRows) := rfl
  have hc2 : (OnBytes.Send.cube cs s).hasMask = decide (0 < s.maskRows) := rfl
  have hk1 : (Msg.of cs s).K = s.mainRows := rfl
  have hk2 : (Msg.of cs s).Kzk = s.maskRows := rfl
  rw [hc2] at hpp
  by_cases h1 : s.mainRows = 0 <;> by_cases h2 : s.maskRows = 0
  · omega
  · have h2' : 0 < s.maskRows := by omega
    simp [hc1, hc2, hk1, hk2, h1, h2, h2', OnBytes.Row.add, ht, hp0, hu1, hpp]
  · have h1' : 0 < s.mainRows := by omega
    simp [hc1, hc2, hk1, hk2, h1, h2, h1', OnBytes.Row.add, ht, hp0, hu1, hpp]
  · have h1' : 0 < s.mainRows := by omega
    have h2' : 0 < s.maskRows := by omega
    simp [hc1, hc2, hk1, hk2, h1, h2, h1', h2', OnBytes.Row.add, ht, hp0, hu1, hpp]
    split <;> rfl

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.seedReadsBack
