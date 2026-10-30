-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyPairs.lean: the conditions on the two lookups of a key file as one test that runs:
the second lookup's runs against the units of the library's layout.

Definitions, statements and proofs. Johnson/Top/H/KeyPortAt.lean asks fifteen things of the two
lookups (`RangesOK`). Two of them speak of all 1,527,800 pairs of rows of the library's layout. In
that layout a unit with two bytes an entry has its low bytes in consecutive rows and its high bytes
as many rows further (`pairAux`, Inst/Model/Layout.lean): this is what a run of a lookup with two
digits reads. So the two conditions are a comparison of two short lists: the runs, and the units.
Main names:
  `unitsT`: for each unit with two bytes an entry: the first row of its low bytes, and the number of
    rows of each byte.
  `pair_of`, `pair_to`: every pair lies in a unit; every row of the low bytes of a unit is the first
    row of a pair (`pairAux_mem`, `pairAux_surj`, Inst/Model/LayoutBridge.lean).
  `inUnit`, `chk1`, `P1_of`: the test that every run lies inside a unit's low bytes and has its
    number of rows as stride; its value true gives (P1).
  `stretchesOf`, `chk2`, `P2_of`: the test that the low bytes of every unit are reached, without a
    gap, by the runs inside them that have that stride (by the verifier's own `Wf.noGap`); its
    value true gives (P2).
  `rangesB`, `rangesB_sound`, `rangesB_d`: one test for all fifteen clauses, and that the tables'
    sizes are the lookups' own; its value true gives `RangesOK`.


Limits: no lookups are given here, so the test is run on nothing in this file. The limits of
Johnson/Top/H/KeyPortAt.lean hold, but for (P1) and (P2): a row number of the programs' matrix is
taken as the same row number of the library's index matrix; nothing
on multiplicities or on knowledge soundness.
-/
import Johnson.Top.H.KeyPortAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Inst.Model Inst.Model.All Cb Cm Cm.WfGl
open Inst.Model.Layout (kRef hRef m2 units twoByte off hU pair pairAux)
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ### The pairs of rows of the library's layout, unit by unit -/

/-- The units with two bytes an entry: the first row of the low bytes, and the number of rows of
each byte. -/
def unitsT : List (ℕ × ℕ) :=
  (twoByte (units ppref)).map fun p => (off kRef (units ppref) p.1, hU kRef p.2)

theorem pairs_total : Layout.Bridge.pairsOf kRef (twoByte (units ppref)) = 1527800 :=
  Layout.Sanity.plan_numbers.1

/-- Every pair lies in a unit. -/
theorem pair_of (v : ℕ) (hv : v < 1527800) :
    ∃ t ∈ unitsT, ∃ r < t.2, pairY v 0 = t.1 + r ∧ pairY v 1 = t.1 + t.2 + r := by
  obtain ⟨p, hp, r, hr, e⟩ := Layout.Bridge.pairAux_mem kRef (units ppref)
    (twoByte (units ppref)) v (by rw [pairs_total]; exact hv)
  refine ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, r, hr, ?_, ?_⟩
  · show (pairAux kRef (units ppref) (twoByte (units ppref)) v).1 = _
    rw [e]
  · show (pairAux kRef (units ppref) (twoByte (units ppref)) v).2 = _
    rw [e]

/-- Every row of the low bytes of a unit is the first row of a pair. -/
theorem pair_to (t : ℕ × ℕ) (ht : t ∈ unitsT) (r : ℕ) (hr : r < t.2) :
    ∃ v < 1527800, pairY v 0 = t.1 + r ∧ pairY v 1 = t.1 + t.2 + r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨q, hq, e⟩ := Layout.Bridge.pairAux_surj kRef (units ppref)
    (twoByte (units ppref)) p hp r hr
  rw [pairs_total] at hq
  refine ⟨q, hq, ?_, ?_⟩
  · show (pairAux kRef (units ppref) (twoByte (units ppref)) q).1 = _
    rw [e]
  · show (pairAux kRef (units ppref) (twoByte (units ppref)) q).2 = _
    rw [e]

/-! ### Two tests that run -/

/-- The run lies inside a stretch of T and has its stride. -/
def inUnit (T : List (ℕ × ℕ)) (ρ : WfRun) : Bool :=
  T.any fun t => ρ.stride == t.2 && decide (t.1 ≤ ρ.firstRow) &&
    decide (ρ.firstRow + ρ.places ≤ t.1 + t.2)

/-- Every run of the lookup does. -/
def chk1 (T : List (ℕ × ℕ)) (l : WfLookup) : Bool := l.parts.all fun p => p.runs.all (inUnit T)

/-- The stretches of rows of the runs that lie inside the stretch t and have its stride. -/
def stretchesOf (l : WfLookup) (t : ℕ × ℕ) : List (ℕ × ℕ) :=
  l.parts.flatMap fun p =>
    (p.runs.filter fun r => r.stride == t.2 && decide (t.1 ≤ r.firstRow) &&
      decide (r.firstRow + r.places ≤ t.1 + t.2)).map fun r => (r.firstRow, r.firstRow + r.places)

/-- Every stretch of T is reached, without a gap, by the runs inside it that have its stride. -/
def chk2 (T : List (ℕ × ℕ)) (l : WfLookup) : Bool :=
  T.all fun t => OnBytes.Wf.noGap (t.1 + t.2) t.1
    ((stretchesOf l t).mergeSort fun a b => decide (a.1 ≤ b.1))

theorem P1_of (l : WfLookup) (hw : l.digitWeight.length = 2) (h : chk1 unitsT l = true) :
    ∀ p ∈ l.parts, ∀ ρ ∈ p.runs, ∀ u, hasPl ρ u →
      ∃ v < 1527800, ∀ q < l.digitWeight.length, pairY v q = rowOf ρ u q := by
  intro p hp ρ hρ u hu
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h p hp) ρ hρ
  obtain ⟨t, ht, e⟩ := List.any_eq_true.1 h1
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
  obtain ⟨⟨e1, e2⟩, e3⟩ := e
  have a1 := hu.1
  have a2 := hu.2
  obtain ⟨v, hv, g0, g1⟩ := pair_to t ht (ρ.firstRow + (u - ρ.firstPlace) - t.1) (by omega)
  refine ⟨v, hv, fun q hq => ?_⟩
  rw [hw] at hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.le_of_lt_succ hq) with rfl | rfl
  · rw [g0]
    unfold rowOf
    omega
  · rw [g1]
    unfold rowOf
    omega

theorem P2_of (l : WfLookup) (hw : l.digitWeight.length = 2) (h : chk2 unitsT l = true) :
    ∀ v < 1527800, ∃ p ∈ l.parts, ∃ ρ ∈ p.runs, ∃ u, hasPl ρ u ∧
      ∀ q < l.digitWeight.length, pairY v q = rowOf ρ u q := by
  intro v hv
  obtain ⟨t, ht, r, hr, g0, g1⟩ := pair_of v hv
  have h1 := List.all_eq_true.1 h t ht
  obtain ⟨x, hx, e1, e2⟩ := noGap_mem _ _ _ h1 (t.1 + r) (Nat.le_add_right _ _) (by omega)
  rw [List.mem_mergeSort] at hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hρ1, hρ2⟩ := List.mem_filter.1 hρ
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hρ2
  have hs : ρ.stride = t.2 := hρ2.1.1
  have e1' : ρ.firstRow ≤ t.1 + r := e1
  have e2' : t.1 + r < ρ.firstRow + ρ.places := e2
  refine ⟨p, hp, ρ, hρ1, ρ.firstPlace + (t.1 + r - ρ.firstRow), ⟨Nat.le_add_right _ _, by omega⟩,
    fun q hq => ?_⟩
  rw [hw] at hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.le_of_lt_succ hq) with rfl | rfl
  · rw [g0]
    unfold rowOf
    omega
  · rw [g1]
    unfold rowOf
    rw [hs]
    omega

/-! ### One test for all clauses -/

/-- The test on two lookups. -/
def rangesB (l₀ l₁ : WfLookup) : Bool :=
  l₀.parts.length == 12 && l₁.parts.length == 12 &&
  ((List.range 12).all fun j => (partAt l₀ j).logPlaces == 18) &&
  ((List.range 12).all fun j => (partAt l₁ j).logPlaces == 17) &&
  l₀.offset.toNat == 128 && l₁.offset.toNat == 4096 && l₁.digitWeight == [1, 256] &&
  decide (l₀.paddingKey.toNat < 2 ^ 8) && decide (l₁.paddingKey.toNat < 2 ^ 13) &&
  (l₀.parts.all fun p => OnBytes.Wf.runsOk p.logPlaces 0 p.runs) &&
  (l₁.parts.all fun p => OnBytes.Wf.runsOk p.logPlaces 0 p.runs) &&
  (l₀.parts.all fun p => p.runs.all fun r => decide (r.firstRow + r.places ≤ hRef)) &&
  OnBytes.Wf.coversAllRows ⟨18, hRef⟩ l₀ && chk1 unitsT l₁ && chk2 unitsT l₁ &&
  l₀.d == 8 && l₁.d == 13

/-- Its value true gives all that Johnson/Top/H/KeyPortAt.lean asks of the two lookups. -/
theorem rangesB_sound (l₀ l₁ : WfLookup) (h : rangesB l₀ l₁ = true) : RangesOK l₀ l₁ := by
  unfold rangesB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩, _⟩, _⟩ := h
  have hw : l₁.digitWeight.length = 2 := by rw [a7]; rfl
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    P1_of l₁ hw a14, P2_of l₁ hw a15⟩

/-- The tables' sizes are the lookups' own. -/
theorem rangesB_d (l₀ l₁ : WfLookup) (h : rangesB l₀ l₁ = true) : l₀.d = 8 ∧ l₁.d = 13 := by
  unfold rangesB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

end Johnson.Pack

#print axioms Johnson.Pack.rangesB_sound
#print axioms Johnson.Pack.pair_of
#print axioms Johnson.Pack.pair_to
#print axioms Johnson.Pack.P1_of
#print axioms Johnson.Pack.P2_of
