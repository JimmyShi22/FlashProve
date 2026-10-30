-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyPlan/LookupOkA.lean: four of the six clauses of the test of form of a lookup's public
inputs hold at what the block of the ranges hands over, if the lookup passes that block's own two
tests.

The block of a lookup refuses public inputs that fail `Lkp.Public.ok` (OnBytes/Iop/Lkp.lean): six
clauses. The block of a key's ranges makes these inputs from a lookup of the item "ranges" and the
matrix's size (`Wf.lookupOf`, OnBytes/Iop/Wf.lean), and has tests of its own on the two
(`Wf.lookupOk`, `Wf.fitsMatrix`, OnBytes/Key/Ranges.lean). Here: the clauses on the sizes and on the
order of the last key level follow from these two tests; the clauses on the blocks of tree numbers
and on the pieces of the table hold of `Wf.lookupOf` by its text.

Main names:
  `lookupOk_facts`: what is used of `Wf.lookupOk`.
  `partsFit_all`, `partsFit_sum`: what `Wf.partsFit` says of each part, and of the sum of the keys.
  `allPairs_of_distinct`: a list that passes `distinctNats` passes the test on pairs.
  `lt_foldl_min`: a number below the start and below each member is below their least.
  `sizesOK_lookupOf`, `keysOK_lookupOf`, `tablesOK_lookupOf`, `orderOK_lookupOf`: the four clauses.

Limits: nothing on the other two clauses (`paddingOK`, `onlyPadding`), so nothing on
`Lkp.Public.ok`. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Iop.Wf

set_option autoImplicit false

namespace OnBytes.KeyPlan
open OnBytes.Params (WfPart WfLookup)

/-- What is used here of the test on a lookup by itself. -/
theorem lookupOk_facts {l : WfLookup} (h : Wf.lookupOk Wf.fBits l = true) :
    1 ≤ l.mu ∧ l.mu ≤ 6 ∧ l.live < 2 ^ l.mu ∧ 2 ≤ Wf.planesOf l ∧ Wf.planesOf l ≤ 62 ∧
      l.d + Wf.planesOf l < 64 ∧ l.parts ≠ [] ∧ distinctNats l.firstBound = true := by
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, -⟩, c7⟩, -⟩, c9⟩, -⟩, -⟩, -⟩, c13⟩, -⟩ := h
  exact ⟨c1, c2, c3, c4, c5, c7, c9, c13⟩

/-- What the test on a lookup and the matrix says of each part. -/
theorem partsFit_all (m : Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (k : Nat),
    Wf.partsFit m l k ps = true → ∀ p ∈ ps, 1 ≤ p.logPlaces + m.kCol ∧
      p.logPlaces + m.kCol < Wf.planesOf l ∧ ∀ v ∈ l.firstBound, v + 1 < p.logPlaces + m.kCol
  | [], _, _ => fun _ hp => by cases hp
  | q :: ps, k, h => by
    unfold Wf.partsFit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2⟩
    · exact partsFit_all m l ps _ h.2 p hp'

/-- The keys so far and those of the parts that follow are fewer than 2 ^ planes. -/
theorem partsFit_sum (m : Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (k : Nat),
    Wf.partsFit m l k ps = true → k < 2 ^ Wf.planesOf l →
      k + (ps.map fun p => 2 ^ (p.logPlaces + m.kCol)).sum < 2 ^ Wf.planesOf l
  | [], k, _, hk => by
    show k + 0 < _
    exact hk
  | q :: ps, k, h, _ => by
    unfold Wf.partsFit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    have ih := partsFit_sum m l ps _ h.2 h.1.2
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc]
    exact ih

/-- A list in which no number occurs twice passes the test on pairs. -/
theorem allPairs_of_distinct : ∀ l : List Nat, distinctNats l = true →
    Lkp.allPairs (fun a b => a != b) l = true
  | [], _ => rfl
  | a :: l, h => by
    have h' : ((!l.contains a) && distinctNats l) = true := h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h'
    show (l.all (fun b => a != b) && Lkp.allPairs (fun a b => a != b) l) = true
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun b hb => bne_iff_ne.2 fun e => ?_, allPairs_of_distinct l h'.2⟩
    subst e
    have hc : l.contains a = true := List.elem_eq_true_of_mem hb
    rw [h'.1] at hc
    cases hc

/-- A number below the start and below each member is below the least of them. -/
theorem lt_foldl_min : ∀ (l : List Nat) (a c : Nat), c < a → (∀ v ∈ l, c < v) →
    c < l.foldl min a
  | [], _, _, h, _ => h
  | b :: l, a, c, h, hl =>
    lt_foldl_min l (min a b) c (Nat.lt_min.2 ⟨h, hl b (List.mem_cons_self ..)⟩)
      fun v hv => hl v (List.mem_cons_of_mem _ hv)

section
variable (id : Nat) (m : Wf.Matrix) (l : WfLookup)

/-- A part of the public inputs is a part of the lookup. -/
theorem mem_parts {x : Nat} (hx : x ∈ (Wf.lookupOf id m l).parts) :
    ∃ p ∈ l.parts, p.logPlaces + m.kCol = x :=
  List.mem_map.1 hx

/-- **The clause on the sizes.** -/
theorem sizesOK_lookupOf (hl : Wf.lookupOk Wf.fBits l = true) (hf : Wf.fitsMatrix m l = true) :
    (Wf.lookupOf id m l).sizesOK = true := by
  obtain ⟨c1, c2, c3, c4, c5, c7, c9, -⟩ := lookupOk_facts hl
  have hs : (Wf.lookupOf id m l).allKeys < 2 ^ Wf.planesOf l := by
    have h := partsFit_sum m l l.parts 0 hf (Nat.two_pow_pos _)
    rw [Nat.zero_add] at h
    have e : (Wf.lookupOf id m l).allKeys =
        (l.parts.map fun p => 2 ^ (p.logPlaces + m.kCol)).sum := by
      show ((l.parts.map fun p => p.logPlaces + m.kCol).map fun x => 2 ^ x).sum = _
      rw [List.map_map]
      rfl
    rw [e]
    exact h
  have h64 : Wf.planesOf l < 64 := by omega
  have hd : l.d < 64 := by omega
  simp only [Lkp.Public.sizesOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨List.cons_ne_nil id [], fun e => c9 (List.map_eq_nil_iff.1 e)⟩, c1⟩, c2⟩,
    c3⟩, c4⟩, h64⟩, fun x hx => ?_⟩, hs⟩, hd⟩, c7⟩, Or.inr ⟨rfl, rfl⟩⟩, Nat.zero_le _⟩
  obtain ⟨p, hp, rfl⟩ := mem_parts id m l hx
  have h := partsFit_all m l l.parts 0 hf p hp
  exact ⟨h.1, h.2.1⟩

/-- **The clause on the blocks of tree numbers**: by the text of `Wf.lookupOf`. -/
theorem keysOK_lookupOf : (Wf.lookupOf id m l).keysOK = true := rfl

/-- **The clause on the pieces of the table**: by the text of `Wf.lookupOf`. -/
theorem tablesOK_lookupOf : (Wf.lookupOf id m l).tablesOK = true := by
  simp [Lkp.Public.tablesOK, Wf.lookupOf, Lkp.allPairs, Nat.two_pow_pos]

/-- **The clause on the order of the last key level.** -/
theorem orderOK_lookupOf (hl : Wf.lookupOk Wf.fBits l = true) (hf : Wf.fitsMatrix m l = true) :
    (Wf.lookupOf id m l).orderOK = true := by
  obtain ⟨-, -, -, -, -, -, c9, c13⟩ := lookupOk_facts hl
  simp only [Lkp.Public.orderOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun j hj => ?_, allPairs_of_distinct _ c13⟩
  have hall : ∀ x ∈ (Wf.lookupOf id m l).parts, j + 1 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_parts id m l hx
    exact (partsFit_all m l l.parts 0 hf p hp).2.2 j hj
  have hfb : (Wf.lookupOf id m l).firstBits ∈ (Wf.lookupOf id m l).parts := by
    obtain ⟨p, ps, e⟩ := List.exists_cons_of_ne_nil c9
    show (l.parts.map fun p => p.logPlaces + m.kCol).headD 0 ∈
      l.parts.map fun p => p.logPlaces + m.kCol
    rw [e, List.map_cons, List.headD_cons]
    exact List.mem_cons_self ..
  have h := lt_foldl_min (Wf.lookupOf id m l).parts (Wf.lookupOf id m l).firstBits (j + 1)
    (hall _ hfb) hall
  omega

end

end OnBytes.KeyPlan

#print axioms OnBytes.KeyPlan.sizesOK_lookupOf
#print axioms OnBytes.KeyPlan.keysOK_lookupOf
#print axioms OnBytes.KeyPlan.tablesOK_lookupOf
#print axioms OnBytes.KeyPlan.orderOK_lookupOf
