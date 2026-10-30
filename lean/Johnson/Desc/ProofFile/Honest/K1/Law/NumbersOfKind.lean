-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/NumbersOfKind.lean: THE SHARED "SENDING" (the kind K1): AT
WHICH NUMBERS THE WRITTEN LIST OF THE FIRST CHAIN's 358 PLACES (P5J.At.ps) HAS A PLACE OF THE KIND
K1: 2 · K1.noL l d (l < 25; both d) · 356: THESE 52 AND NO OTHER. PUBLIC: closed numbers. Eight
theorems; no definition.

  - k1_numbers_full: BY LEAN's KERNEL: the numbers below 358 at which P5J.At.ps has a place of the
    kind K1 are, in their order, 2, then K1.noL l false and K1.noL l true for l = 0 to 24, then 356.
  - k1_numbers_52: that list has 52 members.
  - k1_numbers_no_k2, k1_numbers_no_short: TWO CONTROLS: the same test at the kind K2, and at the
    list without 356, says no.
  - k1_numbers_mem: what it is to be in that list.
  - k1_number_of_kind: a place of the kind K1 on the written list stands at one of the 52.
  - k1_kind_of_number: at each of the 52 the written list has a place of the kind K1.
  - k1_kind_iff: the two in one.

For whom. L25's gather by kind ("∀ b p, P5J.At.ps[b]? = some p → p.kind ≠ KindName.frame → …"): K1's
shares are stated at the numbers (SharesAtMembers.lean; 356: not there): this is the bridge from the
kind to the numbers.

KIN, TOLD; NONE IS RESTATED. The like at the kind K3, whose form is followed here:
k03_border_of_kind (Johnson/P5J/K03AsksAt.lean). BY ADDRESS, not by number: of the written list's
places those of the kind K1 are just 52 named addresses: k1_places_written
(Johnson/Desc/K1/Law/SitsFirstChain.lean). WHICH PLACE stands at a number (more than its kind):
place_fifty (Johnson/Desc/K1/Law/CallsE.lean); ps_two (Honest/K1/Law/RecordAtHead.lean); m4_place
(Honest/K13/ExchangeM4At.lean). K1.noL l d = 14 * l + IM.k1Ix l d + 2 by its text; IM.k1Ix l d <
IM.nAt l: k1Ix_lt (OwedAtMembers.lean). The list's length: ps_358 (Johnson/P5J/K09Len.lean): called.

Limits. THE FULL SIZE's WRITTEN LIST ALONE. It says where the kind stands: nothing on what is sent
there. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.K09Len
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (KindName Place)

set_option maxRecDepth 1000000 in
/-- **THE 52 NUMBERS, AND NO OTHER**: by the kernel. -/
theorem k1_numbers_full :
    ((List.range 358).filter fun b => (P5J.At.ps[b]?).any fun p => p.kind == KindName.K1) =
      2 :: ((List.range 25).flatMap fun l => [K1.noL l false, K1.noL l true]) ++ [356] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k1_numbers_52 :
    (2 :: ((List.range 25).flatMap fun l => [K1.noL l false, K1.noL l true]) ++
      [356]).length = 52 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the kind K2 the test says no. -/
theorem k1_numbers_no_k2 :
    decide (((List.range 358).filter fun b =>
        (P5J.At.ps[b]?).any fun p => p.kind == KindName.K2) =
      2 :: ((List.range 25).flatMap fun l => [K1.noL l false, K1.noL l true]) ++
        [356]) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the list without 356 the test says no. -/
theorem k1_numbers_no_short :
    decide (((List.range 358).filter fun b =>
        (P5J.At.ps[b]?).any fun p => p.kind == KindName.K1) =
      2 :: ((List.range 25).flatMap fun l => [K1.noL l false, K1.noL l true])) = false := by
  decide +kernel

/-- What it is to be in the list. -/
theorem k1_numbers_mem (b : ℕ) :
    b ∈ (2 :: ((List.range 25).flatMap fun l => [K1.noL l false, K1.noL l true]) ++ [356]) ↔
      (b = 2 ∨ (∃ l, l < 25 ∧ ∃ d, b = K1.noL l d) ∨ b = 356) := by
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false]
  constructor
  · rintro (h | ⟨l, hl, h | h⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨l, hl, false, h⟩)
    · exact Or.inr (Or.inl ⟨l, hl, true, h⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨l, hl, d, h⟩ | h)
    · exact Or.inl h
    · cases d
      · exact Or.inr (Or.inl ⟨l, hl, Or.inl h⟩)
      · exact Or.inr (Or.inl ⟨l, hl, Or.inr h⟩)
    · exact Or.inr (Or.inr h)

/-- **A PLACE OF THE KIND K1 STANDS AT ONE OF THE 52.** -/
theorem k1_number_of_kind {b : ℕ} {p : Place} (hb : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) :
    b = 2 ∨ (∃ l, l < 25 ∧ ∃ d, b = K1.noL l d) ∨ b = 356 := by
  have hi : b < 358 := by
    have h0 := (List.getElem?_eq_some_iff.1 hb).1
    rw [P5J.ps_358] at h0
    exact h0
  have hm : b ∈ (List.range 358).filter fun b =>
      (P5J.At.ps[b]?).any fun p => p.kind == KindName.K1 := by
    refine List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩
    rw [hb]
    show (p.kind == KindName.K1) = true
    rw [hk]
    rfl
  rw [k1_numbers_full] at hm
  exact (k1_numbers_mem b).1 hm

/-- **AT EACH OF THE 52 STANDS A PLACE OF THE KIND K1.** -/
theorem k1_kind_of_number {b : ℕ}
    (h : b = 2 ∨ (∃ l, l < 25 ∧ ∃ d, b = K1.noL l d) ∨ b = 356) :
    ∃ p, P5J.At.ps[b]? = some p ∧ p.kind = KindName.K1 := by
  have hm := (k1_numbers_mem b).2 h
  rw [← k1_numbers_full] at hm
  have hp : ((P5J.At.ps[b]?).any fun p => p.kind == KindName.K1) = true :=
    (List.mem_filter.1 hm).2
  cases hq : P5J.At.ps[b]? with
  | none =>
    rw [hq] at hp
    simp at hp
  | some p =>
    rw [hq] at hp
    exact ⟨p, rfl, beq_iff_eq.1 hp⟩

/-- The two in one. -/
theorem k1_kind_iff (b : ℕ) :
    (∃ p, P5J.At.ps[b]? = some p ∧ p.kind = KindName.K1) ↔
      (b = 2 ∨ (∃ l, l < 25 ∧ ∃ d, b = K1.noL l d) ∨ b = 356) :=
  ⟨fun ⟨_, hb, hk⟩ => k1_number_of_kind hb hk, k1_kind_of_number⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_numbers_full
#print axioms ProofFile.Honest.K1.k1_numbers_52
#print axioms ProofFile.Honest.K1.k1_numbers_no_k2
#print axioms ProofFile.Honest.K1.k1_numbers_no_short
#print axioms ProofFile.Honest.K1.k1_numbers_mem
#print axioms ProofFile.Honest.K1.k1_number_of_kind
#print axioms ProofFile.Honest.K1.k1_kind_of_number
#print axioms ProofFile.Honest.K1.k1_kind_iff
