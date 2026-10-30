--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesCut.lean: structured vectors that are cut below a length and laid on the
table of an oracle message: that they can be made, what shape they have, and that they read as 0
beyond the cut.

A row of the linear claim is made of structured vectors (tensors) on the entries of a vector that
lies in a message's main table. Each is cut below a length (tensorBelow), so that it reads nothing
behind the vector's end, and then carried to the table's own indices (VectorLay.onTable). The
message's last entries mask the answers to its out-of-domain sample; a row must not read them.

Main names:
  tensorBelow_makes   a vector without a written-out factor can be cut wherever it has the variables
                      and the length is within them
  laid_cut_zero       **the summands of a cut, laid on a table, add up to 0 at the index of an entry
                      beyond the cut**
  Sits T G o lay n    facts: the message o is a member of the group G, has a main table of the
                      layout's size, of at most 63 index bits, and each place of its pad in that
                      table lies inside the table and holds an entry numbered at least n
  laid_term_fits      under Sits a laid vector is in order and fits its place
  entry_fits          under Sits a single entry at an index of the table fits its place
  mem_addLaid, units_addLaid, runs_addLaid, forms_addLaid
                      what the laying of vectors leaves of a row (its kind: the library's laid_kind)
  terms_units, mem_units, runs_units, forms_units, kind_units
                      what a loop that adds single entries leaves of a row

What is not claimed. That Sits holds at any statement. Nothing on what a row means, on soundness, on
completeness or on hiding.

-/
import Johnson.Desc.Means.Forth.YesRow
import Johnson.Desc.K14.Law.Carry
import Johnson.Desc.Own.RoomPlaces
import OnBytes.Slice.BlkCross

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open Desc.K14.Law (onTable_entry tensorBelow_val tensorBelow_mem sum_map_zero)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## A cut can be made -/

/-- A vector without a written-out factor can be cut wherever it has the variables and the length is
within them. -/
theorem tensorBelow_makes (v : Tensor) (hd : v.denseVars = []) (start count len : Nat)
    (hv : start + count ≤ v.vars) (hl : len ≤ 2 ^ count) :
    ∃ L, tensorBelow v start count len = some L := by
  unfold tensorBelow
  simp only [hd]
  split
  · rename_i h1
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h | h
    · exact absurd h (Nat.not_lt.2 hv)
    · exact absurd h (Nat.not_lt.2 hl)
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · simp only [List.filter_nil, List.length_nil, beq_self_eq_true, if_true]
          exact ⟨_, rfl⟩

/-! ## Beyond the cut -/

/-- **The summands of a cut, laid on a table, add up to 0 at the index of an entry beyond the
cut.** k: the entry's number. -/
theorem laid_cut_zero (lay : VectorLay) (v : Tensor) (hd : v.denseVars = [])
    (start count len : Nat) (L : List Tensor) (hL : tensorBelow v start count len = some L)
    (hn : v.vars ≤ lay.bits) (k : Nat) (hk : k < 2 ^ lay.bits)
    (hz : k < 2 ^ v.vars → len ≤ k / 2 ^ start % 2 ^ count) :
    (L.map fun t => ρ.val ((lay.onTable t).entry (lay.index k))).sum = 0 := by
  have each : ∀ t ∈ L, ρ.val ((lay.onTable t).entry (lay.index k)) =
      if k < 2 ^ v.vars then ρ.val (t.entry k) else 0 := by
    intro t ht
    obtain ⟨h1, h2⟩ := tensorBelow_mem v hd start count len L hL t ht
    have h0 := onTable_entry ρ lay t h1 (by rw [h2]; exact hn) k hk
    rwa [h2] at h0
  rw [List.map_congr_left each]
  by_cases hk2 : k < 2 ^ v.vars
  · simp only [if_pos hk2]
    rw [tensorBelow_val ρ v hd start count len L hL k, if_neg (Nat.not_lt.2 (hz hk2))]
  · simp only [if_neg hk2]
    exact sum_map_zero L _ fun _ _ => rfl

/-! ## A message that sits in a group -/

/-- Facts on a message with a vector in its main table. n: the entries from number n on may
mask answers. -/
structure Sits (T : Statement) (G : Group) (o : Nat) (lay : VectorLay) (n : Nat) : Prop where
  member : G.members.contains o = true
  table : T.has o .main = true
  bits : T.tableBits o .main = lay.bits
  small : lay.bits ≤ 63
  pad : ∀ x, T.oracles[o]? = some x → ∀ q ∈ x.pad, q.1 = Part.main →
    q.2 < 2 ^ lay.bits ∧ n ≤ lay.entryAt q.2

/-- "The table is there", in the own text of the IOP as written in Lean. -/
theorem tableThere_of_has (T : Statement) (o : Nat) (part : Part) (h : T.has o part = true) :
    VerifiableInference.Desc.Own.tableThere T o part = true := by
  unfold Statement.has at h
  unfold VerifiableInference.Desc.Own.tableThere
  cases hx : T.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; exact h

/-- Under Sits a laid vector is in order and fits its place. -/
theorem laid_term_fits {T : Statement} {G : Group} {o : Nat} {lay : VectorLay} {n : Nat}
    (h : Sits T G o lay n) (v : Tensor) (hd : v.denseVars = []) (hv : v.vars ≤ lay.bits) :
    VerifiableInference.Desc.Own.tensorInOrder (lay.onTable v) = true ∧
      VerifiableInference.Desc.Own.placeFits T G o .main (lay.onTable v).vars 0 = true := by
  obtain ⟨h1, h2⟩ := Slice.onTable_vars lay v hd hv
  have h3 : (lay.onTable v).pairs.length = lay.bits := h1
  constructor
  · unfold VerifiableInference.Desc.Own.tensorInOrder
    rw [h2, h3]
    simp [h.small]
  · unfold VerifiableInference.Desc.Own.placeFits
    rw [h.member, tableThere_of_has T o .main h.table, h1, h.bits]
    simp

/-- Under Sits a single entry of the table fits its place. -/
theorem entry_fits {T : Statement} {G : Group} {o : Nat} {lay : VectorLay} {n : Nat}
    (h : Sits T G o lay n) (i : Nat) (hi : i < 2 ^ lay.bits) :
    VerifiableInference.Desc.Own.placeFits T G o .main (T.tableBits o .main) i = true := by
  unfold VerifiableInference.Desc.Own.placeFits
  rw [h.member, tableThere_of_has T o .main h.table, h.bits]
  simp [hi]

/-! ## What the laying of vectors leaves of a row -/

/-- One step of the laying. -/
theorem addLaid_cons (r : Row) (o : Nat) (lay : VectorLay) (t : Tensor) (L : List Tensor) :
    addLaid r o lay (t :: L) = addLaid (r.add o .main (lay.onTable t)) o lay L := rfl

/-- A structured summand behind the laying was there before, or is one of the laid vectors. -/
theorem mem_addLaid (o : Nat) (lay : VectorLay) : ∀ (L : List Tensor) (r : Row) (x : Term),
    x ∈ (addLaid r o lay L).terms →
      x ∈ r.terms ∨ ∃ t ∈ L, x = ⟨o, .main, lay.onTable t⟩
  | [], _, _, h => Or.inl h
  | t :: L, r, x, h => by
    rw [addLaid_cons] at h
    rcases mem_addLaid o lay L _ x h with h1 | ⟨s, hs, e⟩
    · have h2 : x ∈ r.terms.push ⟨o, .main, lay.onTable t⟩ := h1
      rcases Array.mem_push.1 h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨t, List.mem_cons_self, h3⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, e⟩

/-- The laying leaves the single entries. -/
theorem units_addLaid (o : Nat) (lay : VectorLay) : ∀ (L : List Tensor) (r : Row),
    (addLaid r o lay L).units = r.units
  | [], _ => rfl
  | t :: L, r => by rw [addLaid_cons, units_addLaid o lay L]; rfl

/-- The laying leaves the runs. -/
theorem runs_addLaid (o : Nat) (lay : VectorLay) : ∀ (L : List Tensor) (r : Row),
    (addLaid r o lay L).runs = r.runs
  | [], _ => rfl
  | t :: L, r => by rw [addLaid_cons, runs_addLaid o lay L]; rfl

/-- The laying leaves the whole forms. -/
theorem forms_addLaid (o : Nat) (lay : VectorLay) : ∀ (L : List Tensor) (r : Row),
    (addLaid r o lay L).forms = r.forms
  | [], _ => rfl
  | t :: L, r => by rw [addLaid_cons, forms_addLaid o lay L]; rfl

/-! ## What a loop that adds single entries leaves of a row -/

section units
variable {α : Type} (o : Nat) (idx : α → Nat) (c : α → E)

/-- The loop leaves the structured summands. -/
theorem terms_units : ∀ (P : List α) (r : Row),
    (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).terms = r.terms
  | [], _ => rfl
  | x :: P, r => by rw [List.foldl_cons, terms_units P]; rfl

/-- A single entry behind the loop was there before, or is one of those added. -/
theorem mem_units : ∀ (P : List α) (r : Row) (u : Single),
    u ∈ (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).units →
      u ∈ r.units ∨ ∃ x ∈ P, u = ⟨o, .main, idx x, c x⟩
  | [], _, _, h => Or.inl h
  | x :: P, r, u, h => by
    rw [List.foldl_cons] at h
    rcases mem_units P _ u h with h1 | ⟨y, hy, e⟩
    · have h2 : u ∈ r.units.push ⟨o, .main, idx x, c x⟩ := h1
      rcases Array.mem_push.1 h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨x, List.mem_cons_self, h3⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, e⟩

/-- The loop leaves the runs. -/
theorem runs_units : ∀ (P : List α) (r : Row),
    (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).runs = r.runs
  | [], _ => rfl
  | x :: P, r => by rw [List.foldl_cons, runs_units P]; rfl

/-- The loop leaves the whole forms. -/
theorem forms_units : ∀ (P : List α) (r : Row),
    (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).forms = r.forms
  | [], _ => rfl
  | x :: P, r => by rw [List.foldl_cons, forms_units P]; rfl

/-- The loop leaves the row's kind. -/
theorem kind_units : ∀ (P : List α) (r : Row),
    (P.foldl (fun r x => r.addUnit o .main (idx x) (c x)) r).kind = r.kind
  | [], _ => rfl
  | x :: P, r => by rw [List.foldl_cons, kind_units P]; rfl

end units

end Desc.K14.Honest

#print axioms Desc.K14.Honest.tensorBelow_makes
#print axioms Desc.K14.Honest.laid_cut_zero
#print axioms Desc.K14.Honest.tableThere_of_has
#print axioms Desc.K14.Honest.laid_term_fits
#print axioms Desc.K14.Honest.entry_fits
#print axioms Desc.K14.Honest.addLaid_cons
#print axioms Desc.K14.Honest.mem_addLaid
#print axioms Desc.K14.Honest.units_addLaid
#print axioms Desc.K14.Honest.runs_addLaid
#print axioms Desc.K14.Honest.forms_addLaid
#print axioms Desc.K14.Honest.terms_units
#print axioms Desc.K14.Honest.mem_units
#print axioms Desc.K14.Honest.runs_units
#print axioms Desc.K14.Honest.forms_units
#print axioms Desc.K14.Honest.kind_units
