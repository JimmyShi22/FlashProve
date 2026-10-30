-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkLayout.lean: the blocks of planes that the program lays into the prover's message,
each by itself.

`Wf.layout` (OnBytes/Key/Ranges.lean) takes the aligned blocks into which `Lkp.liveBlocks` cuts the
real planes of each lookup, sorts them by falling size and gives each a row and a first place.
OnBytes/Slice/BlkPlanes.lean asks of a block by itself that its planes are an aligned block below
2 ^ mu, that it has the index bits of its planes and the d row variables, and that these are at most
the index bits of a place in a row (`BlockFits`). This file shows that of every block of the layout
that belongs to lookup number i, from the program's public tests: the lookup is in order
(`Wf.lookupOk`), and the layout's first block fits a row (a clause of `Wf.admitted`).

Main definitions: `keyOf` (what the laying leaves of a block: lookup, first plane, sizes).
Main theorems.
 `liveLoop_spec`     each block of real planes is aligned and lies below the number of real planes.
 `layLoop_keys`, `layout_keys`   the laying changes rows and places alone, and keeps the order.
 `layout_mem`        a block of the layout comes from a block of real planes of its lookup.
 `layout_bits_le`    no block has more index bits than the first.
 `layout_fits`       every block of lookup i in the layout meets `BlockFits`.

Not claimed. That the blocks hold each real plane once. That they lie apart in the table, begin at
multiples of their sizes, or lie in real rows. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkPlanes
import OnBytes.Slice.ProgCodes

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open OnBytes.Params (WfLookup)

/-! ## The blocks of real planes -/

/-- The block that the search for a size finds is aligned and fits, if the block that it starts from
does. -/
theorem growBits_spec' (x left : ℕ) : ∀ (k b : ℕ), x % 2 ^ b = 0 → 2 ^ b ≤ left →
    x % 2 ^ Lkp.growBits x left k b = 0 ∧ 2 ^ Lkp.growBits x left k b ≤ left
  | 0, _, h1, h2 => ⟨h1, h2⟩
  | k + 1, b, h1, h2 => by
    unfold Lkp.growBits
    split
    · next h =>
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact growBits_spec' x left k (b + 1) h.1 h.2
    · exact ⟨h1, h2⟩

/-- Each block of real planes is aligned and lies below the number of real planes. -/
theorem liveLoop_spec (live : ℕ) : ∀ (k first : ℕ), ∀ b ∈ Lkp.liveLoop live k first,
    b.1 % 2 ^ b.2 = 0 ∧ b.1 + 2 ^ b.2 ≤ live
  | 0, _, b, hb => by cases hb
  | k + 1, first, b, hb => by
    unfold Lkp.liveLoop at hb
    split at hb
    · cases hb
    · next hlt =>
      obtain ⟨g1, g2⟩ := growBits_spec' first (live - first) 6 0 (by rw [pow_zero, Nat.mod_one])
        (by rw [pow_zero]; omega)
      rcases List.mem_cons.1 hb with e | hb
      · rw [e]
        refine ⟨g1, ?_⟩
        show first + 2 ^ Lkp.growBits first (live - first) 6 0 ≤ live
        omega
      · exact liveLoop_spec live k _ b hb

/-! ## The laying -/

/-- What the laying leaves of a block: its lookup, its first plane and its two sizes. -/
def keyOf (b : Wf.Block) : ℕ × ℕ × ℕ × ℕ := (b.lookup, b.first, b.logPlanes, b.bits)

/-- The loop that lays blocks changes rows and places alone, and keeps the order. -/
theorem layLoop_keys (ell : ℕ) : ∀ (bs : List Wf.Block) (row place : ℕ) (done : List Wf.Block),
    (Wf.layLoop ell row place bs done).map keyOf = done.reverse.map keyOf ++ bs.map keyOf
  | [], _, _, done => by simp [Wf.layLoop]
  | b :: bs, row, place, done => by
    unfold Wf.layLoop
    split
    · rw [layLoop_keys ell bs, List.reverse_cons, List.map_append, List.append_assoc]
      rfl
    · rw [layLoop_keys ell bs, List.reverse_cons, List.map_append, List.append_assoc]
      rfl

/-- All lookups' blocks, before they are sorted and laid. -/
def allBlocks (lookups : List WfLookup) : List Wf.Block :=
  lookups.zipIdx.flatMap fun x =>
    (Lkp.liveBlocks (Wf.planesOf x.1)).map fun b => ⟨x.2, b.1, b.2, b.2 + x.1.d, 0, 0⟩

/-- The laying changes rows and places alone, and keeps the order of the sorted blocks. -/
theorem layout_keys (lookups : List WfLookup) (ell : ℕ) :
    (Wf.layout lookups ell).map keyOf =
      ((allBlocks lookups).mergeSort fun a b => decide (b.bits ≤ a.bits)).map keyOf := by
  unfold Wf.layout Wf.layFrom
  rw [layLoop_keys]
  rfl

/-- A member of a numbered list stands in the list at its number less the first number. -/
theorem getElem?_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (x : α × ℕ), x ∈ l.zipIdx k →
    k ≤ x.2 ∧ l[x.2 - k]? = some x.1
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with h | h
    · rw [h]
      simp
    · obtain ⟨h1, h2⟩ := getElem?_of_mem_zipIdx l (k + 1) x h
      refine ⟨by omega, ?_⟩
      rw [show x.2 - k = (x.2 - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact h2

/-- A block of the layout comes from a block of real planes of its lookup. -/
theorem layout_mem (lookups : List WfLookup) (ell : ℕ) (b : Wf.Block)
    (hb : b ∈ Wf.layout lookups ell) :
    ∃ l, lookups[b.lookup]? = some l ∧ (b.first, b.logPlanes) ∈ Lkp.liveBlocks (Wf.planesOf l) ∧
      b.bits = b.logPlanes + l.d := by
  have h1 : keyOf b ∈ (Wf.layout lookups ell).map keyOf := List.mem_map_of_mem hb
  rw [layout_keys] at h1
  obtain ⟨b0, h2, h3⟩ := List.mem_map.1 h1
  rw [List.mem_mergeSort] at h2
  obtain ⟨x, hx, h4⟩ := List.mem_flatMap.1 h2
  obtain ⟨y, hy, h5⟩ := List.mem_map.1 h4
  obtain ⟨_, h6⟩ := getElem?_of_mem_zipIdx lookups 0 x hx
  rw [Nat.sub_zero] at h6
  subst h5
  simp only [keyOf, Prod.mk.injEq] at h3
  obtain ⟨a1, a2, a3, a4⟩ := h3
  refine ⟨x.1, by rw [← a1]; exact h6, by rw [← a2, ← a3]; exact hy, by rw [← a4, ← a3]⟩

/-- No block of the layout has more index bits than the first. -/
theorem layout_bits_le (lookups : List WfLookup) (ell : ℕ) (b0 b : Wf.Block)
    (h0 : (Wf.layout lookups ell).head? = some b0) (hb : b ∈ Wf.layout lookups ell) :
    b.bits ≤ b0.bits := by
  have hs : ((allBlocks lookups).mergeSort fun a b => decide (b.bits ≤ a.bits)).Pairwise
      fun a b => decide (b.bits ≤ a.bits) = true :=
    List.pairwise_mergeSort (le := fun a b : Wf.Block => decide (b.bits ≤ a.bits))
      (fun a b c h1 h2 => by
        rw [decide_eq_true_eq] at h1 h2 ⊢
        omega)
      (fun a b => by
        rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        omega) _
  have hk := layout_keys lookups ell
  generalize (allBlocks lookups).mergeSort (fun a b => decide (b.bits ≤ a.bits)) = S at hs hk
  cases hL : Wf.layout lookups ell with
  | nil => rw [hL] at hb; cases hb
  | cons c cs =>
    rw [hL] at h0 hb hk
    obtain rfl : c = b0 := Option.some.inj h0
    cases S with
    | nil => cases hk
    | cons s ss =>
      rw [List.map_cons, List.map_cons] at hk
      obtain ⟨k1, k2⟩ := List.cons.inj hk
      rcases List.mem_cons.1 hb with e | hb
      · rw [e]
      · have h1 : keyOf b ∈ ss.map keyOf := by rw [← k2]; exact List.mem_map_of_mem hb
        obtain ⟨y, hy, h3⟩ := List.mem_map.1 h1
        have h4 := (List.pairwise_cons.1 hs).1 y hy
        rw [decide_eq_true_eq] at h4
        simp only [keyOf, Prod.mk.injEq] at h3 k1
        omega

/-- Every block of lookup i in the layout meets what is asked of a block by itself, if the
lookup is in order and the layout's first block fits a row of ell places. -/
theorem layout_fits (lookups : List WfLookup) (ell i : ℕ) (l : WfLookup)
    (hi : lookups[i]? = some l) (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout lookups ell).head?.any fun b => decide (2 ^ b.bits ≤ ell)) = true) :
    ∀ b ∈ (Wf.layout lookups ell).filter (·.lookup == i), BlockFits l.mu l.d (ceilLog2 ell) b := by
  intro b hb
  obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
  have hbi : b.lookup = i := by simpa using hb2
  obtain ⟨l', h1, h2, h3⟩ := layout_mem lookups ell b hb1
  rw [hbi, hi] at h1
  obtain rfl := Option.some.inj h1
  obtain ⟨g1, g2⟩ := liveLoop_spec (Wf.planesOf l) 64 0 _ h2
  have hpl : Wf.planesOf l ≤ 2 ^ l.mu := by
    simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    have h5 : l.live < 2 ^ l.mu := hl.1.1.1.1.1.1.1.1.1.1.1.2
    unfold Wf.planesOf
    split
    · exact le_refl _
    · omega
  have hin : b.first + 2 ^ b.logPlanes ≤ 2 ^ l.mu := le_trans g2 hpl
  obtain ⟨b0, hb0, hfit⟩ : ∃ b0, (Wf.layout lookups ell).head? = some b0 ∧ 2 ^ b0.bits ≤ ell := by
    cases hq : (Wf.layout lookups ell).head? with
    | none => rw [hq] at hh; cases hh
    | some b0 =>
      rw [hq] at hh
      exact ⟨b0, rfl, by simpa using hh⟩
  have hle := layout_bits_le lookups ell b0 b hb0 hb1
  refine ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (by omega), g1, hin, h3,
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 ?_⟩
  calc 2 ^ b.bits ≤ 2 ^ b0.bits := Nat.pow_le_pow_right (by decide) hle
    _ ≤ ell := hfit
    _ ≤ 2 ^ ceilLog2 ell := le_two_pow_ceilLog2 ell

end OnBytes.Slice.Planes
