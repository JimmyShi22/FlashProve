-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05NoHole.lean: A MATRIX THAT IS LAID LAWFULLY HAS A BLOCK FOR EVERY ELEMENT
INSIDE ITS SIZES: the programs' test laidMatrixOk (OnBytes/Iop/ReqRows.lean) counts the blocks'
elements; its docstring: "the blocks are disjoint and inside, so the right number is full cover".
Here that sentence is proved. With Johnson/Desc/First/Att/K05CellAt.lean (no two blocks hold one
element): the blocks tile the matrix.

Main names:
  `blockCells b`, `blocksCells l`: the elements that a block, a list of blocks, holds, as finite
    sets.
    `mem_blockCells`, `card_blockCells`, `mem_blocksCells`, `card_blocksCells` (no two meet: counted
    block by block).
  `laid_no_hole`: **laidMatrixOk a R P = true, i < a.sizeI, c < a.sizeC: laidPlace a.blocks i c
    answers.**
  `laidPlace_block`: its answer is laidIn b i c at a block b of the list that holds the element.
  `laidIn_row_in`: the row at which a block lays an element that it holds lies in the block's own
    rows.
  `laidIn_place_lt`: the place lies below 2 ^ P.
General in the sort of link, though the file stands among the files of kind K5.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05CellAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First.Look (laidHolds laidPlace)

/-- The elements that a block holds. -/
def blockCells (b : LaidBlock) : Finset (ℕ × ℕ) :=
  Finset.Ico b.firstI (b.firstI + 2 ^ b.bitsI) ×ˢ Finset.Ico b.firstC (b.firstC + 2 ^ b.bitsC)

theorem mem_blockCells (b : LaidBlock) (i c : ℕ) : (i, c) ∈ blockCells b ↔ laidHolds b i c = true := by
  unfold blockCells laidHolds
  simp only [Finset.mem_product, Finset.mem_Ico, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩
    exact ⟨⟨⟨a, b⟩, c⟩, d⟩
  · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
    exact ⟨⟨a, b⟩, c, d⟩

theorem card_blockCells (b : LaidBlock) : (blockCells b).card = 2 ^ (b.bitsI + b.bitsC) := by
  unfold blockCells
  rw [Finset.card_product, Nat.card_Ico, Nat.card_Ico, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left, pow_add]

/-- The elements that the blocks of a list hold. -/
def blocksCells : List LaidBlock → Finset (ℕ × ℕ)
  | [] => ∅
  | b :: l => blockCells b ∪ blocksCells l

theorem mem_blocksCells {i c : ℕ} : ∀ {l : List LaidBlock}, (i, c) ∈ blocksCells l →
    ∃ b ∈ l, laidHolds b i c = true
  | [], h => by simp [blocksCells] at h
  | b :: l, h => by
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨b, List.mem_cons_self, (mem_blockCells b i c).1 h⟩
    · obtain ⟨y, hy, e⟩ := mem_blocksCells h
      exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

/-- No two blocks meet: so the elements are counted block by block. -/
theorem card_blocksCells : ∀ l : List LaidBlock,
    noPair (fun (x y : LaidBlock) =>
      laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC)
      l = true →
    (blocksCells l).card = (l.map fun b => 2 ^ (b.bitsI + b.bitsC)).sum
  | [], _ => rfl
  | b :: l, hn => by
    unfold noPair at hn
    obtain ⟨hn1, hn2⟩ := Eq.mp (Bool.and_eq_true _ _) hn
    have hd : Disjoint (blockCells b) (blocksCells l) := by
      rw [Finset.disjoint_left]
      rintro ⟨i, c⟩ h1 h2
      obtain ⟨y, hy, e⟩ := mem_blocksCells h2
      have := List.all_eq_true.1 hn1 y hy
      rw [meet_of_holds b y i c ((mem_blockCells b i c).1 h1) e] at this
      cases this
    show (blockCells b ∪ blocksCells l).card = _
    rw [Finset.card_union_of_disjoint hd, card_blockCells, card_blocksCells l hn2, List.map_cons,
      List.sum_cons]

/-- **NO HOLE: a matrix that is laid lawfully has a block for every element inside its sizes.** -/
theorem laid_no_hole (a : ReqArray) (R P : ℕ) (h : laidMatrixOk a R P = true) {i c : ℕ}
    (hi : i < a.sizeI) (hc : c < a.sizeC) : ∃ rp, laidPlace a.blocks i c = some rp := by
  unfold laidMatrixOk at h
  obtain ⟨h12, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h12
  have hsub : blocksCells a.blocks ⊆ Finset.range a.sizeI ×ˢ Finset.range a.sizeC := by
    rintro ⟨i', c'⟩ hm
    obtain ⟨b, hb, e⟩ := mem_blocksCells hm
    have hb1 := List.all_eq_true.1 h1 b hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb1
    unfold laidHolds at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hcard : (Finset.range a.sizeI ×ˢ Finset.range a.sizeC).card ≤ (blocksCells a.blocks).card := by
    rw [card_blocksCells a.blocks h2, Finset.card_product, Finset.card_range, Finset.card_range]
    have h3' : (a.blocks.map fun b => 2 ^ (b.bitsI + b.bitsC)).foldl (· + ·) 0 =
        a.sizeI * a.sizeC := by simpa using h3
    rw [← h3', List.sum_eq_foldl]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hm : (i, c) ∈ blocksCells a.blocks := by
    rw [heq]
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hi, hc⟩
  obtain ⟨b, hb, e⟩ := mem_blocksCells hm
  unfold laidPlace
  cases hf : a.blocks.find? fun b => laidHolds b i c with
  | some y => exact ⟨_, rfl⟩
  | none =>
    have := List.find?_eq_none.1 hf b hb
    rw [e] at this
    exact absurd rfl this

/-- laidPlace's answer is what a block of the list that holds the element gives. -/
theorem laidPlace_block {l : List LaidBlock} {i c : ℕ} {rp : ℕ × ℕ} (h : laidPlace l i c = some rp) :
    ∃ b ∈ l, laidHolds b i c = true ∧ rp = VerifiableInference.Desc.First.Look.laidIn b i c := by
  unfold laidPlace at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have hh := List.find?_some hb
  exact ⟨b, List.mem_of_find?_eq_some hb, hh, rfl⟩

/-- The row lies in the block's own rows. -/
theorem laidIn_row_in (b : LaidBlock) (R P : ℕ) (F : VerifiableInference.Desc.K9L.BlockFacts b R P)
    (i c : ℕ) (h : laidHolds b i c = true) :
    (VerifiableInference.Desc.First.Look.laidIn b i c).1 < b.firstRow + 2 ^ b.rowBits := by
  obtain ⟨hx, _, _⟩ := numIn_lt b i c h
  have exb : 2 ^ b.bitsI * 2 ^ b.bitsC = 2 ^ b.placeBits * 2 ^ b.rowBits := by
    rw [← pow_add, ← pow_add, ← F.hs, Nat.add_comm]
  have hu : numIn b i c / 2 ^ b.placeBits < 2 ^ b.rowBits := by
    apply Nat.div_lt_of_lt_mul
    rw [← exb]
    exact hx
  show b.firstRow + numIn b i c / 2 ^ b.placeBits < _
  omega

/-- The place lies below 2 ^ P. -/
theorem laidIn_place_lt (b : LaidBlock) (R P : ℕ) (F : VerifiableInference.Desc.K9L.BlockFacts b R P)
    (i c : ℕ) : (VerifiableInference.Desc.First.Look.laidIn b i c).2 < 2 ^ P := by
  have eP : 2 ^ P = 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := by
    rw [← pow_add, Nat.add_sub_cancel' F.hP]
  have hv : numIn b i c % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have efp : b.firstPlace = 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) := by
    have := Nat.mod_add_div b.firstPlace (2 ^ b.placeBits)
    rw [F.alPlace, Nat.zero_add] at this
    exact this.symm
  have hfp : b.firstPlace / 2 ^ b.placeBits < 2 ^ (P - b.placeBits) := by
    apply Nat.div_lt_of_lt_mul
    rw [← eP]
    exact F.placeLt
  show b.firstPlace + numIn b i c % 2 ^ b.placeBits < 2 ^ P
  rw [efp, eP]
  calc 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) + numIn b i c % 2 ^ b.placeBits
      < 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) + 2 ^ b.placeBits := by omega
    _ = 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits + 1) := by ring
    _ ≤ 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := Nat.mul_le_mul_left _ hfp

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.card_blocksCells
#print axioms VerifiableInference.Desc.First.Att.P.laid_no_hole
#print axioms VerifiableInference.Desc.First.Att.P.laidPlace_block
#print axioms VerifiableInference.Desc.First.Att.P.laidIn_row_in
#print axioms VerifiableInference.Desc.First.Att.P.laidIn_place_lt
