-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerLaid.lean: «EVERY ADDRESS THAT THE LOOKUP READS RESOLVES» (Resolves,
K3CallerBase.lean) FROM TESTS THAT A PROGRAM CAN RUN IN A MOMENT: no walk over the cells.
Definitions with code, statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. A digits' lookup of the full size reads about 2^27 cells. Resolves speaks of each. An array is
laid in a few dozen blocks, each a rectangle with sides that are powers of two. If the blocks lie
inside the array, no two share an element, and their sizes add up to the array's, then every element
lies in a block: by counting. That is the argument of the programs' own test laidMatrixOk
(OnBytes/Iop/ReqRows.lean: «the blocks are disjoint and inside, so the right number is full cover»),
here as a theorem.

Main names.
  rect, cover, card_cover, cover_all: the counting.
  blocksB bs R K rows ell: the test on an array's blocks: each inside the R × K array; as large in
    the table as in the array; inside the first «rows» rows and «ell» places of the table; no two
    share an element (the programs' own noPair and laidMeet, by name); the sizes add up to R · K.
  laidPlace_some: under blocksB every element (i, c) with i < R, c < K has a place, and the place
    lies in the table.
  arrB S D l i t: the test on array number t of link i's list: it is in the written list S; arrayOf
    names it as the link's own; the layout has it; its message is in the signature's list l; blocksB
    at S's rows and columns and the message's main rows and their length.
  cell_resolves: under arrB every cell of the array that has an entry has a seat that fits.
  maskB, mask_resolves: the like for the mask entries below a bound.
Limits. blocksB is OUR test, after the programs' laidMatrixOk, laidBlockOk and reqMessageLayoutOk;
no theorem says that a yes of reqLayoutOk gives it. Nothing is evaluated in this file.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerBase
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

/-! ## 1 The counting -/

/-- The elements of a block. -/
def rect (b : Params.LaidBlock) : Finset (ℕ × ℕ) :=
  Finset.Ico b.firstI (b.firstI + 2 ^ b.bitsI) ×ˢ Finset.Ico b.firstC (b.firstC + 2 ^ b.bitsC)

theorem holds_iff {b : Params.LaidBlock} {i c : ℕ} : laidHolds b i c = true ↔
    (b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI) ∧ b.firstC ≤ c ∧ c < b.firstC + 2 ^ b.bitsC := by
  simp only [laidHolds, Bool.and_eq_true, decide_eq_true_eq]
  exact and_assoc

theorem mem_rect {b : Params.LaidBlock} {i c : ℕ} : (i, c) ∈ rect b ↔ laidHolds b i c = true := by
  rw [holds_iff, rect, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]

theorem card_rect (b : Params.LaidBlock) : (rect b).card = 2 ^ b.bitsI * 2 ^ b.bitsC := by
  rw [rect, Finset.card_product, Nat.card_Ico, Nat.card_Ico, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]

/-- The elements of a list of blocks. -/
def cover : List Params.LaidBlock → Finset (ℕ × ℕ)
  | [] => ∅
  | b :: l => rect b ∪ cover l

theorem mem_cover {p : ℕ × ℕ} : ∀ {l : List Params.LaidBlock}, p ∈ cover l ↔ ∃ b ∈ l, p ∈ rect b
  | [] => by simp [cover]
  | b :: l => by
    rw [cover, Finset.mem_union, mem_cover (l := l)]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem card_cover : ∀ l : List Params.LaidBlock,
    l.Pairwise (fun x y => Disjoint (rect x) (rect y)) →
      (cover l).card = (l.map fun b => 2 ^ b.bitsI * 2 ^ b.bitsC).sum
  | [], _ => rfl
  | b :: l, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    have hd : Disjoint (rect b) (cover l) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨y, hy, hpy⟩ := mem_cover.1 hq
      exact Finset.disjoint_left.1 (h1 y hy) hp hpy
    rw [cover, Finset.card_union_of_disjoint hd, card_rect, card_cover l h2, List.map_cons,
      List.sum_cons]

/-- **Blocks inside an R × K array, no two sharing an element, whose sizes add up to R · K, hold
every element.** -/
theorem cover_all (l : List Params.LaidBlock) (R K : ℕ)
    (hin : ∀ b ∈ l, b.firstI + 2 ^ b.bitsI ≤ R ∧ b.firstC + 2 ^ b.bitsC ≤ K)
    (hp : l.Pairwise fun x y => Disjoint (rect x) (rect y))
    (hs : (l.map fun b => 2 ^ b.bitsI * 2 ^ b.bitsC).sum = R * K) {i c : ℕ} (hi : i < R)
    (hc : c < K) : ∃ b ∈ l, laidHolds b i c = true := by
  have hsub : cover l ⊆ Finset.range R ×ˢ Finset.range K := by
    rintro ⟨i', c'⟩ hp'
    obtain ⟨b, hb, hpb⟩ := mem_cover.1 hp'
    obtain ⟨h1, h2⟩ := hin b hb
    obtain ⟨⟨_, h3⟩, _, h4⟩ := holds_iff.1 (mem_rect.1 hpb)
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_of_lt_of_le h3 h1, Nat.lt_of_lt_of_le h4 h2⟩
  have hcard : (Finset.range R ×ˢ Finset.range K).card ≤ (cover l).card := by
    rw [card_cover l hp, hs, Finset.card_product, Finset.card_range, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hm : (i, c) ∈ cover l := by
    rw [heq, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨hi, hc⟩
  obtain ⟨b, hb, hpb⟩ := mem_cover.1 hm
  exact ⟨b, hb, mem_rect.1 hpb⟩

/-! ## 2 The test on an array's blocks -/

/-- Two blocks share an element: the programs' own test, by name. -/
def meetB (x y : Params.LaidBlock) : Bool :=
  laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC

/-- One block: inside the array; as large in the table as in the array; inside the table. -/
def blockB (R K rows ell : Nat) (b : Params.LaidBlock) : Bool :=
  decide (b.firstI + 2 ^ b.bitsI ≤ R) && decide (b.firstC + 2 ^ b.bitsC ≤ K) &&
    decide (b.rowBits + b.placeBits = b.bitsI + b.bitsC) &&
    decide (b.firstRow + 2 ^ b.rowBits ≤ rows) && decide (b.firstPlace + 2 ^ b.placeBits ≤ ell)

/-- **The test on an array's blocks.** -/
def blocksB (bs : List Params.LaidBlock) (R K rows ell : Nat) : Bool :=
  bs.all (blockB R K rows ell) && noPair meetB bs &&
    decide ((bs.map fun b => 2 ^ b.bitsI * 2 ^ b.bitsC).sum = R * K)

theorem pairwise_of_noPair {α : Type} (r : α → α → Bool) : ∀ l : List α, noPair r l = true →
    l.Pairwise fun a b => r a b = false
  | [], _ => .nil
  | a :: l, h => by
    simp only [noPair, Bool.and_eq_true, List.all_eq_true] at h
    exact List.pairwise_cons.2 ⟨fun b hb => by simpa using h.1 b hb, pairwise_of_noPair r l h.2⟩

theorem disjoint_of_meetB {x y : Params.LaidBlock} (h : meetB x y = false) :
    Disjoint (rect x) (rect y) := by
  rw [Finset.disjoint_left]
  rintro ⟨i, c⟩ h1 h2
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := holds_iff.1 (mem_rect.1 h1)
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := holds_iff.1 (mem_rect.1 h2)
  have e : meetB x y = true := by
    simp only [meetB, laidMeet, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨Nat.lt_of_le_of_lt a1 b2, Nat.lt_of_le_of_lt b1 a2⟩,
      Nat.lt_of_le_of_lt a3 b4, Nat.lt_of_le_of_lt b3 a4⟩
  rw [e] at h
  cases h

theorem lt_mul_of {a b A B : ℕ} (ha : a < A) (hb : b < B) : b * A + a < B * A :=
  calc b * A + a < b * A + A := Nat.add_lt_add_left ha _
    _ = (b + 1) * A := (Nat.succ_mul b A).symm
    _ ≤ B * A := Nat.mul_le_mul_right A hb

/-- A block lays its elements inside its rectangle of the table. -/
theorem laidIn_lt {b : Params.LaidBlock} {i c rows ell : ℕ} (hh : laidHolds b i c = true)
    (e : b.rowBits + b.placeBits = b.bitsI + b.bitsC) (h1 : b.firstRow + 2 ^ b.rowBits ≤ rows)
    (h2 : b.firstPlace + 2 ^ b.placeBits ≤ ell) :
    (laidIn b i c).1 < rows ∧ (laidIn b i c).2 < ell := by
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := holds_iff.1 hh
  have hi : i - b.firstI < 2 ^ b.bitsI := by omega
  have hc : c - b.firstC < 2 ^ b.bitsC := by omega
  have key : ∀ x : ℕ, x < 2 ^ b.placeBits * 2 ^ b.rowBits →
      b.firstRow + x / 2 ^ b.placeBits < rows ∧ b.firstPlace + x % 2 ^ b.placeBits < ell := by
    intro x hx
    have d1 : x / 2 ^ b.placeBits < 2 ^ b.rowBits := Nat.div_lt_of_lt_mul hx
    have d2 : x % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ (by positivity)
    omega
  have sz : 2 ^ b.placeBits * 2 ^ b.rowBits = 2 ^ b.bitsC * 2 ^ b.bitsI := by
    rw [← pow_add, ← pow_add, Nat.add_comm b.placeBits, e, Nat.add_comm]
  unfold laidIn
  split
  · exact key _ (by rw [sz]; exact lt_mul_of hi hc)
  · exact key _ (by rw [sz, Nat.mul_comm (2 ^ b.bitsC) (2 ^ b.bitsI)]; exact lt_mul_of hc hi)

/-- **Under the test every element of the array has a place, and the place lies in the table.** -/
theorem laidPlace_some {bs : List Params.LaidBlock} {R K rows ell : ℕ}
    (h : blocksB bs R K rows ell = true) {i c : ℕ} (hi : i < R) (hc : c < K) :
    ∃ rp, laidPlace bs i c = some rp ∧ rp.1 < rows ∧ rp.2 < ell := by
  simp only [blocksB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hb : ∀ b ∈ bs, (b.firstI + 2 ^ b.bitsI ≤ R ∧ b.firstC + 2 ^ b.bitsC ≤ K) ∧
      b.rowBits + b.placeBits = b.bitsI + b.bitsC ∧ b.firstRow + 2 ^ b.rowBits ≤ rows ∧
      b.firstPlace + 2 ^ b.placeBits ≤ ell := by
    intro b hb
    have := h1 b hb
    simp only [blockB, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨⟨this.1.1.1.1, this.1.1.1.2⟩, this.1.1.2, this.1.2, this.2⟩
  obtain ⟨b, hbm, hbh⟩ := cover_all bs R K (fun b hb' => (hb b hb').1)
    ((pairwise_of_noPair meetB bs h2).imp fun h => disjoint_of_meetB h) h3 hi hc
  have hsome : (bs.find? fun b => laidHolds b i c).isSome = true :=
    List.find?_isSome.2 ⟨b, hbm, hbh⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hsome
  have m' : b' ∈ bs := List.mem_of_find?_eq_some hb'
  have p' : laidHolds b' i c = true := List.find?_some (p := fun b => laidHolds b i c) hb'
  refine ⟨laidIn b' i c, ?_, laidIn_lt p' (hb b' m').2.1 (hb b' m').2.2.1 (hb b' m').2.2.2⟩
  unfold laidPlace
  rw [hb']
  rfl

/-! ## 3 An array of the link; the mask row -/

/-- **The test on array number t of link i's list.** S: the written list. l: the signature's
list. -/
def arrB (S : Road.Rows.Shape) (D : Sent) (l : List (OracleShape × Nat)) (i t : Nat) : Bool :=
  match S.arrays[t]?, (D.arrayOf.getD i #[])[t]? with
  | some T, some bn =>
    bn.1 == i &&
      match OnBytes.reqArray D.layout i bn.2 with
      | some a =>
        match l[a.message]? with
        | some o => blocksB a.blocks T.R T.K o.1.mainRows (Johnson.Pack.pMain D.codes o.1).ell
        | none => false
      | none => false
  | _, _ => false

/-- **Under the test every cell of the array that has an entry has a seat, and the seat fits.** -/
theorem cell_resolves {S : Road.Rows.Shape} {D : Sent} {l : List (OracleShape × Nat)} {i t : ℕ}
    (h : arrB S D l i t = true) {r c : ℕ} (hj : (findJ S (.cell t r c)).isSome = true) :
    ∃ s, seatOf D i (.cell t r c) = some s ∧ s.Fits D.codes l := by
  unfold arrB at h
  split at h
  · rename_i T bn hT hbn
    rw [Bool.and_eq_true] at h
    obtain ⟨hi, h⟩ := h
    split at h
    · rename_i a ha
      split at h
      · rename_i o ho
        obtain ⟨ht, eT⟩ := List.getElem?_eq_some_iff.1 hT
        obtain ⟨hk, eo⟩ := List.getElem?_eq_some_iff.1 ho
        -- the entry's row and column are the array's
        have hrc : r < T.R ∧ c < T.K := by
          simp only [findJ, dif_pos ht] at hj
          obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hj
          obtain ⟨r', hr, hj⟩ := Option.bind_eq_some_iff.1 hj
          obtain ⟨c', hc, -⟩ := Option.map_eq_some_iff.1 hj
          unfold finOf at hr hc
          split at hr
          · split at hc
            · rename_i x1 x2
              rw [← eT]
              exact ⟨x1, x2⟩
            · cases hc
          · cases hr
        obtain ⟨rp, e1, e2, e3⟩ := laidPlace_some h hrc.1 hrc.2
        refine ⟨⟨a.message, false, rp.1, rp.2⟩, ?_, hk, ?_⟩
        · simp only [seatOf, hbn, Option.bind_some, hi, if_true, ha, e1, Option.map_some]
        · rw [if_neg (by simp)]
          show rp.1 < (l.get ⟨a.message, hk⟩).1.mainRows ∧ _
          rw [List.get_eq_getElem, eo]
          exact ⟨e2, e3⟩
      · cases h
    · cases h
  · cases h

/-- **The test on the mask row**: the link's first message with a mask row is in the signature's
list, has a mask row, and that row has at least «upTo» places. -/
def maskB (D : Sent) (l : List (OracleShape × Nat)) (i upTo : Nat) : Bool :=
  match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
  | some m =>
    match l[m]? with
    | some o => decide (0 < o.1.maskRows) && decide (upTo ≤ (Johnson.Pack.pMask D.codes o.1).ell)
    | none => false
  | none => false

theorem mask_resolves {D : Sent} {l : List (OracleShape × Nat)} {i upTo : ℕ}
    (h : maskB D l i upTo = true) {j : ℕ} (hj : j < upTo) :
    ∃ s, seatOf D i (.mask j) = some s ∧ s.Fits D.codes l := by
  unfold maskB at h
  split at h
  · rename_i m hm
    split at h
    · rename_i o ho
      obtain ⟨hk, eo⟩ := List.getElem?_eq_some_iff.1 ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨⟨m, true, 0, j⟩, ?_, hk, ?_⟩
      · simp only [seatOf, hm, Option.map_some]
      · rw [if_pos rfl]
        show 0 < (l.get ⟨m, hk⟩).1.maskRows ∧ _
        rw [List.get_eq_getElem, eo]
        exact ⟨h.1, Nat.lt_of_lt_of_le hj h.2⟩
    · cases h
  · cases h

#print axioms cover_all
#print axioms laidIn_lt
#print axioms laidPlace_some
#print axioms cell_resolves
#print axioms mask_resolves

end VerifiableInference.Desc.First.Look
