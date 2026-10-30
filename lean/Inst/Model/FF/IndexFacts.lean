-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/IndexFacts.lean: proofs of the facts on the index maps of a feed-forward segment.

  The file proves the ten statements `Spec.*` of Inst/Model/FF/Index.lean and `Spec.keyVecAt` of
  Inst/Model/FF/Trace.lean, for all sizes (every `Dim`; under `Dim.OK` where the statement asks for
  it; `addrBBij` if lp ≤ r). Each theorem has the name of its statement. In Lean names keys are the
  looked-up values (`key`, Inst/Model/FF/Trace.lean) and trees the batches of looked-up values of a
  call (`trees`, Inst/Model/FF/Index.lean).

    `posInj`, `posRange`, `posAligned`, `famAtPos`
                         the index map of a call, and its inverse `famAt`
    `treesTile`, `padCountEq`
                         the batches of the calls (with `callOf_spec`, `callOf_eq`) and their
                         padding positions (with `card_pad`, `card_not_pad`, `two_pow_Dk`)
    `addrRange`, `addrInj`, `addrBBij`, `blocks`
                         the addresses of the cells and of the bits B; blocks in a matrix that is
                         read by block reads
    `keyVecAt`           the key vector of a call has the keys at the columns of the index map (no
                         statement `Spec.*` gives its value at padding positions; the definition
                         of `keyVec`, Inst/Model/FF/Trace.lean, does: there it is the table's
                         padding value)

  The piece of an index x < n is fixed by arithmetic (`IsBit`); `bitOf`, which is written with xor
  and log2, has this property (`isBit_bitOf`).

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; its fields `r`, `lp`: a table of the
  look-up argument has 2^r rows, a multiplicity has 2^lp bits; `len`: n_s, the length of a family; a
  piece: `pieces`: the pieces of a call: family and exponent; `bitOf`: the exponent of the piece of
  a family of length n that contains the index x < n; `lJ`: log2 of J_c; `aC`: a_c: call c has
  2^(a_c) keys; `Dk`: D, where a number is meant: min(cap, min_c a_c); `NT`: N_T, the number of
  batches of all calls together; `padCount`: ϕ_θ, the number of padding positions of the batch θ;
  `lFeat`: the number of bits of the features in a column; `lRow`: log2 of n_1, the number of rows;
  B[ι, θ, π]: the bits at `addrB` (Inst/Model/FF/Index.lean).
-/
import Inst.Model.FF.Trace
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg.IndexFacts

variable [scl : Scl]

open Finset

/-! ## 0. Intervals placed end to end -/

section Tiling
variable {ι : Type} [DecidableEq ι] (P : Finset ι) (w : ι → ℕ) (lt : ι → ι → Prop) [DecidableRel lt]

/-- the sizes of all items before p, added up -/
def base (p : ι) : ℕ := ∑ q ∈ P, if lt q p then w q else 0

/-- lt is a strict total order on P -/
structure Ord : Prop where
  irrefl : ∀ p ∈ P, ¬ lt p p
  trans : ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, lt p q → lt q r → lt p r
  tri : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → lt p q ∨ lt q p

variable {P w lt}

omit scl in
theorem base_add_le (h : Ord P lt) {p q : ι} (hp : p ∈ P) (hq : q ∈ P) (hpq : lt p q) :
    base P w lt p + w p ≤ base P w lt q := by
  have e : w p = ∑ r ∈ P, if r = p then w r else 0 := by
    rw [Finset.sum_ite_eq' P p w, if_pos hp]
  unfold base
  calc
    (∑ r ∈ P, if lt r p then w r else 0) + w p =
        ∑ r ∈ P, ((if lt r p then w r else 0) + if r = p then w r else 0) := by
      rw [sum_add_distrib, ← e]
    _ ≤ ∑ r ∈ P, if lt r q then w r else 0 := by
      refine sum_le_sum fun r hr => ?_
      by_cases h1 : r = p
      · subst h1
        rw [if_neg (h.irrefl r hr), if_pos rfl, if_pos hpq, Nat.zero_add]
      · rw [if_neg h1, Nat.add_zero]
        by_cases h2 : lt r p
        · rw [if_pos h2, if_pos (h.trans r hr p hp q hq h2 hpq)]
        · rw [if_neg h2]
          exact Nat.zero_le _

omit scl in
theorem base_add_le_total (h : Ord P lt) {p : ι} (hp : p ∈ P) :
    base P w lt p + w p ≤ ∑ q ∈ P, w q := by
  have e : w p = ∑ r ∈ P, if r = p then w r else 0 := by
    rw [Finset.sum_ite_eq' P p w, if_pos hp]
  unfold base
  calc
    (∑ r ∈ P, if lt r p then w r else 0) + w p =
        ∑ r ∈ P, ((if lt r p then w r else 0) + if r = p then w r else 0) := by
      rw [sum_add_distrib, ← e]
    _ ≤ ∑ r ∈ P, w r := by
      refine sum_le_sum fun r hr => ?_
      by_cases h1 : r = p
      · subst h1
        rw [if_neg (h.irrefl r hr), if_pos rfl, Nat.zero_add]
      · rw [if_neg h1, Nat.add_zero]
        split_ifs
        · exact le_rfl
        · exact Nat.zero_le _

omit scl in
/-- Under `Ord P lt`, two items of P whose intervals share a number are equal. -/
theorem tile_inj (h : Ord P lt) {p q : ι} (hp : p ∈ P) (hq : q ∈ P) {j : ℕ} (h1 : base P w lt p ≤ j)
    (h2 : j < base P w lt p + w p) (h3 : base P w lt q ≤ j) (h4 : j < base P w lt q + w q) :
    p = q := by
  by_contra hne
  rcases h.tri p hp q hq hne with h5 | h5
  · have := base_add_le (w := w) h hp hq h5
    omega
  · have := base_add_le (w := w) h hq hp h5
    omega

omit scl in
/-- Under `Ord P lt`, the intervals cover the numbers below the sum of all sizes. -/
theorem tile_cover (h : Ord P lt) {j : ℕ} (hj : j < ∑ q ∈ P, w q) :
    ∃ p ∈ P, base P w lt p ≤ j ∧ j < base P w lt p + w p := by
  have hsub : (P.biUnion fun p => Ico (base P w lt p) (base P w lt p + w p)) ⊆
      range (∑ q ∈ P, w q) := by
    intro a ha
    obtain ⟨p, hp, hap⟩ := mem_biUnion.mp ha
    have := base_add_le_total (w := w) h hp
    have := (mem_Ico.mp hap).2
    exact mem_range.mpr (by omega)
  have hcard : (P.biUnion fun p => Ico (base P w lt p) (base P w lt p + w p)).card =
      ∑ q ∈ P, w q := by
    rw [card_biUnion]
    · exact sum_congr rfl fun p _ => by rw [Nat.card_Ico]; omega
    · intro p hp q hq hne
      refine disjoint_left.mpr fun a ha hb => hne ?_
      exact tile_inj h hp hq (mem_Ico.mp ha).1 (mem_Ico.mp ha).2 (mem_Ico.mp hb).1 (mem_Ico.mp hb).2
  have heq := eq_of_subset_of_card_le hsub (by rw [card_range, hcard])
  have hm : j ∈ P.biUnion fun p => Ico (base P w lt p) (base P w lt p + w p) := by
    rw [heq]
    exact mem_range.mpr hj
  obtain ⟨p, hp, hap⟩ := mem_biUnion.mp hm
  exact ⟨p, hp, (mem_Ico.mp hap).1, (mem_Ico.mp hap).2⟩

end Tiling

/-! ## 1. Binary digits -/

omit scl in
theorem testBit_iff (n b : ℕ) : n.testBit b = true ↔ n / 2 ^ b % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

omit scl in
/-- The binary digits below k add up to n mod 2^k. -/
theorem sum_bits (n k : ℕ) : ∑ b ∈ range k, (if n.testBit b then 2 ^ b else 0) = n % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [sum_range_succ, ih, Nat.mod_pow_succ]
    by_cases h : n.testBit k = true
    · rw [if_pos h, (testBit_iff n k).mp h, Nat.mul_one]
    · have h0 : n / 2 ^ k % 2 = 0 := by
        have := (testBit_iff n k).not.mp h
        omega
      rw [if_neg h, h0, Nat.mul_zero]

omit scl in
theorem sum_bits_size (n : ℕ) :
    ∑ b ∈ range (Nat.size n), (if n.testBit b then 2 ^ b else 0) = n := by
  rw [sum_bits, Nat.mod_eq_of_lt (Nat.lt_size_self n)]

omit scl in
theorem lt_size_of_testBit {n b : ℕ} (h : n.testBit b = true) : b < Nat.size n := by
  by_contra hc
  have h1 : n < 2 ^ b :=
    lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hc))
  rw [Nat.testBit_lt_two_pow h1] at h
  exact Bool.false_ne_true h

/-- b is the highest binary digit position in which x and n differ, and n has the digit 1 there -/
def IsBit (n x b : ℕ) : Prop :=
  n / 2 ^ (b + 1) = x / 2 ^ (b + 1) ∧ n / 2 ^ b % 2 = 1 ∧ x / 2 ^ b % 2 = 0

omit scl in
theorem div_pow_of_le {n x a c : ℕ} (h : n / 2 ^ a = x / 2 ^ a) (hac : a ≤ c) :
    n / 2 ^ c = x / 2 ^ c := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hac
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

omit scl in
theorem isBit_unique {n x b b' : ℕ} (h : IsBit n x b) (h' : IsBit n x b') : b = b' := by
  rcases lt_trichotomy b b' with hlt | heq | hlt
  · have := div_pow_of_le h.1 (show b + 1 ≤ b' from hlt)
    have h1 := h'.2.1
    have h2 := h'.2.2
    rw [this] at h1
    omega
  · exact heq
  · have := div_pow_of_le h'.1 (show b' + 1 ≤ b from hlt)
    have h1 := h.2.1
    have h2 := h.2.2
    rw [this] at h1
    omega

omit scl in
theorem isBit_bitOf {n x : ℕ} (h : x < n) : IsBit n x (bitOf n x) := by
  unfold bitOf
  set z := n ^^^ x with hz
  have hz0 : z ≠ 0 := by
    intro h0
    have := Nat.xor_eq_zero_iff.mp h0
    omega
  set k := Nat.log2 z with hk
  have h1 : z.testBit k = true := Nat.testBit_log2 hz0
  have h2 : ∀ j, k < j → z.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hj))
  have hx : ∀ j, z.testBit j = (n.testBit j ^^ x.testBit j) := fun j => Nat.testBit_xor n x j
  have hagree : ∀ j, k < j → x.testBit j = n.testBit j := fun j hj => by
    have := h2 j hj
    rw [hx j] at this
    cases hn : n.testBit j <;> cases hxx : x.testBit j <;> simp_all
  have hdiff := h1
  rw [hx k] at hdiff
  have hnk : n.testBit k = true := by
    by_contra hc
    have hn0 : n.testBit k = false := by simpa using hc
    have hx1 : x.testBit k = true := by
      rw [hn0] at hdiff
      simpa using hdiff
    have := Nat.lt_of_testBit k hn0 hx1 (fun j hj => (hagree j hj).symm)
    omega
  have hxk : x.testBit k = false := by
    rw [hnk] at hdiff
    simpa using hdiff
  refine ⟨?_, (testBit_iff n k).mp hnk, ?_⟩
  · refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact (hagree _ (by omega)).symm
  · have := (testBit_iff x k).not.mp (by rw [hxk]; exact Bool.false_ne_true)
    omega

omit scl in
theorem bitOf_eq {n x b : ℕ} (h : IsBit n x b) (hx : x < n) : bitOf n x = b :=
  isBit_unique (isBit_bitOf hx) h

omit scl in
/-- If `IsBit n x b`, then x is the first index of the piece of size 2^b plus x mod 2^b, and the
piece ends at or before n. -/
theorem isBit_split {n x b : ℕ} (h : IsBit n x b) :
    x = pieceStart n b + x % 2 ^ b ∧ pieceStart n b + 2 ^ b ≤ n := by
  obtain ⟨h1, h2, h3⟩ := h
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at h1
  unfold pieceStart
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have ex := Nat.div_add_mod x (2 ^ b)
  have en := Nat.div_add_mod n (2 ^ b)
  generalize 2 ^ b = Q at *
  generalize hxa : x / Q = xa at *
  generalize hna : n / Q = na at *
  have e1 : xa = 2 * (na / 2) := by omega
  have e2 : na = 2 * (na / 2) + 1 := by omega
  generalize na / 2 = q at *
  generalize x % Q = rx at *
  generalize n % Q = rn at *
  subst e1
  constructor
  · rw [← ex]
    ring
  · rw [e2] at en
    rw [← en]
    have e5 : Q * (2 * q + 1) = q * (Q * 2) + Q := by ring
    omega

omit scl in
/-- If n has the digit 1 at b, every index of the piece of size 2^b satisfies `IsBit` at b and, in
particular, is below n. -/
theorem isBit_piece {n b y : ℕ} (hb : n / 2 ^ b % 2 = 1) (hy : y < 2 ^ b) :
    IsBit n (pieceStart n b + y) b ∧ (pieceStart n b + y) % 2 ^ b = y ∧ pieceStart n b + y < n := by
  have hP : 0 < 2 ^ b := Nat.two_pow_pos b
  have e0 : pieceStart n b = 2 ^ b * (2 * (n / 2 ^ b / 2)) := by
    unfold pieceStart
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    ring
  have e1 : (pieceStart n b + y) / 2 ^ b = 2 * (n / 2 ^ b / 2) := by
    rw [e0, Nat.mul_add_div hP, Nat.div_eq_of_lt hy, Nat.add_zero]
  have e2 : (pieceStart n b + y) % 2 ^ b = y := by
    rw [e0, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  refine ⟨⟨?_, hb, by rw [e1]; omega⟩, e2, ?_⟩
  · rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1]
    omega
  · have en := Nat.div_add_mod n (2 ^ b)
    rw [e0]
    generalize 2 ^ b = Q at *
    generalize n / Q = na at *
    have e3 : na = 2 * (na / 2) + 1 := by omega
    generalize na / 2 = q at *
    generalize n % Q = rn at *
    rw [e3] at en
    have e5 : Q * (2 * q + 1) = Q * (2 * q) + Q := by ring
    omega

/-! ## 2. The pieces of a call, and the index map -/

omit scl in
theorem fams_nodup : ∀ c : Fin 8, (fams c).Nodup := by decide

omit scl in
theorem call_of_mem : ∀ c : Fin 8, ∀ s ∈ fams c, call s = c := by decide

omit scl in
theorem mem_fams_call (s : Fam) : s ∈ fams (call s) := by cases s <;> decide

omit scl in
theorem mem_fams_iff {s : Fam} {c : Fin 8} : s ∈ fams c ↔ call s = c :=
  ⟨call_of_mem c s, fun h => h ▸ mem_fams_call s⟩

omit scl in
theorem ord_inj {s s' : Fam} (hc : call s = call s') (h : ord s = ord s') : s = s' := by
  unfold ord at h
  rw [← hc] at h
  exact (List.idxOf_inj (mem_fams_call s)).mp h

variable (D : Dim)

/-- a piece: a family and an exponent -/
abbrev Pc : Type := (_ : Fam) × ℕ

/-- the pieces of a call -/
def PS (c : Fin 8) : Finset Pc :=
  (fams c).toFinset.sigma fun s =>
    (range (Nat.size (len D s))).filter fun b => (len D s).testBit b = true

def wP (q : Pc) : ℕ := 2 ^ q.2

/-- q comes before p: it is larger, or as large and of an earlier family -/
def ltP (q p : Pc) : Prop := p.2 < q.2 ∨ (q.2 = p.2 ∧ ord q.1 < ord p.1)

instance : DecidableRel ltP := fun q p => by unfold ltP; infer_instance

omit scl in
theorem mem_PS {c : Fin 8} {s : Fam} {b : ℕ} :
    (⟨s, b⟩ : Pc) ∈ PS D c ↔ call s = c ∧ (len D s).testBit b = true := by
  unfold PS
  rw [mem_sigma, List.mem_toFinset, mem_fams_iff, mem_filter, mem_range]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, lt_size_of_testBit h.2, h.2⟩⟩

omit scl in
theorem ord_PS (c : Fin 8) : Ord (PS D c) ltP where
  irrefl := fun p _ h => by
    unfold ltP at h
    omega
  trans := fun p _ q _ r _ h1 h2 => by
    unfold ltP at *
    omega
  tri := fun p hp q hq hne => by
    obtain ⟨s, b⟩ := p
    obtain ⟨s', b'⟩ := q
    have h1 := ((mem_PS D).mp hp).1
    have h2 := ((mem_PS D).mp hq).1
    unfold ltP
    by_cases hb : b = b'
    · subst hb
      have hs : ord s ≠ ord s' := fun h => hne (by rw [ord_inj (h1.trans h2.symm) h])
      show (b < b ∨ (b = b ∧ ord s < ord s')) ∨ (b < b ∨ (b = b ∧ ord s' < ord s))
      omega
    · show (b' < b ∨ (b = b' ∧ ord s < ord s')) ∨ (b < b' ∨ (b' = b ∧ ord s' < ord s))
      omega

omit scl in
/-- the first column of a piece is the sum of the sizes of the pieces before it -/
theorem colBase_eq (s : Fam) (b : ℕ) : colBase D s b = base (PS D (call s)) wP ltP ⟨s, b⟩ := by
  unfold colBase base PS
  rw [sum_sigma, ← List.sum_toFinset _ (fams_nodup (call s))]
  refine sum_congr rfl fun s' _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun b' _ => ?_
  unfold ltP wP
  by_cases h1 : (len D s').testBit b' = true
  · simp only [h1, true_and, if_true]
  · simp only [h1, false_and, if_false, Bool.false_eq_true]

omit scl in
theorem total_PS (c : Fin 8) : ∑ q ∈ PS D c, wP q = used D c := by
  unfold PS used
  rw [sum_sigma, ← List.sum_toFinset _ (fams_nodup c)]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_filter]
  exact sum_bits_size (len D s)

omit scl in
/-- The column of an index x < n_s is within the interval of the piece with the exponent `bitOf`. -/
theorem pos_in {s : Fam} {x : ℕ} (hx : x < len D s) :
    (⟨s, bitOf (len D s) x⟩ : Pc) ∈ PS D (call s) ∧
    base (PS D (call s)) wP ltP ⟨s, bitOf (len D s) x⟩ ≤ pos D s x ∧
    pos D s x < base (PS D (call s)) wP ltP ⟨s, bitOf (len D s) x⟩ + wP ⟨s, bitOf (len D s) x⟩ := by
  have hb := isBit_bitOf hx
  refine ⟨(mem_PS D).mpr ⟨rfl, (testBit_iff _ _).mpr hb.2.1⟩, ?_, ?_⟩
  · unfold pos
    rw [colBase_eq]
    exact Nat.le_add_right _ _
  · unfold pos
    rw [colBase_eq]
    exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _

omit scl in
/-- The index number y of a piece of size 2^b is below n_s and gets the column `colBase` + y. -/
theorem pos_piece {s : Fam} {b y : ℕ} (hb : (len D s).testBit b = true) (hy : y < 2 ^ b) :
    pieceStart (len D s) b + y < len D s ∧
    pos D s (pieceStart (len D s) b + y) = colBase D s b + y := by
  obtain ⟨h1, h2, h3⟩ := isBit_piece ((testBit_iff _ _).mp hb) hy
  refine ⟨h3, ?_⟩
  unfold pos
  rw [bitOf_eq h1 h3, h2]

omit scl in
/-- The index map of a call is injective. -/
theorem posInj : Spec.posInj := by
  intro D s s' x x' hc hx hx' h
  obtain ⟨a1, a2, a3⟩ := pos_in D hx
  obtain ⟨b1, b2, b3⟩ := pos_in D hx'
  rw [← hc] at b1 b2 b3
  rw [← h] at b2 b3
  have e := tile_inj (ord_PS D (call s)) a1 b1 a2 a3 b2 b3
  have es : s = s' := congrArg Sigma.fst e
  subst es
  refine ⟨rfl, ?_⟩
  have eb : bitOf (len D s) x = bitOf (len D s) x' := by
    have := congrArg (fun q : Pc => q.2) e
    exact this
  have h1 := (isBit_split (isBit_bitOf hx)).1
  have h2 := (isBit_split (isBit_bitOf hx')).1
  unfold pos at h
  rw [← eb] at h h2
  have h3 : x % 2 ^ bitOf (len D s) x = x' % 2 ^ bitOf (len D s) x := Nat.add_left_cancel h
  rw [h1, h2, h3]

omit scl in
/-- The image of the index map of a call is an initial range of the columns. -/
theorem posRange : Spec.posRange := by
  intro D c jj
  constructor
  · intro hj
    rw [← total_PS] at hj
    obtain ⟨⟨s, b⟩, hp, h1, h2⟩ := tile_cover (ord_PS D c) hj
    obtain ⟨hc, hb⟩ := (mem_PS D).mp hp
    subst hc
    rw [← colBase_eq] at h1 h2
    obtain ⟨k1, k2⟩ :=
      pos_piece D hb (y := jj - colBase D s b) (by unfold wP at h2; simp only at h2; omega)
    exact ⟨s, mem_fams_call s, _, k1, by rw [k2]; omega⟩
  · rintro ⟨s, hs, x, hx, rfl⟩
    have hc := mem_fams_iff.mp hs
    subst hc
    obtain ⟨a1, _, a3⟩ := pos_in D hx
    have := base_add_le_total (w := wP) (ord_PS D (call s)) a1
    rw [total_PS] at this
    omega

omit scl in
theorem mem_pieces {c : Fin 8} {s : Fam} {b : ℕ} :
    (s, b) ∈ pieces D c ↔ call s = c ∧ (len D s).testBit b = true := by
  unfold pieces
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', b', ⟨_, hb'⟩, rfl, rfl⟩
    exact ⟨mem_fams_iff.mp hs', hb'⟩
  · rintro ⟨hc, hb⟩
    exact ⟨s, mem_fams_iff.mpr hc, b, ⟨lt_size_of_testBit hb, hb⟩, rfl, rfl⟩

omit scl in
/-- If every item on which f is defined gives a, and there is one, the first gives a. -/
theorem findSome_eq {α β : Type} {f : α → Option β} {a : β} :
    ∀ {l : List α},
      (∀ p ∈ l, ∀ a', f p = some a' → a' = a) → (∃ p ∈ l, f p = some a) → l.findSome? f = some a
  | [], _, h => by
    obtain ⟨p, hp, _⟩ := h
    exact absurd hp (List.not_mem_nil)
  | p :: l, h1, h2 => by
    rw [List.findSome?_cons]
    cases hf : f p with
    | some a' => rw [h1 p (List.mem_cons_self) a' hf]
    | none =>
      refine findSome_eq (fun q hq => h1 q (List.mem_cons_of_mem _ hq)) ?_
      obtain ⟨q, hq, hfq⟩ := h2
      rcases List.mem_cons.mp hq with rfl | hq'
      · rw [hf] at hfq
        exact absurd hfq (by simp)
      · exact ⟨q, hq', hfq⟩

omit scl in
/-- `famAt` is the inverse of `pos`. -/
theorem famAtPos : Spec.famAtPos := by
  intro D c jj s x
  have key : ∀ p ∈ pieces D c, ∀ a',
      (if colBase D p.1 p.2 ≤ jj ∧ jj < colBase D p.1 p.2 + 2 ^ p.2 then
            some (p.1, pieceStart (len D p.1) p.2 + (jj - colBase D p.1 p.2))
          else none) = some a' →
      call a'.1 = c ∧ a'.2 < len D a'.1 ∧ pos D a'.1 a'.2 = jj := by
    rintro ⟨s', b'⟩ hp a' ha
    obtain ⟨hc, hb⟩ := (mem_pieces D).mp hp
    by_cases hcond : colBase D s' b' ≤ jj ∧ jj < colBase D s' b' + 2 ^ b'
    · rw [if_pos hcond] at ha
      have ea := Option.some.inj ha
      subst ea
      obtain ⟨k1, k2⟩ := pos_piece D hb (y := jj - colBase D s' b') (by omega)
      exact ⟨hc, k1, by show pos D s' _ = jj; rw [k2]; omega⟩
    · rw [if_neg hcond] at ha
      exact absurd ha (by simp)
  constructor
  · intro h
    obtain ⟨p, hp, hf⟩ := List.exists_of_findSome?_eq_some h
    exact key p hp (s, x) hf
  · rintro ⟨hc, hx, hpos⟩
    subst hc
    refine findSome_eq (fun p hp a' ha => ?_) ?_
    · obtain ⟨k1, k2, k3⟩ := key p hp a' ha
      obtain ⟨e1, e2⟩ := posInj D a'.1 s a'.2 x k1 k2 hx (k3.trans hpos.symm)
      exact Prod.ext e1 e2
    · have hb := isBit_bitOf hx
      refine ⟨(s, bitOf (len D s) x), (mem_pieces D).mpr ⟨rfl, (testBit_iff _ _).mpr hb.2.1⟩, ?_⟩
      have e1 : pos D s x = colBase D s (bitOf (len D s) x) + x % 2 ^ bitOf (len D s) x := rfl
      have hm := Nat.mod_lt x (Nat.two_pow_pos (bitOf (len D s) x))
      show (if colBase D s (bitOf (len D s) x) ≤ jj ∧
              jj < colBase D s (bitOf (len D s) x) + 2 ^ bitOf (len D s) x then _
          else _) = _
      rw [if_pos ⟨by omega, by omega⟩]
      have e2 : jj - colBase D s (bitOf (len D s) x) = x % 2 ^ bitOf (len D s) x := by omega
      rw [e2, ← (isBit_split hb).1]

/-! ### Aligned runs -/

omit scl in
theorem even_div_of_dvd {n b a : ℕ} (h : 2 ^ b ∣ n) (ha : a < b) : n / 2 ^ a % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt ha
  have e1 : 2 ^ (a + e + 1) * k = 2 ^ a * (2 * (2 ^ e * k)) := by ring
  rw [e1, Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  omega

omit scl in
theorem div_add_small {b a x' x'' : ℕ} (hx : x'' < 2 ^ b) (hab : b ≤ a) :
    (2 ^ b * x' + x'') / 2 ^ a = 2 ^ b * x' / 2 ^ a := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.mul_add_div (Nat.two_pow_pos b), Nat.div_eq_of_lt hx, Nat.add_zero,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos b)]

omit scl in
/-- If 2^b divides n_s, an aligned run of 2^b indices takes 2^b consecutive columns, which start at
a multiple of 2^b. -/
theorem posAligned : Spec.posAligned := by
  intro D s b x' x'' hd hX hx''
  have hβ := isBit_bitOf hX
  set n := len D s with hn
  set β := bitOf n (2 ^ b * x') with hβd
  have hbβ : b ≤ β := by
    by_contra hc
    have := even_div_of_dvd hd (Nat.lt_of_not_le hc)
    have := hβ.2.1
    omega
  have hlt : 2 ^ b * x' + x'' < n := by
    obtain ⟨k, hk⟩ := hd
    rw [hk] at hX ⊢
    have h1 : x' < k := Nat.lt_of_mul_lt_mul_left hX
    calc 2 ^ b * x' + x'' < 2 ^ b * x' + 2 ^ b := Nat.add_lt_add_left hx'' _
      _ = 2 ^ b * (x' + 1) := by ring
      _ ≤ 2 ^ b * k := Nat.mul_le_mul_left _ h1
  have hβ' : IsBit n (2 ^ b * x' + x'') β :=
    ⟨by rw [div_add_small hx'' (by omega)]; exact hβ.1,
      hβ.2.1,
      by rw [div_add_small hx'' hbβ]; exact hβ.2.2⟩
  have hmod : (2 ^ b * x' + x'') % 2 ^ β = 2 ^ b * x' % 2 ^ β + x'' := by
    have h1 := Nat.div_add_mod (2 ^ b * x' + x'') (2 ^ β)
    have h2 := Nat.div_add_mod (2 ^ b * x') (2 ^ β)
    rw [div_add_small hx'' hbβ] at h1
    omega
  constructor
  · show colBase D s (bitOf n (2 ^ b * x' + x'')) +
        (2 ^ b * x' + x'') % 2 ^ bitOf n (2 ^ b * x' + x'') =
      colBase D s β + 2 ^ b * x' % 2 ^ β + x''
    rw [bitOf_eq hβ' hlt, hmod, Nat.add_assoc]
  · show 2 ^ b ∣ colBase D s β + 2 ^ b * x' % 2 ^ β
    refine Nat.dvd_add ?_ ((Nat.dvd_mod_iff (pow_dvd_pow 2 hbβ)).mpr (Nat.dvd_mul_right _ _))
    rw [colBase_eq]
    refine Finset.dvd_sum fun q _ => ?_
    by_cases hq : ltP q ⟨s, β⟩
    · rw [if_pos hq]
      have hq' : β < q.2 ∨ (q.2 = β ∧ ord q.1 < ord s) := hq
      exact pow_dvd_pow 2 (by omega)
    · rw [if_neg hq]
      exact Nat.dvd_zero _

/-! ## 3. The batches of the calls -/

/-- c' comes before c: it is larger, or as large and has a smaller number -/
def ltT (c' c : Fin 8) : Prop := aC D c < aC D c' ∨ (aC D c' = aC D c ∧ c' < c)

instance : DecidableRel (ltT D) := fun c' c => by unfold ltT; infer_instance

omit scl in
theorem ord_T : Ord (Finset.univ : Finset (Fin 8)) (ltT D) where
  irrefl := fun p _ h => by
    unfold ltT at h
    rcases h with h | h
    · omega
    · exact absurd h.2 (lt_irrefl _)
  trans := fun p _ q _ r _ h1 h2 => by
    unfold ltT at *
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, lt_trans h1.2 h2.2⟩
  tri := fun p _ q _ hne => by
    unfold ltT
    rcases lt_trichotomy (aC D p) (aC D q) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inl (Or.inl h)

omit scl in
theorem firstTree_eq (c : Fin 8) : firstTree D c = base Finset.univ (trees D) (ltT D) c := rfl

omit scl in
/-- the batch θ < N_T is in the block of its call -/
theorem callOf_spec {θ : ℕ} (hθ : θ < NT D) :
    firstTree D (callOf D θ) ≤ θ ∧ θ < firstTree D (callOf D θ) + trees D (callOf D θ) := by
  obtain ⟨c0, _, h1, h2⟩ := tile_cover (w := trees D) (ord_T D) (j := θ) hθ
  unfold callOf
  cases hf : (List.finRange 8).find? fun c =>
      decide (firstTree D c ≤ θ ∧ θ < firstTree D c + trees D c) with
  | none =>
    have := List.find?_eq_none.mp hf c0 (List.mem_finRange c0)
    exact absurd
      (decide_eq_true (show firstTree D c0 ≤ θ ∧ θ < firstTree D c0 + trees D c0 from ⟨h1, h2⟩))
      this
  | some c =>
    have := List.find?_some hf
    exact of_decide_eq_true this

omit scl in
/-- a batch is in the block of one call only -/
theorem callOf_eq {θ : ℕ} {c : Fin 8} (h1 : firstTree D c ≤ θ)
    (h2 : θ < firstTree D c + trees D c) : callOf D θ = c := by
  have hθ : θ < NT D := lt_of_lt_of_le h2 (base_add_le_total (w := trees D) (ord_T D) (mem_univ c))
  obtain ⟨h3, h4⟩ := callOf_spec D hθ
  exact tile_inj (w := trees D) (ord_T D) (mem_univ _) (mem_univ _) h3 h4 h1 h2

omit scl in
/-- The batches of the calls are the numbers below N_T, each call a block that starts at a multiple
of its number of batches. -/
theorem treesTile : Spec.treesTile := by
  intro D
  refine ⟨fun θ hθ => callOf_spec D hθ,
    fun c => ⟨?_, base_add_le_total (w := trees D) (ord_T D) (mem_univ c)⟩⟩
  rw [firstTree_eq]
  refine Finset.dvd_sum fun c' _ => ?_
  by_cases hq : ltT D c' c
  · rw [if_pos hq]
    have hq' : aC D c < aC D c' ∨ (aC D c' = aC D c ∧ c' < c) := hq
    exact pow_dvd_pow 2 (by omega)
  · rw [if_neg hq]
    exact Nat.dvd_zero _

/-! ## 4. Addresses -/

omit scl in
theorem mr_inj {n a a' r r' : ℕ} (hr : r < n) (hr' : r' < n) (h : a * n + r = a' * n + r') :
    a = a' ∧ r = r' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have h1 : (a * n + r) / n = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]
  have h2 : (a' * n + r') / n = a' := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr', Nat.add_zero]
  have e : a = a' := by rw [← h1, ← h2, h]
  subst e
  exact ⟨rfl, Nat.add_left_cancel h⟩

omit scl in
theorem mr_lt {n m a r : ℕ} (ha : a < m) (hr : r < n) : a * n + r < m * n :=
  calc a * n + r < a * n + n := Nat.add_lt_add_left hr _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha

section Lists
variable {α : Type} [DecidableEq α] (g : α → ℕ)

/-- the sizes of the items of a list before X, added up -/
def offL (l : List α) (X : α) : ℕ := ((l.takeWhile (· != X)).map g).sum

omit scl in
theorem offL_cons_self (l : List α) (X : α) : offL g (X :: l) X = 0 := by
  unfold offL
  rw [List.takeWhile_cons_of_neg (by simp)]
  rfl

omit scl in
theorem offL_cons_ne (l : List α) {a X : α} (h : a ≠ X) : offL g (a :: l) X = g a + offL g l X := by
  unfold offL
  rw [List.takeWhile_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons]

omit scl in
theorem offL_add_le : ∀ {l : List α} {X : α}, X ∈ l → offL g l X + g X ≤ (l.map g).sum
  | a :: l, X, h => by
    rw [List.map_cons, List.sum_cons]
    by_cases ha : a = X
    · subst ha
      rw [offL_cons_self]
      omega
    · rw [offL_cons_ne g l ha]
      have := offL_add_le (l := l) (X := X) ((List.mem_cons.mp h).resolve_left (Ne.symm ha))
      omega

omit scl in
theorem offL_disj :
    ∀ {l : List α} {X X' : α},
      X ∈ l → X' ∈ l → X ≠ X' → offL g l X + g X ≤ offL g l X' ∨ offL g l X' + g X' ≤ offL g l X
  | a :: l, X, X', h, h', hne => by
    by_cases ha : a = X
    · subst ha
      rw [offL_cons_self, offL_cons_ne g l hne]
      exact Or.inl (by omega)
    · by_cases ha' : a = X'
      · subst ha'
        rw [offL_cons_self, offL_cons_ne g l ha]
        exact Or.inr (by omega)
      · rw [offL_cons_ne g l ha, offL_cons_ne g l ha']
        rcases offL_disj (l := l) ((List.mem_cons.mp h).resolve_left (Ne.symm ha))
          ((List.mem_cons.mp h').resolve_left (Ne.symm ha')) hne with h1 | h1
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)

omit scl in
theorem dvd_offL {k : ℕ} {l : List α} (h : ∀ a ∈ l, k ∣ g a) (X : α) : k ∣ offL g l X := by
  unfold offL
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact h a ((List.takeWhile_prefix _).subset ha)

end Lists

omit scl in
theorem mem_arrs (X : Arr) : X ∈ arrs X.mx := by cases X <;> decide

omit scl in
theorem mx_of_mem : ∀ μ : Mx, ∀ X ∈ arrs μ, X.mx = μ := by
  intro μ
  cases μ <;> decide

omit scl in
theorem OFF_eq (X : Arr) : OFF D X = offL (Arr.nFeat D) (arrs X.mx) X := rfl

omit scl in
theorem T_pos : 0 < D.T := Nat.two_pow_pos _

omit scl in
/-- the features of an array (k, inst, j in range) lie in the range from OFF_X, of length `nFeat` -/
theorem feat_in {X : Arr} {k inst j : ℕ} (hk : k < X.nCell)
    (hi : inst < X.cnt D) (hj : j < X.width D) :
    OFF D X ≤ feat D X k inst j ∧ feat D X k inst j < OFF D X + X.nFeat D := by
  unfold feat Arr.nFeat
  have := mr_lt (mr_lt hk hi) hj
  omega

omit scl in
theorem feat_lt {X : Arr} {k inst j : ℕ} (hk : k < X.nCell)
    (hi : inst < X.cnt D) (hj : j < X.width D) :
    feat D X k inst j < nFeatMx D X.mx := by
  have h1 := (feat_in D hk hi hj).2
  have h2 : OFF D X + X.nFeat D ≤ nFeatMx D X.mx := offL_add_le (Arr.nFeat D) (mem_arrs X)
  omega

omit scl in
theorem featAt_inj {μ : Mx} {φ φ' i i' : ℕ} (hi : i < D.T) (hi' : i' < D.T)
    (h : featAt D μ φ i = featAt D μ φ' i') : φ = φ' ∧ i = i' := by
  unfold featAt at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨h3, h4⟩ := mr_inj hi hi' h1
  refine ⟨?_, h4⟩
  rw [← Nat.div_add_mod φ (2 ^ lFeat D μ), ← Nat.div_add_mod φ' (2 ^ lFeat D μ), h2, h3]

omit scl in
theorem lRow_eq {μ : Mx} (h : μ ≠ .b) : lRow D μ = lFeat D μ + D.lT := by
  cases μ <;> first | rfl | exact absurd rfl h

omit scl in
theorem mx_ne_b (X : Arr) : X.mx ≠ .b := by cases X <;> decide

omit scl in
theorem div_lt_ceil {φ n Q : ℕ} (hQ : 0 < Q) (h : φ < n) : φ / Q < (n + Q - 1) / Q := by
  rw [Nat.div_lt_iff_lt_mul hQ]
  have := Nat.lt_div_mul_add (a := n + Q - 1) hQ
  omega

omit scl in
/-- Under `Dim.OK`, every feature of a matrix other than b is in one of its columns. -/
theorem col_lt (hD : D.OK) {μ : Mx} (hμ : μ ≠ .b) {φ : ℕ} (h : φ < nFeatMx D μ) :
    φ / 2 ^ lFeat D μ < nCol D μ := by
  have hc := div_lt_ceil (Nat.two_pow_pos (lFeat D μ)) h
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    show φ / 2 ^ D.fBig < D.parts * afCols D
    have hc' : φ / 2 ^ D.fBig < (nFeatMx D .af + 2 ^ D.fBig - 1) / 2 ^ D.fBig := hc
    unfold afCols
    have :=
      Nat.lt_div_mul_add (a := (nFeatMx D .af + 2 ^ D.fBig - 1) / 2 ^ D.fBig + D.parts - 1) hD.parts
    rw [Nat.mul_comm D.parts]
    omega
  | ad => exact hc
  | ar => exact hc
  | qa => exact hc
  | xin => exact hc
  | xout => exact hc

omit scl in
/-- Under `Dim.OK`, the row and the column of every valid cell are within its matrix. -/
theorem addrRange : Spec.addrRange := by
  intro D hD c hc
  obtain ⟨hk, hi, hj, hp⟩ := hc
  refine ⟨?_, col_lt D hD (mx_ne_b c.X) (feat_lt D hk hi hj)⟩
  show feat D c.X c.k c.inst c.j % 2 ^ lFeat D c.X.mx * D.T + c.i < 2 ^ lRow D c.X.mx
  rw [lRow_eq D (mx_ne_b c.X), pow_add]
  exact mr_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) hp

omit scl in
/-- Under `Dim.OK`, distinct valid cells have distinct addresses. -/
theorem addrInj : Spec.addrInj := by
  intro D _ c c' hc hc' h
  obtain ⟨hk, hi, hj, hp⟩ := hc
  obtain ⟨hk', hi', hj', hp'⟩ := hc'
  obtain ⟨X, k, inst, j, i⟩ := c
  obtain ⟨X', k', inst', j', i'⟩ := c'
  simp only at hk hi hj hp hk' hi' hj' hp'
  unfold addr at h
  obtain ⟨hm, hf⟩ := Prod.mk.inj h
  simp only at hm hf
  rw [← hm] at hf
  obtain ⟨hφ, hii⟩ := featAt_inj D hp hp' hf
  have hX : X = X' := by
    by_contra hne
    have a1 := feat_in D hk hi hj
    have a2 := feat_in D hk' hi' hj'
    have hmem : X' ∈ arrs X.mx := hm ▸ mem_arrs X'
    have e2 : OFF D X' = offL (Arr.nFeat D) (arrs X.mx) X' := by rw [OFF_eq, hm]
    rcases offL_disj (Arr.nFeat D) (mem_arrs X) hmem hne with h1 | h1
    · rw [← OFF_eq, ← e2] at h1
      omega
    · rw [← OFF_eq, ← e2] at h1
      omega
  subst hX
  unfold feat at hφ
  obtain ⟨h1, h2⟩ :=
    mr_inj hj hj' (Nat.add_left_cancel (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hφ))
  obtain ⟨h3, h4⟩ := mr_inj hi hi' h1
  subst h2 h3 h4 hii
  rfl

omit scl in
/-- Under `Dim.OK`, in a matrix that is read by block reads, a block holds consecutive channels of
one (array, k, instance). -/
theorem blocks : Spec.blocks := by
  intro D hD X hX k inst jb j2 _
  refine ⟨?_, by unfold feat; omega⟩
  unfold feat
  refine Nat.dvd_add (Nat.dvd_add ?_ (Dvd.dvd.mul_left (hD.blk X hX) _)) (Nat.dvd_mul_right _ _)
  rw [OFF_eq]
  refine dvd_offL _ (fun Y hY => ?_) X
  unfold Arr.nFeat
  exact Dvd.dvd.mul_left (hD.blk Y (by rw [mx_of_mem _ Y hY]; exact hX)) _

omit scl in
/-- If lp ≤ r, the bits B[ι, θ, π] and the entries of the matrix b correspond one to one. -/
theorem addrBBij : Spec.addrBBij := by
  intro D _
  have hr : 0 < 2 ^ D.r := Nat.two_pow_pos _
  have hl : 0 < 2 ^ D.lp := Nat.two_pow_pos _
  constructor
  · intro ι hι θ hθ π hπ
    refine ⟨Nat.mod_lt _ hr, ?_⟩
    show ((θ * 2 ^ D.r + ι) * 2 ^ D.lp + π) / 2 ^ D.r < NT D * 2 ^ D.lp
    rw [Nat.div_lt_iff_lt_mul hr]
    have := mr_lt (mr_lt hθ hι) hπ
    calc (θ * 2 ^ D.r + ι) * 2 ^ D.lp + π < NT D * 2 ^ D.r * 2 ^ D.lp := this
      _ = NT D * 2 ^ D.lp * 2 ^ D.r := by ring
  · intro row hrow col hcol
    have hcol' : col < NT D * 2 ^ D.lp := hcol
    have hN : col * 2 ^ D.r + row < NT D * 2 ^ D.r * 2 ^ D.lp := by
      have := mr_lt hcol' hrow
      calc col * 2 ^ D.r + row < NT D * 2 ^ D.lp * 2 ^ D.r := this
        _ = NT D * 2 ^ D.r * 2 ^ D.lp := by ring
    set N := col * 2 ^ D.r + row with hNd
    have hdec : (N / 2 ^ D.lp / 2 ^ D.r * 2 ^ D.r + N / 2 ^ D.lp % 2 ^ D.r) * 2 ^ D.lp +
          N % 2 ^ D.lp = N := by
      rw [Nat.div_add_mod' (N / 2 ^ D.lp) (2 ^ D.r), Nat.div_add_mod' N (2 ^ D.lp)]
    have hback : (N % 2 ^ D.r, N / 2 ^ D.r) = (row, col) := by
      rw [hNd, Nat.mul_comm col, Nat.mul_add_mod, Nat.mod_eq_of_lt hrow, Nat.mul_add_div hr,
        Nat.div_eq_of_lt hrow, Nat.add_zero]
    refine ⟨(N / 2 ^ D.lp % 2 ^ D.r, N / 2 ^ D.lp / 2 ^ D.r, N % 2 ^ D.lp),
      ⟨Nat.mod_lt _ hr, ?_, Nat.mod_lt _ hl, ?_⟩,
      ?_⟩
    · show N / 2 ^ D.lp / 2 ^ D.r < NT D
      rw [Nat.div_lt_iff_lt_mul hr, Nat.div_lt_iff_lt_mul hl]
      exact hN
    · show addrB D _ _ _ = _
      unfold addrB
      rw [hdec]
      exact hback
    · rintro ⟨ι, θ, π⟩ ⟨h1, _, h3, h4⟩
      simp only at h1 h3 h4
      unfold addrB at h4
      obtain ⟨e1, e2⟩ := Prod.mk.inj h4
      have eN : (θ * 2 ^ D.r + ι) * 2 ^ D.lp + π = N := by
        rw [← Nat.div_add_mod' ((θ * 2 ^ D.r + ι) * 2 ^ D.lp + π) (2 ^ D.r), e1, e2]
      rw [← hdec] at eN
      obtain ⟨e3, e4⟩ := mr_inj h3 (Nat.mod_lt _ hl) eN
      obtain ⟨e5, e6⟩ := mr_inj h1 (Nat.mod_lt _ hr) e3
      rw [e4, e5, e6]

/-! ## 5. The padding positions of a batch -/

omit scl in
theorem sum_range_mul (f : ℕ → ℕ) (A B : ℕ) :
    ∑ X ∈ range (A * B), f X = ∑ u ∈ range A, ∑ v ∈ range B, f (u * B + v) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

omit scl in
theorem foldl_min_le {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (a : ℕ),
      l.foldl (fun m c => min m (f c)) a ≤ a ∧ ∀ c ∈ l, l.foldl (fun m c => min m (f c)) a ≤ f c
  | [], a => ⟨le_rfl, fun c hc => absurd hc (List.not_mem_nil)⟩
  | b :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_min_le f l (min a (f b))
    rw [List.foldl_cons]
    refine ⟨le_trans h1 (min_le_left _ _), fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact le_trans h1 (min_le_right _ _)
    · exact h2 c hc'

omit scl in
theorem Dk_le (c : Fin 8) : Dk D ≤ aC D c :=
  (foldl_min_le (aC D) (List.finRange 8) D.cap).2 c (List.mem_finRange c)

omit scl in
/-- Under `Dim.OK`, a batch holds whole layers: 2^D = (layers in a batch) · J_c · T. Here D is the
number `Dk D`, not the record of sizes; the layers in a batch are `layersIn D c`, and J_c is
2^(`lJ D c`). -/
theorem two_pow_Dk (hD : D.OK) (c : Fin 8) : 2 ^ Dk D = layersIn D c * 2 ^ lJ D c * D.T := by
  have h1 := Dk_le D c
  have h2 := hD.whole c
  have e : aC D c = D.lL + lJ D c + D.lT := rfl
  have e1 : layersIn D c = 2 ^ D.lL / 2 ^ (aC D c - Dk D) := rfl
  have e2 : D.T = 2 ^ D.lT := rfl
  rw [e1, e2]
  generalize Dk D = k at *
  generalize aC D c = a at *
  generalize lJ D c = j at *
  generalize D.lL = lL at *
  generalize D.lT = lT at *
  subst e
  rw [Nat.pow_div (by omega) (by norm_num), ← pow_add, ← pow_add]
  exact congrArg (2 ^ ·) (by omega)

omit scl in
theorem used_le (c : Fin 8) : used D c ≤ 2 ^ lJ D c := Nat.le_pow_clog (by norm_num) _

omit scl in
theorem pos_lt {s : Fam} {x : ℕ} (hx : x < len D s) : pos D s x < 2 ^ lJ D (call s) :=
  lt_of_lt_of_le ((posRange D (call s) (pos D s x)).mpr ⟨s, mem_fams_call s, x, hx, rfl⟩)
    (used_le D (call s))

omit scl in
/-- a column is not padding in a layer if and only if an index of a family that is present there
takes it -/
theorem not_isPad_iff (c : Fin 8) (l jj : ℕ) :
    isPad D c l jj = false ↔
    ∃ s ∈ (fams c).filter (present · l), ∃ x < len D s, pos D s x = jj := by
  unfold isPad
  cases hf : famAt D c jj with
  | none =>
    simp only [Bool.true_eq_false, false_iff]
    rintro ⟨s, hs, x, hx, hp⟩
    have := (famAtPos D c jj s x).mpr ⟨mem_fams_iff.mp (List.mem_filter.mp hs).1, hx, hp⟩
    rw [hf] at this
    exact absurd this (by simp)
  | some a =>
    obtain ⟨s, x⟩ := a
    obtain ⟨h1, h2, h3⟩ := (famAtPos D c jj s x).mp hf
    simp only [Bool.not_eq_false']
    constructor
    · intro hp
      exact ⟨s, List.mem_filter.mpr ⟨mem_fams_iff.mpr h1, hp⟩, x, h2, h3⟩
    · rintro ⟨s', hs', x', hx', hp'⟩
      have hc' := mem_fams_iff.mp (List.mem_filter.mp hs').1
      obtain ⟨e1, _⟩ := posInj D s' s x' x (hc'.trans h1.symm) hx' h2 (hp'.trans h3.symm)
      rw [← e1]
      exact (List.mem_filter.mp hs').2

omit scl in
/-- the number of columns of a call that are not padding in a layer is the sum of the lengths of the
families that are present there -/
theorem card_not_pad (c : Fin 8) (l : ℕ) :
    ((range (2 ^ lJ D c)).filter fun jj => isPad D c l jj = false).card = usedIn D c l := by
  have hset : ((range (2 ^ lJ D c)).filter fun jj => isPad D c l jj = false) =
      ((fams c).filter (present · l)).toFinset.biUnion fun s =>
        (range (len D s)).image (pos D s) := by
    ext jj
    rw [mem_filter, mem_range, not_isPad_iff, mem_biUnion]
    constructor
    · rintro ⟨_, s, hs, x, hx, hp⟩
      exact ⟨s, List.mem_toFinset.mpr hs, mem_image.mpr ⟨x, mem_range.mpr hx, hp⟩⟩
    · rintro ⟨s, hs, hj⟩
      obtain ⟨x, hx, hp⟩ := mem_image.mp hj
      have hs' := List.mem_toFinset.mp hs
      have hc := mem_fams_iff.mp (List.mem_filter.mp hs').1
      refine ⟨?_, s, hs', x, mem_range.mp hx, hp⟩
      rw [← hp, ← hc]
      exact pos_lt D (mem_range.mp hx)
  rw [hset, card_biUnion]
  · unfold usedIn
    rw [← List.sum_toFinset _ ((fams_nodup c).filter _)]
    refine sum_congr rfl fun s _ => ?_
    rw [card_image_of_injOn, card_range]
    intro x hx x' hx' h
    exact (posInj D s s x x' rfl (mem_range.mp (mem_coe.mp hx)) (mem_range.mp (mem_coe.mp hx')) h).2
  · intro s hs s' hs' hne
    refine disjoint_left.mpr fun jj h1 h2 => hne ?_
    obtain ⟨x, hx, hp⟩ := mem_image.mp h1
    obtain ⟨x', hx', hp'⟩ := mem_image.mp h2
    have hc := mem_fams_iff.mp (List.mem_filter.mp (List.mem_toFinset.mp hs)).1
    have hc' := mem_fams_iff.mp (List.mem_filter.mp (List.mem_toFinset.mp hs')).1
    exact (posInj D s s' x x' (hc.trans hc'.symm) (mem_range.mp hx)
      (mem_range.mp hx') (hp.trans hp'.symm)).1

omit scl in
theorem card_pad (c : Fin 8) (l : ℕ) :
    ((range (2 ^ lJ D c)).filter fun jj => isPad D c l jj = true).card =
      2 ^ lJ D c - usedIn D c l := by
  have h :=
    card_filter_add_card_filter_not (s := range (2 ^ lJ D c)) (fun jj => isPad D c l jj = true)
  have e : ((range (2 ^ lJ D c)).filter fun jj => ¬ isPad D c l jj = true) =
      (range (2 ^ lJ D c)).filter fun jj => isPad D c l jj = false := by
    refine filter_congr fun jj _ => ?_
    simp
  rw [e, card_not_pad, card_range] at h
  omega

omit scl in
/-- Under `Dim.OK`, ϕ_θ counts the padding positions of a batch θ < N_T. -/
theorem padCountEq : Spec.padCountEq := by
  intro D hD θ _
  set c := callOf D θ with hc
  set t := θ - firstTree D c with ht
  have hK := two_pow_Dk D hD c
  have hT := T_pos D
  have hJ : 0 < 2 ^ lJ D c := Nat.two_pow_pos _
  rw [card_filter, hK, sum_range_mul]
  rw [sum_range_mul]
  show ∑ u ∈ range (layersIn D c), (2 ^ lJ D c - usedIn D c (t * layersIn D c + u)) * D.T = _
  refine sum_congr rfl fun u _ => ?_
  rw [← card_pad, card_filter, sum_mul]
  refine sum_congr rfl fun jj hjj => ?_
  have hjj' := mem_range.mp hjj
  have key : ∀ i < D.T,
      (t * (layersIn D c * 2 ^ lJ D c * D.T) + ((u * 2 ^ lJ D c + jj) * D.T + i)) / D.T =
        (t * layersIn D c + u) * 2 ^ lJ D c + jj := fun i hi => by
    have e : t * (layersIn D c * 2 ^ lJ D c * D.T) + ((u * 2 ^ lJ D c + jj) * D.T + i) =
        D.T * ((t * layersIn D c + u) * 2 ^ lJ D c + jj) + i := by ring
    rw [e, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have k1 : ((t * layersIn D c + u) * 2 ^ lJ D c + jj) / 2 ^ lJ D c = t * layersIn D c + u := by
    rw [Nat.mul_comm, Nat.mul_add_div hJ, Nat.div_eq_of_lt hjj', Nat.add_zero]
  have k2 : ((t * layersIn D c + u) * 2 ^ lJ D c + jj) % 2 ^ lJ D c = jj := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjj']
  rw [sum_congr rfl (fun i hi => by
      rw [key i (mem_range.mp hi), k1, k2] : ∀ i ∈ range D.T,
        (if isPad D c ((t * (layersIn D c * 2 ^ lJ D c * D.T) + ((u * 2 ^ lJ D c + jj) * D.T + i)) /
                    D.T / 2 ^ lJ D c)
                  ((t * (layersIn D c * 2 ^ lJ D c * D.T) + ((u * 2 ^ lJ D c + jj) * D.T + i)) /
                    D.T % 2 ^ lJ D c) = true then 1
            else 0) =
          if isPad D c (t * layersIn D c + u) jj = true then 1 else 0)]
  rw [sum_const, card_range, smul_eq_mul, Nat.mul_comm]

/-! ## 6. The key vector of a call -/

/-- Under the hypotheses of its statement, the key vector of a call holds the keys at the columns of
the index map. -/
theorem keyVecAt : Spec.keyVecAt := by
  intro R _ D t tb L0 w s l x i hx hi hp
  have hT := T_pos D
  have hJ : 0 < 2 ^ lJ D (call s) := Nat.two_pow_pos _
  have hpos := pos_lt D hx
  have e1 : keyIdx D (call s) l (pos D s x) i / D.T = l * 2 ^ lJ D (call s) + pos D s x := by
    unfold keyIdx
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : keyIdx D (call s) l (pos D s x) i % D.T = i := by
    unfold keyIdx
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have e3 : (l * 2 ^ lJ D (call s) + pos D s x) / 2 ^ lJ D (call s) = l := by
    rw [Nat.mul_comm, Nat.mul_add_div hJ, Nat.div_eq_of_lt hpos, Nat.add_zero]
  have e4 : (l * 2 ^ lJ D (call s) + pos D s x) % 2 ^ lJ D (call s) = pos D s x := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hpos]
  have e5 : famAt D (call s) (pos D s x) = some (s, x) :=
    (famAtPos D (call s) (pos D s x) s x).mpr ⟨rfl, hx, rfl⟩
  unfold keyVec
  rw [e1, e2, e3, e4, e5]
  simp only
  rw [if_pos hp]

end Inst.Model.FFSeg.IndexFacts
