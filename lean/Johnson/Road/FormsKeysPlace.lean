-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysPlace.lean: the rule that places a lookup call's segments in columns puts
every segment on whole blocks.

Johnson/Road/FormsKeysEq.lean shows that the weights of a segment's entries and of its blocks are
one set of weights if the segment's columns are aligned on blocks of 2^ls entries (Aligned). This
file shows that the placing rule (place in OnBytes/Model/Calls.lean) gives such columns to every
segment whose length is a multiple of 2^ls and is below 2^(topBit + 1).

The way. The rule cuts each length into powers of two and lays the pieces by falling size. So each
piece begins at a multiple of its own size (piecesBelow_spec). The pieces of one segment are the set
bits of its length, from the top down, once each (exps_piecesBelow), so their sizes add up to the
length and nothing is filled in (bitsBelow_sum). A length that 2^ls divides has no bit below ls
(le_of_testBit), so each of its pieces is a whole number of blocks and begins at a multiple of 2^ls.
Runs of that kind, one after another, are aligned (OnBlocks.append, onBlocks_fold).

Main definitions: bitsBelow, run, layStep, OnBlocks.
Main theorems: piecesBelow_spec, exps_piecesBelow, columnsOf_onBlocks, place_aligned,
place_aligned_all.

What is not claimed. Nothing is said of a length with a bit above topBit, of two segments' columns
being apart, of the array used, or of which calls a verifier admits. The program does not import
this file.

-/
import Johnson.Road.FormsKeysEq

set_option autoImplicit false

namespace OnBytes.Road

open OnBytes.Model (Seg CallD SegAsk topBit piecesOfSize piecesBelow columnsOf place)

/-! ## Bits -/

/-- The lowest k + 1 bits of a number are bit k and the lowest k bits. -/
theorem mod_two_pow_succ (n k : ℕ) :
    n % 2 ^ (k + 1) = (if n.testBit k = true then 2 ^ k else 0) + n % 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h, Nat.add_comm]

/-- A multiple of 2^ls has no bit below ls. -/
theorem le_of_testBit {ls n b : ℕ} (hd : 2 ^ ls ∣ n) (hb : n.testBit b = true) : ls ≤ b := by
  by_contra hc
  obtain ⟨d, rfl⟩ : ∃ d, ls = b + 1 + d := ⟨ls - b - 1, by omega⟩
  obtain ⟨q, rfl⟩ := hd
  have hpos : 0 < 2 ^ b := by positivity
  have e : 2 ^ (b + 1 + d) * q = 2 ^ b * (2 * (2 ^ d * q)) := by ring
  rw [Nat.testBit_eq_decide_div_mod_eq, e, Nat.mul_div_cancel_left _ hpos] at hb
  simp at hb

/-- The set bits of n below k, from the top down. -/
def bitsBelow (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => (if n.testBit k = true then [k] else []) ++ bitsBelow n k

/-- Every member of the list is a set bit. -/
theorem bitsBelow_testBit (n : ℕ) : ∀ (k b : ℕ), b ∈ bitsBelow n k → n.testBit b = true
  | 0, b, h => by simp [bitsBelow] at h
  | k + 1, b, h => by
    rw [bitsBelow] at h
    rcases List.mem_append.mp h with h | h
    · cases hk : n.testBit k with
      | true =>
        have e : b = k := by simpa [hk] using h
        rw [e]
        exact hk
      | false => simp [hk] at h
    · exact bitsBelow_testBit n k b h

/-- The powers of two of the set bits below k add up to the number's lowest k bits. -/
theorem bitsBelow_sum (n : ℕ) : ∀ k : ℕ, ((bitsBelow n k).map fun b => 2 ^ b).sum = n % 2 ^ k
  | 0 => by simp [bitsBelow, Nat.mod_one]
  | k + 1 => by
    rw [bitsBelow, List.map_append, List.sum_append, bitsBelow_sum n k, mod_two_pow_succ]
    cases hk : n.testBit k <;> simp

/-- n is at most 2^(ceilLog2 n). -/
theorem le_two_pow_ceilLog2 (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split_ifs with h
  · simpa using h
  · have h1 : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

/-! ## Two facts on multiples -/

/-- Inside a block: if block x begins before the end of m blocks, all of it lies before that end. -/
theorem block_lt {P x m r : ℕ} (h : P * x < P * m) (hr : r < P) : P * x + r < P * m := by
  have h1 : x + 1 ≤ m := by
    by_contra hc
    have h2 : P * m ≤ P * x := Nat.mul_le_mul_left P (by omega)
    omega
  have h3 : P * (x + 1) ≤ P * m := Nat.mul_le_mul_left P h1
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

/-- Block x of the n / P whole blocks of n entries begins before entry n. -/
theorem mul_lt_of_lt_div {P n x : ℕ} (h : x < n / P) : P * x < n := by
  have h1 : P * (x + 1) ≤ P * (n / P) := Nat.mul_le_mul_left P h
  have h2 : P * (n / P) ≤ n := Nat.mul_div_le n P
  have hP : 0 < P := by
    rcases Nat.eq_zero_or_pos P with e | e
    · subst e
      simp at h
    · exact e
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

/-! ## The pieces of one size -/

/-- The pieces of size 2^b if the first length has bit b. -/
theorem piecesOfSize_cons_true {b n : ℕ} (h : n.testBit b = true) (ns : List ℕ) (s off : ℕ) :
    piecesOfSize b (n :: ns) s off =
      ((s, b, off) :: (piecesOfSize b ns (s + 1) (off + 2 ^ b)).1,
        (piecesOfSize b ns (s + 1) (off + 2 ^ b)).2) := by
  simp [piecesOfSize, h]

/-- The pieces of size 2^b if the first length does not have bit b. -/
theorem piecesOfSize_cons_false {b n : ℕ} (h : n.testBit b = false) (ns : List ℕ) (s off : ℕ) :
    piecesOfSize b (n :: ns) s off = piecesOfSize b ns (s + 1) off := by
  simp [piecesOfSize, h]

/-- From a first free column that 2^b divides: the new first free column is no smaller and 2^b
divides it; every piece has the exponent b, begins at a multiple of 2^b and ends before the new
first free column. -/
theorem piecesOfSize_spec (b : ℕ) : ∀ (ns : List ℕ) (s off : ℕ), 2 ^ b ∣ off →
    off ≤ (piecesOfSize b ns s off).2 ∧ 2 ^ b ∣ (piecesOfSize b ns s off).2 ∧
      ∀ p ∈ (piecesOfSize b ns s off).1,
        p.2.1 = b ∧ 2 ^ b ∣ p.2.2 ∧ p.2.2 + 2 ^ b ≤ (piecesOfSize b ns s off).2
  | [], _, _, h => ⟨Nat.le_refl _, h, fun p hp => by simp [piecesOfSize] at hp⟩
  | n :: ns, s, off, h => by
    cases hb : n.testBit b with
    | true =>
      obtain ⟨h1, h2, h3⟩ :=
        piecesOfSize_spec b ns (s + 1) (off + 2 ^ b) (Nat.dvd_add h (Nat.dvd_refl _))
      rw [piecesOfSize_cons_true hb]
      refine ⟨Nat.le_trans (Nat.le_add_right _ _) h1, h2, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with e | hp
      · subst e
        exact ⟨rfl, h, h1⟩
      · exact h3 p hp
    | false =>
      rw [piecesOfSize_cons_false hb]
      exact piecesOfSize_spec b ns (s + 1) off h

/-- A segment whose number is below that of the list's first segment gets no piece. -/
theorem filter_piecesOfSize_lt (b s : ℕ) : ∀ (ns : List ℕ) (s0 off : ℕ), s < s0 →
    ((piecesOfSize b ns s0 off).1.filter fun p => p.1 == s) = []
  | [], _, _, _ => by simp [piecesOfSize]
  | n :: ns, s0, off, h => by
    have ih := fun off' => filter_piecesOfSize_lt b s ns (s0 + 1) off' (by omega)
    have hne : s0 ≠ s := by omega
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show List.filter (fun p => p.1 == s)
        ((s0, b, off) :: (piecesOfSize b ns (s0 + 1) (off + 2 ^ b)).1) = []
      rw [List.filter_cons_of_neg (by simpa using hne)]
      exact ih _
    | false =>
      rw [piecesOfSize_cons_false hb]
      exact ih _

/-- The exponents of the pieces of size 2^b that member number d of the list gets: b if its length
has bit b, none otherwise. -/
theorem exps_piecesOfSize (b : ℕ) : ∀ (ns : List ℕ) (s0 d off : ℕ),
    (((piecesOfSize b ns s0 off).1.filter fun p => p.1 == s0 + d).map fun p => p.2.1) =
      if (ns.getD d 0).testBit b = true then [b] else []
  | [], _, _, _ => by simp [piecesOfSize]
  | n :: ns, s0, 0, off => by
    have ih := fun off' => filter_piecesOfSize_lt b s0 ns (s0 + 1) off' (Nat.lt_succ_self _)
    rw [Nat.add_zero]
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show List.map (fun p => p.2.1) (List.filter (fun p => p.1 == s0)
        ((s0, b, off) :: (piecesOfSize b ns (s0 + 1) (off + 2 ^ b)).1)) = _
      rw [List.filter_cons_of_pos (by simp), ih]
      simp [hb]
    | false =>
      rw [piecesOfSize_cons_false hb, ih]
      simp [hb]
  | n :: ns, s0, d + 1, off => by
    have ih := fun off' => exps_piecesOfSize b ns (s0 + 1) d off'
    have e : s0 + (d + 1) = s0 + 1 + d := by omega
    have hne : s0 ≠ s0 + 1 + d := by omega
    rw [e, List.getD_cons_succ]
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show List.map (fun p => p.2.1) (List.filter (fun p => p.1 == s0 + 1 + d)
        ((s0, b, off) :: (piecesOfSize b ns (s0 + 1) (off + 2 ^ b)).1)) = _
      rw [List.filter_cons_of_neg (by simpa using hne)]
      exact ih _
    | false =>
      rw [piecesOfSize_cons_false hb]
      exact ih _

/-! ## All pieces -/

/-- The pieces of sizes 2^k down to 1: those of size 2^k, then the smaller ones. -/
theorem piecesBelow_succ (lengths : List ℕ) (k off : ℕ) :
    piecesBelow lengths (k + 1) off =
      ((piecesOfSize k lengths 0 off).1 ++
          (piecesBelow lengths k (piecesOfSize k lengths 0 off).2).1,
        (piecesBelow lengths k (piecesOfSize k lengths 0 off).2).2) := rfl

/-- From a first free column that 2^k divides: every piece begins at a multiple of its own size and
ends before the new first free column, which is no smaller than the old one. -/
theorem piecesBelow_spec (lengths : List ℕ) : ∀ (k off : ℕ), 2 ^ k ∣ off →
    off ≤ (piecesBelow lengths k off).2 ∧
      ∀ p ∈ (piecesBelow lengths k off).1,
        2 ^ p.2.1 ∣ p.2.2 ∧ p.2.2 + 2 ^ p.2.1 ≤ (piecesBelow lengths k off).2
  | 0, _, _ => ⟨Nat.le_refl _, fun p hp => by simp [piecesBelow] at hp⟩
  | k + 1, off, h => by
    have hk : 2 ^ k ∣ off := Nat.dvd_trans (pow_dvd_pow 2 (Nat.le_succ k)) h
    obtain ⟨a1, a2, a3⟩ := piecesOfSize_spec k lengths 0 off hk
    obtain ⟨r1, r2⟩ := piecesBelow_spec lengths k _ a2
    rw [piecesBelow_succ]
    refine ⟨Nat.le_trans a1 r1, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨e, dv, le⟩ := a3 p hp
      rw [e]
      exact ⟨dv, Nat.le_trans le r1⟩
    · exact r2 p hp

/-- The exponents of the pieces of segment number s, in the order of the list: the set bits of its
length below k, from the top down. -/
theorem exps_piecesBelow (lengths : List ℕ) (s : ℕ) : ∀ (k off : ℕ),
    (((piecesBelow lengths k off).1.filter fun p => p.1 == s).map fun p => p.2.1) =
      bitsBelow (lengths.getD s 0) k
  | 0, _ => by simp [piecesBelow, bitsBelow]
  | k + 1, off => by
    have h1 := exps_piecesOfSize k lengths 0 s off
    rw [Nat.zero_add] at h1
    rw [piecesBelow_succ]
    show List.map (fun p => p.2.1) (List.filter (fun p => p.1 == s)
      ((piecesOfSize k lengths 0 off).1 ++
        (piecesBelow lengths k (piecesOfSize k lengths 0 off).2).1)) = _
    rw [List.filter_append, List.map_append, h1, exps_piecesBelow lengths s k, bitsBelow]

/-! ## Runs of columns, one after another -/

/-- The 2^b neighbouring columns from off on. -/
def run (b off : ℕ) : Array ℕ := (Array.range (2 ^ b)).map (· + off)

/-- One step of the laying: the columns of piece p are appended. -/
def layStep (a : Array ℕ) (p : ℕ × ℕ × ℕ) : Array ℕ := a ++ run p.2.1 p.2.2

/-- What columnsOf is, in these words. -/
theorem columnsOf_eq (pieces : List (ℕ × ℕ × ℕ)) (s n : ℕ) :
    columnsOf pieces s n = (pieces.filter fun p => p.1 == s).foldl layStep #[] ++
      Array.replicate (n - ((pieces.filter fun p => p.1 == s).foldl layStep #[]).size) 0 := rfl

/-- A run has 2^b columns. -/
theorem size_append_run (a : Array ℕ) (b off : ℕ) : (a ++ run b off).size = a.size + 2 ^ b := by
  simp [run]

/-- Before the appended run the array is as it was. -/
theorem getD_run_left (a : Array ℕ) (b off : ℕ) {x : ℕ} (h : x < a.size) :
    (a ++ run b off).getD x 0 = a.getD x 0 := by
  have h' : x < a.size + 2 ^ b := Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  simp [run, Array.getD, h, h']

/-- Entry y of the appended run is the column off + y. -/
theorem getD_run_right (a : Array ℕ) (b off : ℕ) {y : ℕ} (h : y < 2 ^ b) :
    (a ++ run b off).getD (a.size + y) 0 = y + off := by
  simp [run, Array.getD, h]

/-- An array of columns that is aligned on blocks of 2^ls entries, with all columns below B: it is a
whole number of blocks, and the entries of each block lie in neighbouring columns from a multiple of
2^ls on. -/
structure OnBlocks (a : Array ℕ) (ls B : ℕ) : Prop where
  /-- a whole number of blocks -/
  whole : 2 ^ ls ∣ a.size
  /-- the columns of block xh -/
  block : ∀ xh, 2 ^ ls * xh < a.size →
    ∃ Q, ∀ r, r < 2 ^ ls → a.getD (2 ^ ls * xh + r) 0 = 2 ^ ls * Q + r
  /-- every column is below B -/
  inside : ∀ x, x < a.size → a.getD x 0 < B

/-- The empty array is aligned. -/
theorem onBlocks_empty (ls B : ℕ) : OnBlocks #[] ls B :=
  ⟨by simp, fun xh h => by simp at h, fun x h => by simp at h⟩

/-- An aligned array stays aligned if a run is appended that has at least 2^ls columns, begins at a
multiple of 2^ls and ends at or before B. -/
theorem OnBlocks.append {a : Array ℕ} {ls B : ℕ} (A : OnBlocks a ls B) {b off : ℕ} (hb : ls ≤ b)
    (hoff : 2 ^ ls ∣ off) (hB : off + 2 ^ b ≤ B) : OnBlocks (a ++ run b off) ls B := by
  obtain ⟨A0, hA⟩ := A.whole
  obtain ⟨O, hO⟩ := hoff
  obtain ⟨M, hM⟩ : 2 ^ ls ∣ 2 ^ b := pow_dvd_pow 2 hb
  have hpos : 0 < 2 ^ ls := by positivity
  have hsz := size_append_run a b off
  refine ⟨?_, ?_, ?_⟩
  · rw [hsz]
    exact Nat.dvd_add A.whole (pow_dvd_pow 2 hb)
  · intro xh hx
    rw [hsz] at hx
    by_cases h : 2 ^ ls * xh < a.size
    · obtain ⟨Q, hQ⟩ := A.block xh h
      refine ⟨Q, fun r hr => ?_⟩
      have hlt : 2 ^ ls * xh + r < a.size := by
        rw [hA] at h ⊢
        exact block_lt h hr
      rw [getD_run_left a b off hlt, hQ r hr]
    · have hle : A0 ≤ xh := by
        by_contra hc
        have h2 : 2 ^ ls * (xh + 1) ≤ 2 ^ ls * A0 := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at h2
        omega
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨d + O, fun r hr => ?_⟩
      rw [Nat.mul_add] at hx
      have hd : 2 ^ ls * d < 2 ^ ls * M := by omega
      have hy : 2 ^ ls * d + r < 2 ^ b := by
        rw [hM]
        exact block_lt hd hr
      have e : 2 ^ ls * (A0 + d) + r = a.size + (2 ^ ls * d + r) := by
        rw [hA, Nat.mul_add]
        omega
      rw [e, getD_run_right a b off hy, hO, Nat.mul_add]
      omega
  · intro x hx
    rw [hsz] at hx
    by_cases h : x < a.size
    · rw [getD_run_left a b off h]
      exact A.inside x h
    · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
      have hy : y < 2 ^ b := by omega
      rw [getD_run_right a b off hy]
      omega

/-- Laying a list of pieces, each of at least 2^ls columns, from a multiple of 2^ls on and ending at
or before B, keeps an array aligned and adds the pieces' sizes to its length. -/
theorem onBlocks_fold (ls B : ℕ) : ∀ (ps : List (ℕ × ℕ × ℕ)) (a : Array ℕ), OnBlocks a ls B →
    (∀ p ∈ ps, ls ≤ p.2.1 ∧ 2 ^ ls ∣ p.2.2 ∧ p.2.2 + 2 ^ p.2.1 ≤ B) →
    OnBlocks (ps.foldl layStep a) ls B ∧
      (ps.foldl layStep a).size = a.size + ((ps.map fun p => p.2.1).map fun b => 2 ^ b).sum
  | [], a, A, _ => ⟨A, by simp⟩
  | p :: ps, a, A, h => by
    obtain ⟨h1, h2, h3⟩ := h p List.mem_cons_self
    obtain ⟨r1, r2⟩ := onBlocks_fold ls B ps (layStep a p) (A.append h1 h2 h3)
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rw [List.foldl_cons]
    refine ⟨r1, ?_⟩
    have e : (layStep a p).size = a.size + 2 ^ p.2.1 := size_append_run a p.2.1 p.2.2
    rw [r2, e, List.map_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- If the laid columns are as many as the segment's entries, nothing is filled in. -/
theorem fill_none {X : Array ℕ} {n : ℕ} (h : X.size = n) :
    X ++ Array.replicate (n - X.size) 0 = X := by
  rw [h, Nat.sub_self]
  simp

/-! ## The columns of one segment -/

/-- The columns of segment number s, from the pieces of sizes below 2^k: if 2^ls divides the
segment's length and the length is below 2^k, there is one column for each entry, and the columns
are aligned on blocks of 2^ls entries and lie below the first free column. -/
theorem columnsOf_onBlocks (lengths : List ℕ) (s ls k : ℕ) (hd : 2 ^ ls ∣ lengths.getD s 0)
    (hlt : lengths.getD s 0 < 2 ^ k) :
    (columnsOf (piecesBelow lengths k 0).1 s (lengths.getD s 0)).size = lengths.getD s 0 ∧
      OnBlocks (columnsOf (piecesBelow lengths k 0).1 s (lengths.getD s 0)) ls
        (piecesBelow lengths k 0).2 := by
  obtain ⟨_, hsp⟩ := piecesBelow_spec lengths k 0 (Nat.dvd_zero _)
  have hex := exps_piecesBelow lengths s k 0
  have hgood : ∀ p ∈ (piecesBelow lengths k 0).1.filter (fun p => p.1 == s),
      ls ≤ p.2.1 ∧ 2 ^ ls ∣ p.2.2 ∧ p.2.2 + 2 ^ p.2.1 ≤ (piecesBelow lengths k 0).2 := by
    intro p hp
    obtain ⟨g1, g2⟩ := hsp p (List.mem_of_mem_filter hp)
    have hb : p.2.1 ∈ bitsBelow (lengths.getD s 0) k := by
      rw [← hex]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hle := le_of_testBit hd (bitsBelow_testBit _ _ _ hb)
    exact ⟨hle, Nat.dvd_trans (pow_dvd_pow 2 hle) g1, g2⟩
  obtain ⟨L, hs⟩ := onBlocks_fold ls _ _ #[] (onBlocks_empty ls _) hgood
  rw [hex, bitsBelow_sum, Nat.mod_eq_of_lt hlt] at hs
  have hs' : (((piecesBelow lengths k 0).1.filter fun p => p.1 == s).foldl layStep #[]).size =
      lengths.getD s 0 := by simpa using hs
  rw [columnsOf_eq, fill_none hs']
  exact ⟨hs', L⟩

/-- A segment whose array of columns is aligned, with one column for each entry and all columns
below 2^lJ, is aligned in the sense of Johnson/Road/FormsKeysEq.lean. -/
theorem aligned_of_onBlocks {s : Seg} {ls lJ B : ℕ} (hsz : s.pos.size = s.n)
    (L : OnBlocks s.pos ls B) (hB : B ≤ 2 ^ lJ) : Aligned s ls lJ := by
  have hpos : 0 < 2 ^ ls := by positivity
  refine ⟨hsz, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := L.whole
    exact ⟨q, by rw [← hsz, hq, Nat.mul_comm]⟩
  · intro xh r hx hr
    obtain ⟨Q, hQ⟩ := L.block xh (by rw [hsz]; exact mul_lt_of_lt_div hx)
    have h0 := hQ 0 hpos
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [hQ r hr, h0]
  · intro xh hx
    obtain ⟨Q, hQ⟩ := L.block xh (by rw [hsz]; exact mul_lt_of_lt_div hx)
    have h0 := hQ 0 hpos
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [h0]
    exact Nat.dvd_mul_right _ _
  · intro x hx
    exact Nat.lt_of_lt_of_le (L.inside x (by rw [hsz]; exact hx)) hB

/-! ## The placing rule -/

/-- A member of a list with its number, counted from k on: it is a member, and the list of the
members' images under f has its image at that number. -/
theorem mem_zipIdx_getD {α : Type} (f : α → ℕ) : ∀ (l : List α) (k : ℕ) (a : α) (i : ℕ),
    (a, i) ∈ l.zipIdx k → a ∈ l ∧ k ≤ i ∧ (l.map f).getD (i - k) 0 = f a
  | [], _, _, _, h => by simp at h
  | x :: l, k, a, i, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.mp h with e | h
    · cases e
      simp
    · obtain ⟨h1, h2, h3⟩ := mem_zipIdx_getD f l (k + 1) a i h
      refine ⟨List.mem_cons_of_mem _ h1, by omega, ?_⟩
      have e : i - k = i - (k + 1) + 1 := by omega
      rw [e, List.map_cons, List.getD_cons_succ]
      exact h3

/-- The placing rule aligns a segment on blocks of 2^ls entries if 2^ls divides the segment's length
and the length is below 2^(topBit + 1). -/
theorem place_aligned (name kind : String) (asks : List SegAsk) (floorLg ls : ℕ) (s : Seg)
    (hs : s ∈ (place name kind asks floorLg).segs) (hd : 2 ^ ls ∣ s.n)
    (hlt : s.n < 2 ^ (topBit + 1)) : Aligned s ls (place name kind asks floorLg).lJ := by
  have hs' : s ∈ asks.zipIdx.map fun x =>
      ({ name := x.1.1, n := x.1.2.1,
         pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
         moe := x.1.2.2 } : Seg) := hs
  obtain ⟨⟨a, i⟩, hx, rfl⟩ := List.mem_map.mp hs'
  obtain ⟨_, _, hn⟩ := mem_zipIdx_getD (fun x : SegAsk => x.2.1) asks 0 a i hx
  rw [Nat.sub_zero] at hn
  have hd' : 2 ^ ls ∣ (asks.map (·.2.1)).getD i 0 := by rw [hn]; exact hd
  have hlt' : (asks.map (·.2.1)).getD i 0 < 2 ^ (topBit + 1) := by rw [hn]; exact hlt
  obtain ⟨c1, c2⟩ := columnsOf_onBlocks (asks.map (·.2.1)) i ls (topBit + 1) hd' hlt'
  rw [hn] at c1 c2
  refine aligned_of_onBlocks c1 c2 ?_
  show (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤
    2 ^ max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) floorLg
  exact Nat.le_trans (le_two_pow_ceilLog2 _)
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))

/-- The same if every length of the call is below 2^(topBit + 1). -/
theorem place_aligned_all (name kind : String) (asks : List SegAsk) (floorLg ls : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) (s : Seg)
    (hs : s ∈ (place name kind asks floorLg).segs) (hd : 2 ^ ls ∣ s.n) :
    Aligned s ls (place name kind asks floorLg).lJ := by
  refine place_aligned name kind asks floorLg ls s hs hd ?_
  have hs' : s ∈ asks.zipIdx.map fun x =>
      ({ name := x.1.1, n := x.1.2.1,
         pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
         moe := x.1.2.2 } : Seg) := hs
  obtain ⟨⟨a, i⟩, hx, rfl⟩ := List.mem_map.mp hs'
  exact hlen a (mem_zipIdx_getD (fun x : SegAsk => x.2.1) asks 0 a i hx).1

#print axioms place_aligned
#print axioms place_aligned_all

end OnBytes.Road
