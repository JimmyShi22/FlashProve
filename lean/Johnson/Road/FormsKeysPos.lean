-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPos.lean: for a lookup call whose segments have the lengths of the families of
one of the library's calls, in the library's order, each below 2^(topBit + 1): the verifier's rule
that places the segments in columns gives every entry the column that the library's index map gives
it, and the logarithm of the verifier's number of columns is the larger of the library's and the
verifier's minimum.

The verifier's rule is an algorithm (place in OnBytes/Model/Calls.lean): it cuts every length into
powers of two, walks the exponents from the top down and the segments in order, and hands out
columns one piece after another. The library's rule is a formula (pos, colBase, lJ in
Inst/Model/FF/Index.lean): a piece begins at the sum of the sizes of all pieces that are larger, or
as large and of an earlier family.

The way. The formula is first written for a plain list of lengths (colL). The pieces that the
algorithm makes for one segment are found with their first columns (filter_piecesOfSize,
filter_piecesBelow). Laying them one after another puts the piece of exponent b at the entries from
pieceStart n b on (fold_bits, columnsOf_piece). That gives place_pos: the verifier's algorithm
against colL. colBase_colL sets the library's colBase against colL at the lengths of a call's
families. pos_eq joins the two.

What is compared with what.
  place_pos       the verifier's place with colL, a formula of this file
  colBase_colL    the library's colBase with colL
  pos_eq          the verifier's place with the library's pos
  pos_eq_segs     the same, for the members of the verifier's list of segments
  pieces_used     the verifier's first free column with the library's used
  ceilLog2_eq_clog  the verifier's ceilLog2 with Mathlib's Nat.clog 2
  lJ_max, lJ_eq   the verifier's lJ with the library's lJ

Main definitions: colL, asksOf.
Main theorems: place_pos, colBase_colL, pos_eq, lengths_of_segs, pos_eq_segs, pieces_used,
ceilLog2_eq_clog, lJ_max, lJ_eq.

The hypotheses of pos_eq, pieces_used, lJ_max and lJ_eq: the lengths in the call's line are the
lengths of the families of the library's call c, in the library's order, and each is below
2^(topBit + 1). met_ref shows that both hold of the list asksOf at the library's reference sizes.
lJ_eq asks in addition that the verifier's minimum is at most the library's lJ; the minimum 0 meets
that, and a run at the end of the file shows a minimum that does not. lengths_of_segs and
pos_eq_segs ask instead of the first hypothesis for a function from segments to families; met_segs
shows that the function which reads a segment's name serves for the list asksOf, at all sizes.

What is not claimed. That a call of a layout which the verifier admits has the lengths of a call of
the library, in its order, or a minimum that is at most the library's lJ. Nothing is said of a
length with a bit above topBit, of the array used, of an entry at or past a segment's length, or of
segments' names. That two entries' columns differ is not stated. The program does not import this
file.
-/
import Johnson.Road.FormsKeysPlace
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Seg CallD SegAsk topBit piecesOfSize piecesBelow columnsOf place)
open Inst.Model.FFSeg (Dim Fam fams call ord len isExp bitOf pieceStart colBase pos used lJ)
open Inst.Model.FFSeg.IndexFacts (testBit_iff sum_bits lt_size_of_testBit isBit_bitOf isBit_split
  fams_nodup call_of_mem)

/-! ## The formula on a list of lengths -/

/-- The first column of the piece of exponent b of segment number a, for segments of the lengths ns:
the sizes of all pieces that are larger, or as large and of an earlier segment. Only exponents up to
topBit count. -/
def colL (ns : List ℕ) (a b : ℕ) : ℕ :=
  ∑ a' ∈ range ns.length, ∑ b' ∈ range (topBit + 1),
    if (ns.getD a' 0).testBit b' = true ∧ (b < b' ∨ (b' = b ∧ a' < a)) then 2 ^ b' else 0

/-- What a segment of length n, number a', adds to the first column of the piece of exponent b of
segment number a. -/
def colTerm (a b n a' : ℕ) : ℕ :=
  ∑ b' ∈ range (topBit + 1),
    if n.testBit b' = true ∧ (b < b' ∨ (b' = b ∧ a' < a)) then 2 ^ b' else 0

/-- colL is the sum of these terms. -/
theorem colL_terms (ns : List ℕ) (a b : ℕ) :
    colL ns a b = ∑ a' ∈ range ns.length, colTerm a b (ns.getD a' 0) a' := rfl

/-- The size of the piece of exponent b of a segment of length n: 2^b if n has bit b, else 0. -/
def bitW (n b : ℕ) : ℕ := if n.testBit b = true then 2 ^ b else 0

/-- The size of a piece that is there. -/
theorem bitW_true {n b : ℕ} (h : n.testBit b = true) : bitW n b = 2 ^ b := by
  rw [bitW, if_pos h]

/-- The size of a piece that is not there. -/
theorem bitW_false {n b : ℕ} (h : n.testBit b = false) : bitW n b = 0 := by
  rw [bitW, if_neg (by simp [h])]

/-- The sizes of the pieces of exponent b of segments of the lengths ns, added up. -/
def cntL (b : ℕ) (ns : List ℕ) : ℕ := (ns.map fun n => bitW n b).sum

/-- The sizes of all pieces with an exponent above b and below k, added up. -/
def aboveL (ns : List ℕ) (k b : ℕ) : ℕ := ∑ b' ∈ range k, if b < b' then cntL b' ns else 0

/-- One more segment at the front. -/
theorem cntL_cons (b n : ℕ) (ns : List ℕ) : cntL b (n :: ns) = bitW n b + cntL b ns := by
  simp only [cntL, List.map_cons, List.sum_cons]

/-- One more exponent at the top. -/
theorem aboveL_succ (ns : List ℕ) (k b : ℕ) :
    aboveL ns (k + 1) b = aboveL ns k b + if b < k then cntL k ns else 0 := by
  unfold aboveL
  rw [sum_range_succ]

/-- No exponent lies above b and below b + 1. -/
theorem aboveL_self (ns : List ℕ) {k b : ℕ} (h : k ≤ b + 1) : aboveL ns k b = 0 := by
  unfold aboveL
  refine sum_eq_zero fun b' hb' => ?_
  have h1 := mem_range.mp hb'
  rw [if_neg (by omega)]

/-- The sum over a list, as a sum over the places of the list. -/
theorem cntL_range (b : ℕ) : ∀ ns : List ℕ,
    cntL b ns = ∑ i ∈ range ns.length, bitW (ns.getD i 0) b
  | [] => by simp [cntL]
  | n :: ns => by
    rw [cntL_cons, cntL_range b ns, List.length_cons, sum_range_succ', Nat.add_comm]
    simp

/-- The sum over the first a members of a list, as a sum over the places of the list. -/
theorem cntL_take_range (b : ℕ) : ∀ (ns : List ℕ) (a : ℕ),
    cntL b (ns.take a) = ∑ i ∈ range ns.length, if i < a then bitW (ns.getD i 0) b else 0
  | [], _ => by simp [cntL]
  | _ :: _, 0 => by simp [cntL]
  | n :: ns, a + 1 => by
    rw [List.take_succ_cons, cntL_cons, cntL_take_range b ns a, List.length_cons, sum_range_succ',
      Nat.add_comm]
    simp

/-- The formula in two parts, with any bound K on the exponents in place of topBit + 1: the larger
pieces of all segments, then the pieces as large of the earlier segments. -/
theorem col_split (ns : List ℕ) (a : ℕ) {b K : ℕ} (hb : b < K) :
    (∑ a' ∈ range ns.length, ∑ b' ∈ range K,
      if (ns.getD a' 0).testBit b' = true ∧ (b < b' ∨ (b' = b ∧ a' < a)) then 2 ^ b' else 0) =
      aboveL ns K b + cntL b (ns.take a) := by
  have e : ∀ a' b' : ℕ,
      (if (ns.getD a' 0).testBit b' = true ∧ (b < b' ∨ (b' = b ∧ a' < a)) then 2 ^ b' else 0) =
        (if b < b' then bitW (ns.getD a' 0) b' else 0) +
          (if b' = b then (if a' < a then bitW (ns.getD a' 0) b else 0) else 0) := by
    intro a' b'
    unfold bitW
    rcases lt_trichotomy b b' with h | h | h
    · have h2 : b' ≠ b := by omega
      simp [h, h2]
    · subst h
      by_cases ha : a' < a <;> simp [ha]
    · have h1 : ¬ b < b' := by omega
      have h2 : b' ≠ b := by omega
      simp [h1, h2]
  have hA : (∑ a' ∈ range ns.length, ∑ b' ∈ range K,
      if b < b' then bitW (ns.getD a' 0) b' else 0) = aboveL ns K b := by
    unfold aboveL
    rw [sum_comm]
    refine sum_congr rfl fun b' _ => ?_
    by_cases h : b < b'
    · simp only [h, if_true]
      rw [cntL_range]
    · simp [h]
  have hB : (∑ a' ∈ range ns.length, ∑ b' ∈ range K,
      if b' = b then (if a' < a then bitW (ns.getD a' 0) b else 0) else 0) =
        cntL b (ns.take a) := by
    rw [cntL_take_range]
    refine sum_congr rfl fun a' _ => ?_
    rw [sum_ite_eq', if_pos (mem_range.mpr hb)]
  simp only [e, sum_add_distrib]
  rw [hA, hB]

/-- The formula colL in these two parts. -/
theorem colL_split (ns : List ℕ) (a : ℕ) {b : ℕ} (hb : b < topBit + 1) :
    colL ns a b = aboveL ns (topBit + 1) b + cntL b (ns.take a) := col_split ns a hb

/-! ## Bits -/

/-- A set bit of a number below 2^k is below k. -/
theorem lt_of_testBit {n b k : ℕ} (hT : n.testBit b = true) (hlt : n < 2 ^ k) : b < k := by
  by_contra hc
  have h1 : n < 2 ^ b :=
    lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hc))
  rw [Nat.testBit_lt_two_pow h1] at hT
  exact Bool.false_ne_true hT

/-- Every member of the list of the set bits below k is below k. -/
theorem bitsBelow_lt (n : ℕ) : ∀ (k b : ℕ), b ∈ bitsBelow n k → b < k
  | 0, b, h => by simp [bitsBelow] at h
  | k + 1, b, h => by
    rw [bitsBelow] at h
    rcases List.mem_append.mp h with h | h
    · cases hk : n.testBit k with
      | true =>
        have e : b = k := by simpa [hk] using h
        omega
      | false => simp [hk] at h
    · have h1 := bitsBelow_lt n k b h
      omega

/-! ## The pieces, with their first columns -/

/-- The first free column after the pieces of size 2^b. -/
theorem piecesOfSize_end (b : ℕ) : ∀ (ns : List ℕ) (s off : ℕ),
    (piecesOfSize b ns s off).2 = off + cntL b ns
  | [], _, _ => by simp [piecesOfSize, cntL]
  | n :: ns, s, off => by
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb, cntL_cons, bitW_true hb]
      show (piecesOfSize b ns (s + 1) (off + 2 ^ b)).2 = _
      rw [piecesOfSize_end b ns (s + 1) (off + 2 ^ b), Nat.add_assoc]
    | false =>
      rw [piecesOfSize_cons_false hb, cntL_cons, bitW_false hb, Nat.zero_add]
      exact piecesOfSize_end b ns (s + 1) off

/-- The piece of size 2^b that member number d of the list gets, if its length has bit b: it begins
after the pieces of that size of the members before it. -/
theorem filter_piecesOfSize (b : ℕ) : ∀ (ns : List ℕ) (s0 d off : ℕ),
    ((piecesOfSize b ns s0 off).1.filter fun p => p.1 == s0 + d) =
      if (ns.getD d 0).testBit b = true then [(s0 + d, b, off + cntL b (ns.take d))] else []
  | [], _, _, _ => by simp [piecesOfSize]
  | n :: ns, s0, 0, off => by
    have ih := fun off' => filter_piecesOfSize_lt b s0 ns (s0 + 1) off' (Nat.lt_succ_self _)
    rw [Nat.add_zero]
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show List.filter (fun p => p.1 == s0)
        ((s0, b, off) :: (piecesOfSize b ns (s0 + 1) (off + 2 ^ b)).1) = _
      rw [List.filter_cons_of_pos (by simp), ih]
      simp [hb, cntL]
    | false =>
      rw [piecesOfSize_cons_false hb, ih]
      simp [hb]
  | n :: ns, s0, d + 1, off => by
    have ih := fun off' => filter_piecesOfSize b ns (s0 + 1) d off'
    have e : s0 + (d + 1) = s0 + 1 + d := by omega
    have hne : s0 ≠ s0 + 1 + d := by omega
    rw [e, List.getD_cons_succ, List.take_succ_cons, cntL_cons]
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show List.filter (fun p => p.1 == s0 + 1 + d)
        ((s0, b, off) :: (piecesOfSize b ns (s0 + 1) (off + 2 ^ b)).1) = _
      rw [List.filter_cons_of_neg (by simpa using hne), ih, bitW_true hb, Nat.add_assoc off]
    | false =>
      rw [piecesOfSize_cons_false hb, ih, bitW_false hb, Nat.zero_add]

/-- The first free column after the pieces of sizes 2^(k - 1) down to 1. -/
theorem piecesBelow_end (ns : List ℕ) : ∀ (k off : ℕ),
    (piecesBelow ns k off).2 = off + ∑ b ∈ range k, cntL b ns
  | 0, _ => by simp [piecesBelow]
  | k + 1, off => by
    rw [piecesBelow_succ]
    show (piecesBelow ns k (piecesOfSize k ns 0 off).2).2 = _
    rw [piecesBelow_end ns k, piecesOfSize_end, sum_range_succ]
    omega

/-- The pieces of segment number s, in the order of the list: one for each set bit of its length
below k, from the top down. The piece of exponent b begins after all larger pieces and after the
pieces as large of the segments before s. -/
theorem filter_piecesBelow (ns : List ℕ) (s : ℕ) : ∀ (k off : ℕ),
    ((piecesBelow ns k off).1.filter fun p => p.1 == s) =
      (bitsBelow (ns.getD s 0) k).map fun b =>
        (s, b, off + aboveL ns k b + cntL b (ns.take s))
  | 0, _ => by simp [piecesBelow, bitsBelow]
  | k + 1, off => by
    have h1 := filter_piecesOfSize k ns 0 s off
    rw [Nat.zero_add] at h1
    rw [piecesBelow_succ]
    show List.filter (fun p => p.1 == s) ((piecesOfSize k ns 0 off).1 ++
      (piecesBelow ns k (piecesOfSize k ns 0 off).2).1) = _
    rw [List.filter_append, h1, filter_piecesBelow ns s k, piecesOfSize_end, bitsBelow,
      List.map_append]
    congr 1
    · cases hk : (ns.getD s 0).testBit k with
      | true => simp [aboveL_self ns (Nat.le_refl (k + 1))]
      | false => simp
    · refine List.map_congr_left fun b hb => ?_
      have hlt := bitsBelow_lt _ _ _ hb
      have e : off + cntL k ns + aboveL ns k b = off + (aboveL ns k b + cntL k ns) := by omega
      rw [aboveL_succ, if_pos hlt, e]

/-- The same from column 0 on. -/
theorem filter_piecesBelow_zero (ns : List ℕ) (s k : ℕ) :
    ((piecesBelow ns k 0).1.filter fun p => p.1 == s) =
      (bitsBelow (ns.getD s 0) k).map fun b => (s, b, aboveL ns k b + cntL b (ns.take s)) := by
  rw [filter_piecesBelow]
  simp only [Nat.zero_add]

/-! ## Laying the pieces of one segment -/

/-- Laying, behind an array a, one piece for each set bit of n below k, from the top down, the piece
of exponent b from column c b on. The array grows by the lowest k bits of n; what stood in it stays;
and the piece of exponent b stands after the larger pieces, that is st entries behind the end of a,
where st and the bits of n up to b make up the lowest k bits of n. -/
theorem fold_bits (n s : ℕ) (c : ℕ → ℕ) : ∀ (k : ℕ) (a : Array ℕ),
    (((bitsBelow n k).map fun b => (s, b, c b)).foldl layStep a).size = a.size + n % 2 ^ k ∧
    (∀ x, x < a.size →
      (((bitsBelow n k).map fun b => (s, b, c b)).foldl layStep a).getD x 0 = a.getD x 0) ∧
    ∀ b st y, b < k → n.testBit b = true → st + n % 2 ^ (b + 1) = n % 2 ^ k → y < 2 ^ b →
      (((bitsBelow n k).map fun b => (s, b, c b)).foldl layStep a).getD (a.size + st + y) 0 =
        c b + y
  | 0, a => ⟨by simp [bitsBelow, Nat.mod_one], fun x _ => by simp [bitsBelow],
      fun b st y hb => by omega⟩
  | k + 1, a => by
    have em := mod_two_pow_succ n k
    cases hk : n.testBit k with
    | true =>
      have eb : bitsBelow n (k + 1) = k :: bitsBelow n k := by simp [bitsBelow, hk]
      rw [if_pos hk] at em
      obtain ⟨i1, i2, i3⟩ := fold_bits n s c k (layStep a (s, k, c k))
      have es : (layStep a (s, k, c k)).size = a.size + 2 ^ k := size_append_run a k (c k)
      have hp : 0 < 2 ^ k := Nat.two_pow_pos k
      rw [eb, List.map_cons, List.foldl_cons]
      refine ⟨by rw [i1, es, em]; omega, fun x hx => ?_, fun b st y hb hT hst hy => ?_⟩
      · rw [i2 x (by rw [es]; omega)]
        exact getD_run_left a k (c k) hx
      · rcases Nat.lt_or_ge b k with hlt | hge
        · have hle : b + 1 ≤ k := hlt
          have hm : n % 2 ^ (b + 1) ≤ n % 2 ^ k := by
            have e := Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hle)
            rw [← e]
            exact Nat.mod_le _ _
          have h3 := i3 b (st - 2 ^ k) y hlt hT (by omega) hy
          have e : a.size + 2 ^ k + (st - 2 ^ k) + y = a.size + st + y := by omega
          rw [es, e] at h3
          exact h3
        · have ebk : b = k := by omega
          subst ebk
          have hst0 : st = 0 := by omega
          subst hst0
          rw [Nat.add_zero, i2 _ (by rw [es]; omega)]
          exact (getD_run_right a b (c b) hy).trans (Nat.add_comm _ _)
    | false =>
      have eb : bitsBelow n (k + 1) = bitsBelow n k := by simp [bitsBelow, hk]
      rw [if_neg (by simp [hk]), Nat.zero_add] at em
      obtain ⟨i1, i2, i3⟩ := fold_bits n s c k a
      rw [eb, em]
      refine ⟨i1, i2, fun b st y hb hT hst hy => ?_⟩
      have hne : b ≠ k := by
        intro e
        rw [e, hk] at hT
        exact Bool.false_ne_true hT
      exact i3 b st y (by omega) hT hst hy

/-- The columns of segment number s, from the pieces of sizes below 2^k, if its length is below 2^k:
the entries from pieceStart on, 2^b of them, lie in neighbouring columns, which begin after all
larger pieces and after the pieces as large of the segments before s. -/
theorem columnsOf_piece (ns : List ℕ) (s k b y : ℕ) (hlt : ns.getD s 0 < 2 ^ k)
    (hT : (ns.getD s 0).testBit b = true) (hy : y < 2 ^ b) :
    (columnsOf (piecesBelow ns k 0).1 s (ns.getD s 0)).getD
        (pieceStart (ns.getD s 0) b + y) 0 =
      aboveL ns k b + cntL b (ns.take s) + y := by
  obtain ⟨f1, _, f3⟩ :=
    fold_bits (ns.getD s 0) s (fun b => aboveL ns k b + cntL b (ns.take s)) k #[]
  have e0 : (#[] : Array ℕ).size = 0 := rfl
  have h := f3 b (pieceStart (ns.getD s 0) b) y (lt_of_testBit hT hlt) hT
    (by rw [Nat.mod_eq_of_lt hlt]; exact Nat.div_add_mod' _ _) hy
  rw [e0, Nat.zero_add, Nat.mod_eq_of_lt hlt] at f1
  rw [e0, Nat.zero_add] at h
  rw [columnsOf_eq, filter_piecesBelow_zero, fill_none f1]
  exact h

/-! ## The verifier's rule against the formula -/

/-- Member number i of a list of images. -/
theorem getD_map_some {α β : Type} (f : α → β) (d : β) {l : List α} {i : ℕ} {x : α}
    (h : l[i]? = some x) : (l.map f).getD i d = f x := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Member number i of the images of a list's members with their numbers, counted from k on. -/
theorem zipIdx_map_getD {α β : Type} (f : α × ℕ → β) (d : β) : ∀ (l : List α) (k i : ℕ) (x : α),
    l[i]? = some x → ((l.zipIdx k).map f).getD i d = f (x, k + i)
  | [], _, _, _, h => by simp at h
  | z :: l, k, 0, x, h => by
    have e : z = x := by simpa using h
    rw [e, List.zipIdx_cons, List.map_cons, List.getD_cons_zero, Nat.add_zero]
  | z :: l, k, i + 1, x, h => by
    have h1 := zipIdx_map_getD f d l (k + 1) i x (by simpa using h)
    have e : k + 1 + i = k + (i + 1) := by omega
    rw [List.zipIdx_cons, List.map_cons, List.getD_cons_succ, h1, e]

/-- The columns that the verifier's rule gives to segment number a. -/
theorem place_columns (name kind : String) (asks : List SegAsk) (fl a : ℕ)
    (ha : a < asks.length) :
    ((place name kind asks fl).segs.getD a default).pos =
      columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 a
        ((asks.map (·.2.1)).getD a 0) := by
  have hx : asks[a]? = some asks[a] := List.getElem?_eq_getElem ha
  have hn : (asks.map (·.2.1)).getD a 0 = asks[a].2.1 := getD_map_some _ 0 hx
  have h := zipIdx_map_getD (fun x : SegAsk × ℕ =>
    ({ name := x.1.1, n := x.1.2.1,
       pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
       moe := x.1.2.2 } : Seg)) default asks 0 a _ hx
  have h' : (place name kind asks fl).segs.getD a default =
      ({ name := asks[a].1, n := asks[a].2.1,
         pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 (0 + a) asks[a].2.1,
         moe := asks[a].2.2 } : Seg) := h
  rw [h', hn, Nat.zero_add]

/-- The verifier's rule against the formula colL. Of segment number a, whose length n is below
2^(topBit + 1), the piece of exponent b holds the entries pieceStart n b + y, y < 2^b, in order, in
the columns from colL on. The other segments' lengths are free. -/
theorem place_pos (name kind : String) (asks : List SegAsk) (fl a b y : ℕ) (ha : a < asks.length)
    (hlt : (asks.map (·.2.1)).getD a 0 < 2 ^ (topBit + 1))
    (hT : ((asks.map fun x : SegAsk => x.2.1).getD a 0).testBit b = true) (hy : y < 2 ^ b) :
    ((place name kind asks fl).segs.getD a default).pos.getD
        (pieceStart ((asks.map (·.2.1)).getD a 0) b + y) 0 =
      colL (asks.map (·.2.1)) a b + y := by
  rw [place_columns name kind asks fl a ha, columnsOf_piece _ _ _ _ _ hlt hT hy,
    colL_split _ _ (lt_of_testBit hT hlt)]

/-! ## The library's first column against the formula -/

/-- In a list without repeats, a sum over the members that reads each member's place is the sum
over the places. -/
theorem sum_idxOf {α : Type} [DecidableEq α] (f : α → ℕ) (F : ℕ → ℕ → ℕ) :
    ∀ (l : List α) (k : ℕ), l.Nodup →
      (l.map fun x => F (f x) (l.idxOf x + k)).sum =
        ∑ i ∈ range l.length, F ((l.map f).getD i 0) (i + k)
  | [], _, _ => by simp
  | x :: l, k, h => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp h
    have e : (l.map fun y => F (f y) ((x :: l).idxOf y + k)) =
        l.map fun y => F (f y) (l.idxOf y + (k + 1)) := by
      refine List.map_congr_left fun y hy => ?_
      have hne : x ≠ y := fun e => hx (e ▸ hy)
      have e1 : (x :: l).idxOf y = l.idxOf y + 1 := by simp [hne]
      rw [e1, Nat.add_assoc, Nat.add_comm 1 k]
    rw [List.map_cons, List.sum_cons, e, sum_idxOf f F l (k + 1) hl, List.idxOf_cons_self,
      List.length_cons, sum_range_succ', List.map_cons, List.getD_cons_zero, Nat.add_comm]
    simp only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 k]

/-- A member's place in a list is inside the list, and the list of images has its image there. -/
theorem idxOf_spec {α : Type} [DecidableEq α] (f : α → ℕ) : ∀ (l : List α) (x : α), x ∈ l →
    l.idxOf x < l.length ∧ (l.map f).getD (l.idxOf x) 0 = f x
  | [], _, h => by simp at h
  | z :: l, x, h => by
    by_cases e : z = x
    · subst e
      simp
    · have hx : x ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      obtain ⟨i1, i2⟩ := idxOf_spec f l x hx
      have e1 : (z :: l).idxOf x = l.idxOf x + 1 := by simp [e]
      rw [e1, List.length_cons, List.map_cons, List.getD_cons_succ]
      exact ⟨by omega, i2⟩

/-- The library's colBase against the formula colL: at the lengths of the families of the call of s,
each below 2^(topBit + 1), and at the place of s in its call, they are one number. -/
theorem colBase_colL (D : Dim) (s : Fam) (b : ℕ)
    (hlt : ∀ s' ∈ fams (call s), len D s' < 2 ^ (topBit + 1)) :
    colBase D s b = colL ((fams (call s)).map (len D)) (ord s) b := by
  have e : ((fams (call s)).map fun s' =>
      ∑ b' ∈ range (Nat.size (len D s')), if (len D s').testBit b' = true ∧
        (b < b' ∨ (b' = b ∧ ord s' < ord s)) then 2 ^ b' else 0) =
      (fams (call s)).map fun s' =>
        colTerm (ord s) b (len D s') ((fams (call s)).idxOf s' + 0) := by
    refine List.map_congr_left fun s' hs' => ?_
    have ho : (fams (call s)).idxOf s' = ord s' := by
      unfold ord
      rw [call_of_mem _ _ hs']
    have hsz : Nat.size (len D s') ≤ topBit + 1 := Nat.size_le.mpr (hlt s' hs')
    unfold colTerm
    rw [Nat.add_zero, ho]
    refine sum_subset
      (fun x hx => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) hsz)) fun b' _ hb' => ?_
    have hT : ¬ (len D s').testBit b' = true :=
      fun hT => hb' (mem_range.mpr (lt_size_of_testBit hT))
    rw [if_neg fun hc => hT hc.1]
  unfold colBase
  rw [e, sum_idxOf (len D) (colTerm (ord s) b) _ 0 (fams_nodup _), colL_terms, List.length_map]
  simp only [Nat.add_zero]

/-! ## The columns: the verifier's against the library's -/

/-- The verifier's rule against the library's index map. If the lengths in a call's line are the
lengths of the families of the library's call c, in the library's order, and each is below
2^(topBit + 1), then entry x of the segment at the place of the family s lies in the column
pos D s x, for every family s of the call and every x below its length. -/
theorem pos_eq (D : Dim) (c : Fin 8) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hl : asks.map (·.2.1) = (fams c).map (len D))
    (hlt : ∀ s ∈ fams c, len D s < 2 ^ (topBit + 1)) {s : Fam} (hs : s ∈ fams c) {x : ℕ}
    (hx : x < len D s) :
    ((place name kind asks fl).segs.getD (ord s) default).pos.getD x 0 = pos D s x := by
  have hc : call s = c := call_of_mem c s hs
  subst hc
  obtain ⟨o1, o2⟩ := idxOf_spec (len D) _ s hs
  have hn : (asks.map (·.2.1)).getD (ord s) 0 = len D s := by
    rw [hl]
    exact o2
  have ha : ord s < asks.length := by
    have e : asks.length = (fams (call s)).length := by
      have e1 := congrArg List.length hl
      rw [List.length_map, List.length_map] at e1
      exact e1
    rw [e]
    exact o1
  have hb := isBit_bitOf hx
  obtain ⟨h1, _⟩ := isBit_split hb
  have hT : (len D s).testBit (bitOf (len D s) x) = true := (testBit_iff _ _).mpr hb.2.1
  have hy : x % 2 ^ bitOf (len D s) x < 2 ^ bitOf (len D s) x :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have h := place_pos name kind asks fl (ord s) (bitOf (len D s) x) _ ha
    (by rw [hn]; exact hlt s hs) (by rw [hn]; exact hT) hy
  rw [hn, ← h1, hl, ← colBase_colL D s _ hlt] at h
  exact h

/-! ## The same for the members of the list of segments -/

/-- The images of a list's members with their numbers, under a function that reads the member
alone. -/
theorem zipIdx_map_left {α β : Type} (g : α → β) : ∀ (l : List α) (k : ℕ),
    ((l.zipIdx k).map fun x => g x.1) = l.map g
  | [], _ => rfl
  | z :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_left g l (k + 1)]

/-- What the placed segments keep of the call's line: name, length, and whether the segment exists
only on layers with routed experts, in the order of the line. -/
theorem place_map {β : Type} (G : String → ℕ → Bool → β) (name kind : String)
    (asks : List SegAsk) (fl : ℕ) :
    ((place name kind asks fl).segs.map fun g => G g.name g.n g.moe) =
      asks.map fun a => G a.1 a.2.1 a.2.2 := by
  show ((asks.zipIdx.map fun x : SegAsk × ℕ =>
    ({ name := x.1.1, n := x.1.2.1,
       pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
       moe := x.1.2.2 } : Seg)).map fun g => G g.name g.n g.moe) = _
  rw [List.map_map]
  exact zipIdx_map_left (fun a : SegAsk => G a.1 a.2.1 a.2.2) asks 0

/-- In a list without repeats, the place of the member at number i is i. -/
theorem idxOf_at {α : Type} [DecidableEq α] : ∀ (l : List α) (i : ℕ) (x : α), l.Nodup →
    l[i]? = some x → l.idxOf x = i
  | [], _, _, _, h => by simp at h
  | z :: l, 0, x, _, h => by
    have e : z = x := by simpa using h
    rw [e, List.idxOf_cons_self]
  | z :: l, i + 1, x, hnd, h => by
    obtain ⟨hz, hl⟩ := List.nodup_cons.mp hnd
    have h' : l[i]? = some x := by simpa using h
    have hne : z ≠ x := fun e => hz (e ▸ List.mem_of_getElem? h')
    have e1 : (z :: l).idxOf x = l.idxOf x + 1 := by simp [hne]
    rw [e1, idxOf_at l i x hl h']

/-- If a function fam sends the placed segments, in order, to the families of the library's call c,
and every segment has the length of its family, then the lengths in the call's line are those of the
call's families: the first hypothesis of pos_eq, pieces_used, lJ_max and lJ_eq. -/
theorem lengths_of_segs (D : Dim) (c : Fin 8) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (fam : Seg → Fam) (hf : (place name kind asks fl).segs.map fam = fams c)
    (hn : ∀ g ∈ (place name kind asks fl).segs, g.n = len D (fam g)) :
    asks.map (·.2.1) = (fams c).map (len D) := by
  have h1 := place_map (fun _ n _ => n) name kind asks fl
  have h2 : ((place name kind asks fl).segs.map fun g => g.n) =
      (place name kind asks fl).segs.map fun g => len D (fam g) := List.map_congr_left hn
  rw [← hf, List.map_map]
  exact h1.symm.trans h2

/-- The verifier's rule against the library's index map, for the members of the list of segments:
under the hypotheses of lengths_of_segs, with every length below 2^(topBit + 1), entry x of a
segment g lies in the column pos D (fam g) x, for every x below the length. -/
theorem pos_eq_segs (D : Dim) (c : Fin 8) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (fam : Seg → Fam) (hf : (place name kind asks fl).segs.map fam = fams c)
    (hn : ∀ g ∈ (place name kind asks fl).segs, g.n = len D (fam g))
    (hlt : ∀ s ∈ fams c, len D s < 2 ^ (topBit + 1)) :
    ∀ g ∈ (place name kind asks fl).segs, ∀ x, x < len D (fam g) →
      g.pos.getD x 0 = pos D (fam g) x := by
  intro g hg x hx
  have hl := lengths_of_segs D c name kind asks fl fam hf hn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi' : (place name kind asks fl).segs[i]? = some (place name kind asks fl).segs[i] :=
    List.getElem?_eq_getElem hi
  have h1 : (fams c)[i]? = some (fam (place name kind asks fl).segs[i]) := by
    rw [← hf, List.getElem?_map, hi']
    rfl
  have hm : fam (place name kind asks fl).segs[i] ∈ fams c := List.mem_of_getElem? h1
  have ho : ord (fam (place name kind asks fl).segs[i]) = i := by
    unfold ord
    rw [call_of_mem c _ hm]
    exact idxOf_at _ i _ (fams_nodup c) h1
  have hd : (place name kind asks fl).segs.getD i default = (place name kind asks fl).segs[i] := by
    rw [List.getD_eq_getElem?_getD, hi']
    rfl
  have h := pos_eq D c name kind asks fl hl hlt hm hx
  rw [ho, hd] at h
  exact h

/-! ## The number of columns -/

/-- The sizes of all pieces with an exponent below k add up to the lengths' lowest k bits. -/
theorem sum_cntL (k : ℕ) : ∀ ns : List ℕ,
    ∑ b ∈ range k, cntL b ns = (ns.map fun n => n % 2 ^ k).sum
  | [] => by simp [cntL]
  | n :: ns => by
    have e : ∑ b ∈ range k, bitW n b = n % 2 ^ k := sum_bits n k
    simp only [cntL_cons, sum_add_distrib]
    rw [sum_cntL k ns, List.map_cons, List.sum_cons, e]

/-- If every length is below 2^k, the first free column after all pieces is the sum of the
lengths. -/
theorem piecesBelow_total (ns : List ℕ) (k : ℕ) (h : ∀ n ∈ ns, n < 2 ^ k) :
    (piecesBelow ns k 0).2 = ns.sum := by
  have e : (ns.map fun n => n % 2 ^ k) = ns.map id :=
    List.map_congr_left fun n hn => Nat.mod_eq_of_lt (h n hn)
  rw [piecesBelow_end, sum_cntL, Nat.zero_add, e, List.map_id]

/-- The verifier's first free column against the library's number of used columns, under the
hypotheses of pos_eq. -/
theorem pieces_used (D : Dim) (c : Fin 8) (asks : List SegAsk)
    (hl : asks.map (·.2.1) = (fams c).map (len D))
    (hlt : ∀ s ∈ fams c, len D s < 2 ^ (topBit + 1)) :
    (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 = used D c := by
  rw [hl]
  refine piecesBelow_total _ _ fun n hn => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
  exact hlt s hs

/-- The verifier's number of columns is two to the power of its logarithm lJ. -/
theorem place_J (name kind : String) (asks : List SegAsk) (fl : ℕ) :
    (place name kind asks fl).J = 2 ^ (place name kind asks fl).lJ := rfl

/-- The verifier's ceilLog2 is Mathlib's Nat.clog 2, at every number; both are 0 at 0 and at 1. -/
theorem ceilLog2_eq_clog (n : ℕ) : ceilLog2 n = Nat.clog 2 n := by
  unfold ceilLog2
  split_ifs with h
  · have h1 : Nat.clog 2 n ≤ 0 := (Nat.clog_le_iff_le_pow (by decide)).2 (by simpa using h)
    omega
  · have h0 : n - 1 ≠ 0 := by omega
    have h1 : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (n - 1).log2 ≤ n - 1 := Nat.log2_self_le h0
    have h3 : (n - 1).log2 < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by decide)).2 (by omega)
    have h4 : Nat.clog 2 n ≤ (n - 1).log2 + 1 :=
      (Nat.clog_le_iff_le_pow (by decide)).2 (by omega)
    omega

/-- The verifier's logarithm of the number of columns against the library's, under the hypotheses of
pos_eq: it is the larger of the library's lJ and the verifier's minimum fl. -/
theorem lJ_max (D : Dim) (c : Fin 8) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hl : asks.map (·.2.1) = (fams c).map (len D))
    (hlt : ∀ s ∈ fams c, len D s < 2 ^ (topBit + 1)) :
    (place name kind asks fl).lJ = max (lJ D c) fl := by
  show max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl =
    max (Nat.clog 2 (used D c)) fl
  rw [pieces_used D c asks hl hlt, ceilLog2_eq_clog]

/-- If moreover the verifier's minimum is at most the library's lJ, the two are one number. -/
theorem lJ_eq (D : Dim) (c : Fin 8) (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hl : asks.map (·.2.1) = (fams c).map (len D))
    (hlt : ∀ s ∈ fams c, len D s < 2 ^ (topBit + 1)) (hfl : fl ≤ Nat.clog 2 (used D c)) :
    (place name kind asks fl).lJ = lJ D c := by
  rw [lJ_max D c name kind asks fl hl hlt]
  exact max_eq_left hfl

/-! ## The hypotheses can be met -/

/-- A line for the library's call c: its families in the library's order, each with the name of its
segment, its length, and whether it exists only on layers with routed experts. -/
def asksOf (D : Dim) (c : Fin 8) : List SegAsk :=
  (fams c).map fun s => (segName s, len D s, isExp s)

/-- Its lengths are the lengths of the call's families. -/
theorem asksOf_lengths (D : Dim) (c : Fin 8) :
    (asksOf D c).map (·.2.1) = (fams c).map (len D) := by
  simp [asksOf, List.map_map, Function.comp_def]

/-- At the library's reference sizes every family's length is below 2^(topBit + 1). -/
theorem ref_len_lt (s : Fam) : len Dim.ref s < 2 ^ (topBit + 1) := by
  cases s <;> decide +kernel

/-- The two hypotheses of pos_eq, pieces_used and lJ_max hold together of the line asksOf at the
library's reference sizes, for every call. -/
theorem met_ref (c : Fin 8) :
    (asksOf Dim.ref c).map (·.2.1) = (fams c).map (len Dim.ref) ∧
      ∀ s ∈ fams c, len Dim.ref s < 2 ^ (topBit + 1) :=
  ⟨asksOf_lengths Dim.ref c, fun s _ => ref_len_lt s⟩

/-- The family whose segment has the name nm; the family G if there is none. -/
def famNamed (nm : String) : Fam :=
  ((([.G, .U, .UT, .QK, .N1, .N2, .O, .D, .V, .LR, .XR, .LT, .DD, .GH, .UH, .OH, .DH, .VH, .LH,
    .QKH, .N1H, .N2H, .ROW, .SEL, .L3, .G0, .CN1, .CN2, .CQK, .CV, .CLR, .F, .MR, .CG] :
      List Fam).find? fun s => segName s == nm).getD .G)

/-- It finds each family under its segment's name. -/
theorem famNamed_segName (s : Fam) : famNamed (segName s) = s := by cases s <;> rfl

/-- The two hypotheses of lengths_of_segs and pos_eq_segs on the function fam hold together of the
line asksOf, at all sizes, with the function that reads a segment's name. -/
theorem met_segs (D : Dim) (c : Fin 8) (name kind : String) (fl : ℕ) :
    ((place name kind (asksOf D c) fl).segs.map fun g => famNamed g.name) = fams c ∧
      ∀ g ∈ (place name kind (asksOf D c) fl).segs, g.n = len D (famNamed g.name) := by
  constructor
  · rw [place_map (fun nm _ _ => famNamed nm) name kind (asksOf D c) fl, asksOf, List.map_map]
    have e : ((fams c).map
        ((fun a : SegAsk => famNamed a.1) ∘ fun s => (segName s, len D s, isExp s))) =
        (fams c).map id := List.map_congr_left fun s _ => famNamed_segName s
    rw [e, List.map_id]
  · have h := place_map (fun nm n _ => decide (n = len D (famNamed nm))) name kind (asksOf D c) fl
    have e : ((asksOf D c).map fun a => decide (a.2.1 = len D (famNamed a.1))) =
        (asksOf D c).map fun _ => true := by
      refine List.map_congr_left fun a ha => ?_
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
      show decide (len D s = len D (famNamed (segName s))) = true
      rw [famNamed_segName]
      exact decide_eq_true rfl
    rw [e] at h
    intro g hg
    have h1 : decide (g.n = len D (famNamed g.name)) ∈
        (asksOf D c).map fun _ => true := by
      rw [← h]
      exact List.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨_, _, h2⟩ := List.mem_map.mp h1
    exact of_decide_eq_true h2.symm

/-- True if, for segments of the lengths ns and the minimum 0, the verifier's rule puts every piece
of every segment in the columns that the formula colL gives. It serves a run on made-up lengths. -/
def runPos (ns : List ℕ) : Bool :=
  (List.range ns.length).all fun a => (List.range (topBit + 1)).all fun b =>
    !(ns.getD a 0).testBit b || (List.range (2 ^ b)).all fun y =>
      (((place "c" "k" (ns.map fun n => ("s", n, false)) 0).segs.getD a default).pos.getD
        (pieceStart (ns.getD a 0) b + y) 0) == colL ns a b + y

#guard runPos [12, 20, 4, 7, 1, 0, 20]
#guard colL [12, 20, 4] 0 3 = 16 ∧ colL [12, 20, 4] 1 4 = 0 ∧ colL [12, 20, 4] 1 2 = 28 ∧
  colL [12, 20, 4] 2 2 = 32

/- Two controls on made-up numbers. Where the minimum is above the logarithm of the used columns,
the verifier's lJ is the minimum: lJ_eq needs its last hypothesis. A bit above topBit gets no piece,
so the first free column is not the sum of the lengths: pieces_used needs the bound on the
lengths. -/
#guard (place "c" "k" [("s", 3, false)] 5).lJ = 5 ∧ Nat.clog 2 3 = 2
#guard (piecesBelow [2 ^ 41 + 1] (topBit + 1) 0).2 = 1

#print axioms place_pos
#print axioms colBase_colL
#print axioms pos_eq
#print axioms lengths_of_segs
#print axioms pos_eq_segs
#print axioms pieces_used
#print axioms ceilLog2_eq_clog
#print axioms lJ_max
#print axioms lJ_eq
#print axioms met_ref
#print axioms met_segs

end OnBytes.Road
