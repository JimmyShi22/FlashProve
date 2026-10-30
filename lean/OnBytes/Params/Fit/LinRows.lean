-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/LinRows.lean: under bounds on the numbers from which they are formed (LinNums),
the five oracle messages of the test on the table have at most 2^128 main rows and mask rows each;
and a group of at most three such messages has at most 131 row variables of either kind
(linGroupBits).

OnBytes/Params/Fit/LinParts.lean says which numbers of rows the five oracle messages have. Here
these numbers are bounded, under bounds on the numbers from which linSized's text forms them. The
bound is far from sharp: it is meant for "the variables of a sample's cube are few".

Main theorems.
 - maskRowsFor_le: Send.maskRowsFor returns at most 4096, whatever it is given.
 - linRowsOf_le, foldedEntries_le; rows_linU, rows_linOmega, rows_linW.
 - lin_rows: the five shapes of what linSized returns.
 - linGroupBits_le: the two numbers of row variables of a group of at most three such messages.

What is asked (LinNums): at most four answers to a sample; kLo ≤ 40; at most 2^64 rows of the
matrix; the table's code has at most 2^32 message entries and 2^32 random entries; at most 4096
mask rows of the request's mask message; the two lines' logL ≤ 32. None is shown here. Nothing on
soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Params.Fit.LinParts

set_option autoImplicit false

namespace OnBytes.Params

/-- n ≤ 2^k gives clog2 n ≤ k. -/
theorem clog2_pow_le {n k : Nat} (h : n ≤ 2 ^ k) : clog2 n ≤ k := by
  unfold clog2
  split
  · exact Nat.zero_le k
  · rename_i h1
    have h2 : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- The least number of mask rows is sought up to 4096. -/
theorem maskRowsFor_le (entries ellZk answers : Nat) :
    Send.maskRowsFor entries ellZk answers ≤ 4096 := by
  unfold Send.maskRowsFor
  split
  · rename_i i hi
    have := List.mem_range.1 (List.mem_of_find?_eq_some hi)
    omega
  · exact Nat.zero_le _

/-- Rows that are not rounded up to a power of two. -/
theorem linRowsOf_le (a e : Nat) : linRowsOf a e true ≤ a + e := by
  show (a + e - 1) / e ≤ a + e
  exact (Nat.div_le_self _ _).trans (by omega)

/-- The entries that a table's folded row takes. -/
theorem foldedEntries_le {I : IndexShape} (h1 : I.code.ell ≤ 2 ^ 32) (h2 : I.code.r ≤ 2 ^ 32) :
    foldedEntries I ≤ 3 * 2 ^ 32 := by
  show (I.code.ell + 2 ^ clog2 I.code.r - 1) / 2 ^ clog2 I.code.r * 2 ^ clog2 I.code.r +
    I.code.r ≤ 3 * 2 ^ 32
  have hp : 2 ^ clog2 I.code.r ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by decide) (clog2_pow_le h2)
  have hd := Nat.div_mul_le_self (I.code.ell + 2 ^ clog2 I.code.r - 1) (2 ^ clog2 I.code.r)
  omega

/-- The bounds on the numbers from which the rows are formed. -/
structure LinNums (s : Setting) (L : LinLines) (T : TableSize) : Prop where
  samples : s.samples ≤ 4
  kLo : L.kLo ≤ 40
  matrix : L.matrixRows ≤ 2 ^ 64
  ell : T.code.ell ≤ 2 ^ 32
  r : T.code.r ≤ 2 ^ 32
  input : L.inputMaskRows ≤ 4096
  foldedL : L.folded.logL ≤ 32
  omegaL : L.omega.logL ≤ 32

/-- At most 2^128 main rows and at most 2^128 mask rows. -/
def FewRows (o : OracleShape) : Prop := o.mainRows ≤ 2 ^ 128 ∧ o.maskRows ≤ 2 ^ 128

theorem FewRows.of_same {a b : OracleShape} (h : SameRows a b) (hb : FewRows b) : FewRows a :=
  ⟨h.1 ▸ hb.1, h.2 ▸ hb.2⟩

section
variable {s : Setting} {L : LinLines} {T : TableSize}

theorem rows_linU (N : LinNums s L T) : FewRows (linU s L T) := by
  refine ⟨?_, Nat.zero_le _⟩
  show linRowsOf (foldedEntries (indexShapeOf s T) + s.samples) (2 ^ L.folded.logL) true ≤ 2 ^ 128
  have h1 := linRowsOf_le (foldedEntries (indexShapeOf s T) + s.samples) (2 ^ L.folded.logL)
  have h2 : foldedEntries (indexShapeOf s T) ≤ 3 * 2 ^ 32 := foldedEntries_le N.ell N.r
  have h3 : 2 ^ L.folded.logL ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) N.foldedL
  have h4 := N.samples
  have g : 3 * 2 ^ 32 + 4 + 2 ^ 32 ≤ 2 ^ 128 := by norm_num
  omega

theorem rows_linOmega (N : LinNums s L T) : FewRows (linOmega s L) := by
  refine ⟨?_, Nat.zero_le _⟩
  show linRowsOf (L.matrixRows + s.samples) (2 ^ L.omega.logL) true ≤ 2 ^ 128
  have h1 := linRowsOf_le (L.matrixRows + s.samples) (2 ^ L.omega.logL)
  have h2 := N.matrix
  have h3 : 2 ^ L.omega.logL ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) N.omegaL
  have h4 := N.samples
  have g : 2 ^ 64 + 4 + 2 ^ 32 ≤ 2 ^ 128 := by norm_num
  omega

theorem rows_linW (N : LinNums s L T) (hv : (indexShapeOf s T).v ≤ 40) :
    FewRows (linW s L T) := by
  constructor
  · show linRowsOf (2 ^ (L.kLo + (indexShapeOf s T).v)) (2 ^ L.omega.logL) true ≤ 2 ^ 128
    have h1 := linRowsOf_le (2 ^ (L.kLo + (indexShapeOf s T).v)) (2 ^ L.omega.logL)
    have h2 : 2 ^ (L.kLo + (indexShapeOf s T).v) ≤ 2 ^ 80 :=
      Nat.pow_le_pow_right (by decide) (by have := N.kLo; omega)
    have h3 : 2 ^ L.omega.logL ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) N.omegaL
    have g : 2 ^ 80 + 2 ^ 32 ≤ 2 ^ 128 := by norm_num
    omega
  · show (if linWRows s L T * 2 ^ L.omega.logL - 2 ^ (L.kLo + (indexShapeOf s T).v) < s.samples
      then 1 else 0) ≤ 2 ^ 128
    have g : 1 ≤ 2 ^ 128 := Nat.one_le_two_pow
    split
    · exact g
    · exact Nat.zero_le _

theorem rows_linSplitMsg : FewRows (linSplitMsg s) := ⟨Nat.zero_le _, Nat.one_le_two_pow⟩

theorem rows_linInput (N : LinNums s L T) : FewRows (linInput s L) := by
  refine ⟨Nat.zero_le _, ?_⟩
  show L.inputMaskRows ≤ 2 ^ 128
  have h := N.input
  have g : 4096 ≤ 2 ^ 128 := by norm_num
  omega

/-- **The five oracle messages of what linSized returns.** -/
theorem lin_rows {codes c : Codes} {x : LinSized} (h : linSized s L T codes = some (x, c))
    (N : LinNums s L T) :
    FewRows x.shape.fold.u ∧ FewRows x.shape.omega ∧ FewRows x.shape.w ∧
      FewRows x.shape.sharedSplit ∧ FewRows x.input.shape := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, _, _, r1, r2, r3, r4, r5,
    _⟩ := linSized_parts h
  exact ⟨.of_same r1 (rows_linU N), .of_same r2 (rows_linOmega N), .of_same r3 (rows_linW N hv),
    .of_same r4 rows_linSplitMsg, .of_same r5 (rows_linInput N)⟩

end

/-- The least power of two that is at least a number of few rows. -/
theorem up_le {r : Nat} (h : r ≤ 2 ^ 128) :
    (if r != 0 then pow2AtLeast r else 0) ≤ 2 ^ 128 := by
  split
  · exact Nat.pow_le_pow_right (by decide) (clog2_pow_le h)
  · exact Nat.zero_le _

/-- A sum of at most three numbers. -/
theorem sumT_le3 {l : List Nat} {B : Nat} (hl : l.length ≤ 3) (h : ∀ a ∈ l, a ≤ B) :
    sumT l ≤ 3 * B := by
  unfold sumT
  rw [foldl_add, Nat.zero_add]
  match l, hl, h with
  | [], _, _ => simp
  | [a], _, h =>
    have := h a (by simp)
    simp only [List.sum_cons, List.sum_nil]
    omega
  | [a, b], _, h =>
    have := h a (by simp)
    have := h b (by simp)
    simp only [List.sum_cons, List.sum_nil]
    omega
  | [a, b, c], _, h =>
    have := h a (by simp)
    have := h b (by simp)
    have := h c (by simp)
    simp only [List.sum_cons, List.sum_nil]
    omega
  | _ :: _ :: _ :: _ :: _, hl, _ => simp at hl; omega

/-- **The row variables of a group of at most three messages with few rows.** -/
theorem linGroupBits_le {ms : List OracleShape} (hl : ms.length ≤ 3)
    (h : ∀ m ∈ ms, FewRows m) :
    (linGroupBits ms).1 ≤ 131 ∧ (linGroupBits ms).2 ≤ 131 := by
  have g : 3 * 2 ^ 128 ≤ 2 ^ 131 := by norm_num
  have a : clog2 (sumT (ms.map fun m =>
      if m.mainRows != 0 then pow2AtLeast m.mainRows else 0)) ≤ 131 := by
    refine clog2_pow_le ((sumT_le3 (by rw [List.length_map]; exact hl) ?_).trans g)
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
    exact up_le (h m hm).1
  have b : clog2 (sumT (ms.map fun m =>
      if m.maskRows != 0 then pow2AtLeast m.maskRows else 0)) ≤ 131 := by
    refine clog2_pow_le ((sumT_le3 (by rw [List.length_map]; exact hl) ?_).trans g)
    intro y hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
    exact up_le (h m hm).2
  constructor
  · show max (max _ _) 1 ≤ 131
    exact Nat.max_le.2 ⟨Nat.max_le.2 ⟨a, b⟩, by decide⟩
  · exact b

end OnBytes.Params
