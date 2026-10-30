-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Tag174.lean: the tag of the stored leaves' number 174, and the code of a stored
symbol.

The declarations are those of OnBytes/Tie/Page174.lean, taken over as text by a program:
`take16_u64`, `tag_low`, `t174`, `t174_differs`; from `nilTo` to `pCol_len`; from `widthTo` to
`pPos_len`; `fillS`, `pStored4`, `symOf`, `pStored`, `storedStr`, `storedOK`, `pStored_some`,
`pStored_put`, `pStored_tag`. None of these names an interface. They are said again here, in the
sibling's namespace.
Not said again: `leafSelS`, `leafMkS`, `startIs`, `pLeafS` and its lemmas. With a leaf's body a
parameter there is one code of bodies: Run/CodingPage.lean's own `pLeaf`, under a test on the
start.

-/
import Run.CodingPage
import Run.PageQChain

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Iop _root_.Compile _root_.Compile.Batch _root_.Run

/-! ## The tag -/

/-- The first 16 bits of a word's spelling are the bits of its two lowest bytes. -/
theorem take16_u64 (y : UInt64) :
    (bytesToBits (Fmt.u64 y)).take 16 = bitsOfByte y.toUInt8 ++ bitsOfByte (y >>> 8).toUInt8 := by
  have e : bytesToBits (Fmt.u64 y) =
      (bitsOfByte y.toUInt8 ++ bitsOfByte (y >>> 8).toUInt8) ++
        bitsL [(y >>> 16).toUInt8, (y >>> 24).toUInt8, (y >>> 32).toUInt8, (y >>> 40).toUInt8,
          (y >>> 48).toUInt8, (y >>> 56).toUInt8] := by
    rw [List.append_assoc]
    rfl
  rw [e]
  exact List.take_left' (by rw [List.length_append, length_bitsOfByte, length_bitsOfByte])

/-- **The low 16 bits of the word n + 65536 x are those of the word n**, for all numbers n and x
(both words are taken modulo 2^64). -/
theorem tag_low (n x : ℕ) :
    (bytesToBits (Fmt.u64n (n + 65536 * x))).take 16 = (bytesToBits (Fmt.u64n n)).take 16 := by
  unfold Fmt.u64n
  rw [take16_u64, take16_u64]
  have e1 : (UInt64.ofNat (n + 65536 * x)).toUInt8 = (UInt64.ofNat n).toUInt8 := by
    apply UInt8.toNat_inj.1
    rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  have e2 : (UInt64.ofNat (n + 65536 * x) >>> 8).toUInt8 = (UInt64.ofNat n >>> 8).toUInt8 := by
    apply UInt8.toNat_inj.1
    rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    show ((n + 65536 * x) % 2 ^ 64) >>> 8 % 2 ^ 8 = (n % 2 ^ 64) >>> 8 % 2 ^ 8
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]

/-- The 16 bits of the number 174, as they stand in the first word of a call's label. -/
def t174 : List Bool := (bytesToBits (Fmt.u64n 174)).take 16

/-- The tag of the stored leaves' number is none of the four tags of Run/CodingTag.lean. -/
theorem t174_differs : t174 ≠ t160 ∧ t174 ≠ t162 ∧ t174 ≠ t164 ∧ t174 ≠ t166 := by
  decide +kernel

/-! ## A column of a given number of words -/

/-- The empty list, as the one point. -/
def nilTo : List UInt64 → Option Unit
  | [] => some ()
  | _ :: _ => none

/-- A list that is not empty, as its first word and the rest. -/
def consTo : List UInt64 → Option (UInt64 × List UInt64)
  | [] => none
  | x :: l => some (x, l)

/-- **A column of exactly W words**, as a list: the words one behind the other. A list of another
length is not written. -/
def pCol : ℕ → PCode (List UInt64)
  | 0 => (pUnit []).pull nilTo (fun _ => some [])
      (fun b _ h => by cases b with
        | nil => rfl
        | cons _ _ => cases h)
      (fun _ b h => by rw [← Option.some.inj h]; rfl)
  | W + 1 => (pU64.cons 64 pU64_len fun _ => pCol W).pull consTo (fun y => some (y.1 :: y.2))
      (fun b a h => by cases b with
        | nil => cases h
        | cons _ _ => rw [← Option.some.inj h])
      (fun a b h => by rw [← Option.some.inj h]; rfl)

/-- What `pCol W` writes: the list has W words, and the string is the bits of the column's bytes. -/
theorem pCol_put :
    ∀ (W : ℕ) (col : List UInt64) (s : List Bool), (pCol W).put col = some s →
      col.length = W ∧ s = bytesToBits (Fmt.colBytes col)
  | 0, col, s, h => by
      obtain ⟨u, hu, hs⟩ := PCode.pull_put _ _ _ _ _ col s h
      cases col with
      | nil => exact ⟨rfl, (Option.some.inj hs).symm⟩
      | cons _ _ => cases hu
  | W + 1, col, s, h => by
      obtain ⟨y, hy, hs⟩ := PCode.pull_put _ _ _ _ _ col s h
      cases col with
      | nil => cases hy
      | cons x l =>
          rw [← Option.some.inj hy] at hs
          obtain ⟨u, v, hu, hv, rfl⟩ :=
            PCode.cons_put pU64 64 pU64_len (fun _ => pCol W) (x, l) s hs
          rw [pU64_put] at hu
          obtain ⟨h1, h2⟩ := pCol_put W l v hv
          refine ⟨by rw [List.length_cons, h1], ?_⟩
          rw [← Option.some.inj hu, h2]
          show _ = bytesToBits (Fmt.cat ((x :: l).map Fmt.u64))
          rw [List.map_cons, Fmt.cat_cons, bytesToBits_append]
          rfl

/-- A list is written by `pCol` at its own length. -/
theorem pCol_some : ∀ col : List UInt64,
    (pCol col.length).put col = some (bytesToBits (Fmt.colBytes col))
  | [] => rfl
  | x :: l => by
      show (pU64.put x).bind (fun u => ((pCol l.length).put l).map (u ++ ·)) = _
      rw [pU64_put, pCol_some l]
      show some (bytesToBits (Fmt.u64 x) ++ bytesToBits (Fmt.colBytes l)) =
        some (bytesToBits (Fmt.cat ((x :: l).map Fmt.u64)))
      rw [List.map_cons, Fmt.cat_cons, bytesToBits_append]
      rfl

/-- Every string of `pCol W` has 64 W bits. -/
theorem pCol_len : ∀ W : ℕ, (pCol W).Len (64 * W)
  | 0 => PCode.pull_len _ _ _ _ _ _ (pUnit_len [])
  | W + 1 => fun b s h => by
      have := PCode.pull_len _ _ _ _ _ _
        (PCode.cons_len pU64 64 pU64_len (fun _ => pCol W) (64 * W) fun _ => pCol_len W) b s h
      omega

/-! ## The two words of the label -/

/-- The number of a column's words, as the label's first word; s8: the number of the words of the
file's salt. None from 2^24 words on. -/
def widthTo (s8 W : ℕ) : Option ℕ :=
  if W < 2 ^ 24 then some (174 + 65536 * Fmt.leafPlace 0 W s8) else none

/-- The number of a column's words, read off the label's first word. -/
def widthOfWord (s8 v : ℕ) : Option ℕ :=
  if v = 174 + 65536 * Fmt.leafPlace 0 (v / 2 ^ 32 % 2 ^ 24) s8 then some (v / 2 ^ 32 % 2 ^ 24)
  else none

/-- The reading undoes the writing. -/
theorem widthOfWord_widthTo (s8 W v : ℕ) (h : widthTo s8 W = some v) :
    widthOfWord s8 v = some W := by
  unfold widthTo at h
  unfold widthOfWord
  by_cases hW : W < 2 ^ 24
  · rw [if_pos hW] at h
    rw [← Option.some.inj h]
    have e : (174 + 65536 * Fmt.leafPlace 0 W s8) / 2 ^ 32 % 2 ^ 24 = W := by
      unfold Fmt.leafPlace
      omega
    rw [e, if_pos rfl]
  · rw [if_neg hW] at h
    cases h

/-- The writing undoes the reading. -/
theorem widthTo_widthOfWord (s8 v W : ℕ) (h : widthOfWord s8 v = some W) :
    widthTo s8 W = some v := by
  unfold widthOfWord at h
  unfold widthTo
  by_cases hv : v = 174 + 65536 * Fmt.leafPlace 0 (v / 2 ^ 32 % 2 ^ 24) s8
  · rw [if_pos hv] at h
    rw [← Option.some.inj h, if_pos (Nat.mod_lt _ (by omega)), ← hv]
  · rw [if_neg hv] at h
    cases h

/-- The label's first word, as a code of the number of the column's words. -/
def pW (s8 : ℕ) : PCode ℕ :=
  pWord.pull (widthTo s8) (widthOfWord s8) (widthOfWord_widthTo s8) (widthTo_widthOfWord s8)

/-- Every string of `pW` has 64 bits. -/
theorem pW_len (s8 : ℕ) : (pW s8).Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

/-- A position, read off the label's second word. -/
def posOfWord (a v : ℕ) : Option ℕ := if 2 ^ a ≤ v then some (v - 2 ^ a) else none

/-- The label's second word, 2^a + the position, as a code of the position. -/
def pPos (a : ℕ) : PCode ℕ :=
  pWord.pull (fun x => some (2 ^ a + x)) (posOfWord a)
    (fun b v h => by
      rw [← Option.some.inj h]
      unfold posOfWord
      rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left])
    (fun v b h => by
      unfold posOfWord at h
      by_cases hv : 2 ^ a ≤ v
      · rw [if_pos hv] at h
        rw [← Option.some.inj h]
        show some (2 ^ a + (v - 2 ^ a)) = some v
        rw [Nat.add_sub_cancel' hv]
      · rw [if_neg hv] at h
        cases h)

/-- Every string of `pPos` has 64 bits. -/
theorem pPos_len (a : ℕ) : (pPos a).Len 64 := PCode.pull_len _ _ _ _ _ 64 pWord_len

/-! ## A symbol of a stored table -/

/-- The fill between a column of W words and a salt of `salt` bytes, as bits. -/
def fillS (W salt : ℕ) : List Bool := bytesToBits (Fmt.zeroBytes (Fmt.fillLen W salt))

/-- The four fields: the number of the column's words, the position, the column, the fill. -/
def pStored4 (a salt : ℕ) : PCode (ℕ × ℕ × List UInt64 × Unit) :=
  (pW (salt / 8)).cons 64 (pW_len _) fun W =>
    (pPos a).cons 64 (pPos_len a) fun _ =>
      (pCol W).cons (64 * W) (pCol_len W) fun _ => pUnit (fillS W salt)

/-- The four fields, back to a symbol: the column must have the number of words that is named. -/
def symOf (z : ℕ × ℕ × List UInt64 × Unit) : Option (ℕ × List UInt64) :=
  if z.2.2.1.length = z.1 then some (z.2.1, z.2.2.1) else none

/-- **A symbol (position, column) of a stored table of depth a**, for leaves whose salt in the file
has `salt` bytes: the word 174 + 2^16 (place), where the place holds the tree's number 0, the
number of the column's words and the number of the salt's words; the word 2^a + position; the
column; the fill. Written exactly where `storedOK` holds. -/
def pStored (a salt : ℕ) : PCode (ℕ × List UInt64) :=
  (pStored4 a salt).pull (fun y => some (y.2.length, y.1, y.2, ())) symOf
    (fun b z h => by
      rw [← Option.some.inj h]
      exact if_pos rfl)
    (fun z b h => by
      obtain ⟨W, x, col, ⟨⟩⟩ := z
      unfold symOf at h
      by_cases hz : col.length = W
      · rw [if_pos hz] at h
        rw [← Option.some.inj h]
        show some (col.length, x, col, ()) = some (W, x, col, ())
        rw [hz]
      · rw [if_neg hz] at h
        cases h)

/-- The string of a symbol: the bits of the label and of the column with its fill. -/
def storedStr (a salt : ℕ) (y : ℕ × List UInt64) : List Bool :=
  bytesToBits (Fmt.label 174 (Fmt.leafPlace 0 y.2.length (salt / 8)) (2 ^ a + y.1)) ++
    bytesToBits (Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length salt))

/-- The test: the column has fewer than 2^24 words, and the label's two words are below 2^64. -/
def storedOK (a salt : ℕ) (y : ℕ × List UInt64) : Prop :=
  y.2.length < 2 ^ 24 ∧ 174 + 65536 * Fmt.leafPlace 0 y.2.length (salt / 8) < 2 ^ 64 ∧
    2 ^ a + y.1 < 2 ^ 64

/-- **Where the test holds, `pStored` writes the symbol's string.** -/
theorem pStored_some (a salt : ℕ) (y : ℕ × List UInt64) (h : storedOK a salt y) :
    (pStored a salt).put y = some (storedStr a salt y) := by
  obtain ⟨h1, h2, h3⟩ := h
  show ((widthTo (salt / 8) y.2.length).bind pWord.put).bind (fun u =>
      (((some (2 ^ a + y.1)).bind pWord.put).bind (fun u' =>
        (((pCol y.2.length).put y.2).bind (fun u'' =>
          (some (fillS y.2.length salt)).map (u'' ++ ·))).map (u' ++ ·))).map (u ++ ·)) = _
  unfold widthTo
  rw [if_pos h1, pCol_some]
  show ((pWord.put _).bind _) = _
  rw [pWord_put _ h2]
  show (((pWord.put _).bind _).map _) = _
  rw [pWord_put _ h3]
  show some _ = some _
  unfold storedStr Fmt.label fillS
  simp only [bytesToBits_append, List.append_assoc]

/-- **What `pStored` writes**: the test holds, and the string is the symbol's string. -/
theorem pStored_put (a salt : ℕ) (y : ℕ × List UInt64) (m : List Bool)
    (h : (pStored a salt).put y = some m) : storedOK a salt y ∧ m = storedStr a salt y := by
  obtain ⟨z, hz, hm⟩ := PCode.pull_put _ _ _ _ _ y m h
  rw [← Option.some.inj hz] at hm
  obtain ⟨u1, v1, hu1, hv1, rfl⟩ := PCode.cons_put _ _ _ _ _ m hm
  obtain ⟨u2, v2, hu2, -, rfl⟩ := PCode.cons_put _ _ _ _ _ v1 hv1
  obtain ⟨w1, hw1, hp1⟩ := PCode.pull_put _ _ _ _ _ _ u1 hu1
  obtain ⟨w2, hw2, hp2⟩ := PCode.pull_put _ _ _ _ _ _ u2 hu2
  have lt64 : ∀ (w : ℕ) (u : List Bool), pWord.put w = some u → w < 2 ^ 64 := fun w u hw => by
    by_contra hn
    have h0 : (if w < 2 ^ 64 then some (bytesToBits (Fmt.u64n w)) else none) = some u := hw
    rw [if_neg hn] at h0
    cases h0
  have k1 : y.2.length < 2 ^ 24 ∧ w1 = 174 + 65536 * Fmt.leafPlace 0 y.2.length (salt / 8) := by
    have h0 : (if y.2.length < 2 ^ 24 then
        some (174 + 65536 * Fmt.leafPlace 0 y.2.length (salt / 8)) else none) = some w1 := hw1
    by_cases hW : y.2.length < 2 ^ 24
    · rw [if_pos hW] at h0
      exact ⟨hW, (Option.some.inj h0).symm⟩
    · rw [if_neg hW] at h0
      cases h0
  have k2 : w2 = 2 ^ a + y.1 := (Option.some.inj hw2).symm
  have ok : storedOK a salt y := ⟨k1.1, k1.2 ▸ lt64 w1 u1 hp1, k2 ▸ lt64 w2 u2 hp2⟩
  exact ⟨ok, Option.some.inj (h.symm.trans (pStored_some a salt y ok))⟩

/-- **Every string of `pStored` begins with the 16 bits of the number 174.** -/
theorem pStored_tag (a salt : ℕ) (y : ℕ × List UInt64) (m : List Bool)
    (h : (pStored a salt).put y = some m) : 16 ≤ m.length ∧ m.take 16 = t174 := by
  rw [(pStored_put a salt y m h).2]
  unfold storedStr Fmt.label
  rw [bytesToBits_append, List.append_assoc]
  refine ⟨by rw [List.length_append, length_u64n]; omega, ?_⟩
  rw [take16 _ _ (by rw [length_u64n]; omega)]
  exact tag_low 174 _

end TypedOracleCompiler.Run

#print axioms TypedOracleCompiler.Run.tag_low
#print axioms TypedOracleCompiler.Run.t174_differs
#print axioms TypedOracleCompiler.Run.pStored_put
#print axioms TypedOracleCompiler.Run.pStored_tag
