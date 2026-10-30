-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPage174.lean: the partial code of a leaf query on a symbol of a stored table in the
programs' format. (174: the number under which the format hashes a leaf of a stored table.)

Definitions that compute, with their laws.
A partial code (`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings,
injectively, with a parser. A leaf query (`LeafIn`, Compile/Batch/Oracles.lean) is the typed query
that hashes one leaf of a tree over oracles: a body and a salt. Run/CodingPage164.lean has the code
of the leaf queries whose body is a symbol of a prover's oracle. Here the body is a symbol of an
encoded index (`L.Symbol`): what a leaf of a stored table holds.

Written after the text of `Run.PQ.leafX` (Run/PlanQXRun.lean), which spells such a query as a call
of the format's hash, and after the pattern of Run/CodingPage164.lean; not against the format page.
As there, the start of a leaf rides in the typed salt: the first 256 bits of the typed salt stand
for the call's start, the rest is the file's salt. A stored leaf starts from a constant of the
instance (the configuration's digest), and `leafX` has no call where the typed salt begins
otherwise; so this code does not write such a query.

Main names:
  `t174`: the 16 bits of the number 174, as they stand in the first word of a call's label;
    `t174_differs`: it is none of the four tags of Run/CodingTag.lean.
  `tag_low`: the low 16 bits of the word n + 65536 x are those of the word n.
  `pCol W`: a column of exactly W words, as a list.
  `pStored a salt`, a `PCode (ℕ × List UInt64)`: a symbol (position, column) of a stored table of
    depth a, for leaves with a salt of `salt` bytes in the file: the two words of the label, the
    column, the fill. `pStored_some`, `pStored_put`: it writes exactly where `storedOK` holds, and
    what it writes is `storedStr`. `pStored_tag`: every string of it begins with `t174`.
  `pLeafS cfg n p : PCode (LeafIn L)`: written exactly if the body is a symbol of an encoded index,
    p writes it, the typed salt has 256 + n bits, and its first 256 bits are the bytes `cfg`. The
    string: `pre33`, the salt's first 256 bits, p's string, the salt's last n bits.
  `pLeafS_put`, `pLeafS_some`: what it writes, and where. `pLeafS_facts`: if p's strings begin with
    `t174`, every string of `pLeafS cfg n p` has the tag `t174` and begins with no byte other than
    0.

Limits: that the strings are those of `Run.PQ.leafX` is not shown in this file (Run/PageXFit.lean:
`storedX_fit`). The code writes fewer queries than `leafX` spells: not those with a salt of another
length, with a column of 2^24 words or more, or with a position from 2^64 - 2^a on; and none at all
if the word with the salt's number of words does not fit 64 bits (`storedOK`). That a string written
here lies in the domain of the format's hash (`Fmt.hDom`, Fmt/Rules23.lean) is not asked and not
claimed. Nor is it asked that a position is below 2^a: a symbol with the position 2^a + x is written
as the call with the index 2^(a+1) + x, the string of a leaf of a tree one level deeper. This file
says nothing on a hash.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage
import Run.PageQChain

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

/-! ## The tag -/

/-- The first 16 bits of a word's spelling are the bits of its two lowest bytes. -/
theorem take16_u64 (y : UInt64) :
    (bytesToBits (_root_.Fmt.u64 y)).take 16 =
      bitsOfByte y.toUInt8 ++ bitsOfByte (y >>> 8).toUInt8 := by
  have e : bytesToBits (_root_.Fmt.u64 y) =
      (bitsOfByte y.toUInt8 ++ bitsOfByte (y >>> 8).toUInt8) ++
        bitsL [(y >>> 16).toUInt8, (y >>> 24).toUInt8, (y >>> 32).toUInt8, (y >>> 40).toUInt8,
          (y >>> 48).toUInt8, (y >>> 56).toUInt8] := by
    rw [List.append_assoc]
    rfl
  rw [e]
  exact List.take_left' (by rw [List.length_append, length_bitsOfByte, length_bitsOfByte])

/-- The low 16 bits of the word n + 65536 x are those of the word n, for all numbers n and x
(both words are taken modulo 2^64). -/
theorem tag_low (n x : ℕ) :
    (bytesToBits (_root_.Fmt.u64n (n + 65536 * x))).take 16 =
      (bytesToBits (_root_.Fmt.u64n n)).take 16 := by
  unfold _root_.Fmt.u64n
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
def t174 : List Bool := (bytesToBits (_root_.Fmt.u64n 174)).take 16

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

/-- A column of exactly W words, as a list: the words one behind the other. A list of another
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
      col.length = W ∧ s = bytesToBits (_root_.Fmt.colBytes col)
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
          show _ = bytesToBits (_root_.Fmt.cat ((x :: l).map _root_.Fmt.u64))
          rw [List.map_cons, _root_.Fmt.cat_cons, bytesToBits_append]
          rfl

/-- A list is written by `pCol` at its own length. -/
theorem pCol_some : ∀ col : List UInt64,
    (pCol col.length).put col = some (bytesToBits (_root_.Fmt.colBytes col))
  | [] => rfl
  | x :: l => by
      show (pU64.put x).bind (fun u => ((pCol l.length).put l).map (u ++ ·)) = _
      rw [pU64_put, pCol_some l]
      show some (bytesToBits (_root_.Fmt.u64 x) ++ bytesToBits (_root_.Fmt.colBytes l)) =
        some (bytesToBits (_root_.Fmt.cat ((x :: l).map _root_.Fmt.u64)))
      rw [List.map_cons, _root_.Fmt.cat_cons, bytesToBits_append]
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
  if W < 2 ^ 24 then some (174 + 65536 * _root_.Fmt.leafPlace 0 W s8) else none

/-- The number of a column's words, read off the label's first word. -/
def widthOfWord (s8 v : ℕ) : Option ℕ :=
  if v = 174 + 65536 * _root_.Fmt.leafPlace 0 (v / 2 ^ 32 % 2 ^ 24) s8 then
    some (v / 2 ^ 32 % 2 ^ 24)
  else none

/-- The reading undoes the writing. -/
theorem widthOfWord_widthTo (s8 W v : ℕ) (h : widthTo s8 W = some v) :
    widthOfWord s8 v = some W := by
  unfold widthTo at h
  unfold widthOfWord
  by_cases hW : W < 2 ^ 24
  · rw [if_pos hW] at h
    rw [← Option.some.inj h]
    have e : (174 + 65536 * _root_.Fmt.leafPlace 0 W s8) / 2 ^ 32 % 2 ^ 24 = W := by
      unfold _root_.Fmt.leafPlace
      omega
    rw [e, if_pos rfl]
  · rw [if_neg hW] at h
    cases h

/-- The writing undoes the reading. -/
theorem widthTo_widthOfWord (s8 v W : ℕ) (h : widthOfWord s8 v = some W) :
    widthTo s8 W = some v := by
  unfold widthOfWord at h
  unfold widthTo
  by_cases hv : v = 174 + 65536 * _root_.Fmt.leafPlace 0 (v / 2 ^ 32 % 2 ^ 24) s8
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
def fillS (W salt : ℕ) : List Bool :=
  bytesToBits (_root_.Fmt.zeroBytes (_root_.Fmt.fillLen W salt))

/-- The four fields: the number of the column's words, the position, the column, the fill. -/
def pStored4 (a salt : ℕ) : PCode (ℕ × ℕ × List UInt64 × Unit) :=
  (pW (salt / 8)).cons 64 (pW_len _) fun W =>
    (pPos a).cons 64 (pPos_len a) fun _ =>
      (pCol W).cons (64 * W) (pCol_len W) fun _ => pUnit (fillS W salt)

/-- The four fields, back to a symbol: the column must have the number of words that is named. -/
def symOf (z : ℕ × ℕ × List UInt64 × Unit) : Option (ℕ × List UInt64) :=
  if z.2.2.1.length = z.1 then some (z.2.1, z.2.2.1) else none

/-- A symbol (position, column) of a stored table of depth a, for leaves whose salt in the file
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
  bytesToBits (_root_.Fmt.label 174 (_root_.Fmt.leafPlace 0 y.2.length (salt / 8)) (2 ^ a + y.1)) ++
    bytesToBits
      (_root_.Fmt.colBytes y.2 ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length salt))

/-- The test: the column has fewer than 2^24 words, and the label's two words are below 2^64. -/
def storedOK (a salt : ℕ) (y : ℕ × List UInt64) : Prop :=
  y.2.length < 2 ^ 24 ∧ 174 + 65536 * _root_.Fmt.leafPlace 0 y.2.length (salt / 8) < 2 ^ 64 ∧
    2 ^ a + y.1 < 2 ^ 64

/-- Where the test holds, `pStored` writes the symbol's string. -/
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
  unfold storedStr _root_.Fmt.label fillS
  simp only [bytesToBits_append, List.append_assoc]

/-- What `pStored` writes: the test holds, and the string is the symbol's string. -/
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
    have h0 : (if w < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n w)) else none) = some u := hw
    rw [if_neg hn] at h0
    cases h0
  have k1 : y.2.length < 2 ^ 24 ∧
      w1 = 174 + 65536 * _root_.Fmt.leafPlace 0 y.2.length (salt / 8) := by
    have h0 : (if y.2.length < 2 ^ 24 then
        some (174 + 65536 * _root_.Fmt.leafPlace 0 y.2.length (salt / 8)) else none) =
        some w1 := hw1
    by_cases hW : y.2.length < 2 ^ 24
    · rw [if_pos hW] at h0
      exact ⟨hW, (Option.some.inj h0).symm⟩
    · rw [if_neg hW] at h0
      cases h0
  have k2 : w2 = 2 ^ a + y.1 := (Option.some.inj hw2).symm
  have ok : storedOK a salt y := ⟨k1.1, k1.2 ▸ lt64 w1 u1 hp1, k2 ▸ lt64 w2 u2 hp2⟩
  exact ⟨ok, Option.some.inj (h.symm.trans (pStored_some a salt y ok))⟩

/-- Every string of `pStored` begins with the 16 bits of the number 174. -/
theorem pStored_tag (a salt : ℕ) (y : ℕ × List UInt64) (m : List Bool)
    (h : (pStored a salt).put y = some m) : 16 ≤ m.length ∧ m.take 16 = t174 := by
  rw [(pStored_put a salt y m h).2]
  unfold storedStr _root_.Fmt.label
  rw [bytesToBits_append, List.append_assoc]
  refine ⟨by rw [List.length_append, length_u64n]; omega, ?_⟩
  rw [take16 _ _ (by rw [length_u64n]; omega)]
  exact tag_low 174 _

/-! ## The leaf query -/

variable {I X : Type} {L : BatchProtocol I X}

/-- A leaf query whose body is a symbol of an encoded index, as (symbol, salt). -/
def leafSelS (q : LeafIn L) : Option (L.Symbol × List Bool) :=
  match q.body with
  | some (.inl s) => some (s, q.salt)
  | _ => none

/-- The leaf query on a symbol of an encoded index, with a salt. -/
def leafMkS (x : L.Symbol × List Bool) : LeafIn L := ⟨some (.inl x.1), x.2⟩

/-- Reading the query that was made of (symbol, salt) gives these back. -/
theorem leafSelS_mk (x : L.Symbol × List Bool) : leafSelS (leafMkS x) = some x := rfl

/-- The query that is made of what was read is the query itself. -/
theorem leafMkS_sel (q : LeafIn L) (x : L.Symbol × List Bool) (h : leafSelS q = some x) :
    leafMkS x = q := by
  obtain ⟨body, salt⟩ := q
  rcases body with _ | (s | _)
  · cases h
  · rw [← Option.some.inj h]
    rfl
  · cases h

/-- The test of `Run.PQ.leafX`: the first 256 bits of the typed salt are the bytes `cfg`. -/
def startIs (cfg : ByteArray) (q : LeafIn L) : Bool := bitsToBytes (q.salt.take 256) == cfg

/-- A leaf query on a symbol of an encoded index. Written exactly if the body is such a symbol,
p writes it, the typed salt has 256 + n bits, and its first 256 bits are the bytes `cfg`. The
string: the 33 bytes with which a call with a digest of 32 bytes begins; the salt's first 256 bits
(the call's start); p's string; the salt's last n bits. -/
def pLeafS (cfg : ByteArray) (n : ℕ) (p : PCode L.Symbol) : PCode (LeafIn L) :=
  ((pSalted pre33 n p).via leafSelS leafMkS leafSelS_mk leafMkS_sel).sub (startIs cfg)

/-- What `pLeafS` writes. -/
theorem pLeafS_put (cfg : ByteArray) (n : ℕ) (p : PCode L.Symbol) (q : LeafIn L) (s : List Bool)
    (h : (pLeafS cfg n p).put q = some s) :
    ∃ y m, q.body = some (.inl y) ∧ startIs cfg q = true ∧ q.salt.length = 256 + n ∧
      p.put y = some m ∧ s = pre33 ++ (q.salt.take 256 ++ (m ++ q.salt.drop 256)) := by
  have h0 : (if startIs cfg q = true then (leafSelS q).bind (pSalted pre33 n p).put else none) =
      some s := h
  by_cases hc : startIs cfg q = true
  · rw [if_pos hc] at h0
    obtain ⟨body, salt⟩ := q
    rcases body with _ | (y | _)
    · cases h0
    · have h1 : (if salt.length = 256 + n then
          (p.put y).map (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) else none) =
          some s := h0
      by_cases hl : salt.length = 256 + n
      · rw [if_pos hl] at h1
        cases hm : p.put y with
        | none => rw [hm] at h1; cases h1
        | some m =>
            rw [hm] at h1
            exact ⟨y, m, rfl, hc, hl, hm, (Option.some.inj h1).symm⟩
      · rw [if_neg hl] at h1
        cases h1
    · cases h0
  · rw [if_neg hc] at h0
    cases h0

/-- Where the four conditions hold, `pLeafS` writes. -/
theorem pLeafS_some (cfg : ByteArray) (n : ℕ) (p : PCode L.Symbol) (y : L.Symbol) (salt m : List Bool)
    (hc : startIs (L := L) cfg ⟨some (.inl y), salt⟩ = true) (hl : salt.length = 256 + n)
    (hm : p.put y = some m) :
    (pLeafS cfg n p).put ⟨some (.inl y), salt⟩ =
      some (pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) := by
  show (if startIs (L := L) cfg ⟨some (.inl y), salt⟩ = true then
    (if salt.length = 256 + n then
      (p.put y).map (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))) else none)
    else none) = _
  rw [if_pos hc, if_pos hl, hm]
  rfl

/-- The tag and the first byte. If every string of p has at least 16 bits and begins with t174,
every string of `pLeafS cfg n p` has the tag t174, and begins with no byte other than 0. -/
theorem pLeafS_facts (cfg : ByteArray) (n : ℕ) (p : PCode L.Symbol)
    (hp : ∀ y m, p.put y = some m → 16 ≤ m.length ∧ m.take 16 = t174)
    (q : LeafIn L) (s : List Bool) (h : (pLeafS cfg n p).put q = some s) :
    tag16 s = t174 ∧ ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s := by
  obtain ⟨y, m, -, -, hl, hm, rfl⟩ := pLeafS_put cfg n p q s h
  exact ⟨(tag16_pre33 _ m _ (by rw [List.length_take, hl]; omega) (hp y m hm).1).trans
    (hp y m hm).2, fun e he => pre33_not_prefix e he _⟩

end Run
