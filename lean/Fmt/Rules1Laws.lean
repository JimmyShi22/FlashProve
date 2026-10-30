-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules1Laws.lean: the format page's known answers "a word and its try" (R6.3; the page prints
them in its section on drawing) and "eight bytes as the spelling of an element" (R1.3) as theorems;
and every reader undoes its spelling, at any place in a longer string, so every spelling is one to
one, each under the conditions named in 3.

A spelling is an encoding of values as bytes (`sp : α → ByteArray`). A reader (`Rd α`,
Fmt/Rules1.lean) is a decoder: from a string of bytes and a place (an offset in bytes) it gives a
value and the place behind it, or it refuses (`none`).

Why. A test (#guard) is an evaluation made while the file compiles, and leaves no declaration. What
is to be quoted as proved stands here.

Sources. Section 1 of the format page (docs/format/FORMAT.md);
this file has not been held against the page as it ships,
and may differ from it. The ten known
answers of R6.3 stand in the page's section on drawing. No Mathlib; the file imports Fmt/Rules1.lean
alone.

1. What the file contains. Theorems.
   `Undoes r sp ok` (a definition).

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   `try_two_0` to `try_one_max1`: the ten known answers "a word and its try" (R6.3; the page prints
     them in its section on drawing), by evaluation in the kernel.
   `spell_two_0` to `spell_one_max`: the nine known answers "eight bytes as the spelling of an
     element" (R1.3), in the same way.
   `undoes_word`, `undoes_elt` (ok: below p), `undoes_ext` (ok: all three below p), `undoes_bool`,
     `undoes_text` (ok: shorter than 2^64 bytes), `undoes_name` (ok: also a name), `undoes_digest`
     (ok: 32 bytes), `undoes_enum` (ok: the number is below 2^64 and is read back), `undoes_bytes`
     (ok: n bytes).
   `undoes_pair` (ok: both parts ok), `undoes_many` (asked, as `hl`: each value ok), `undoes_list`
     (ok: fewer than 2^64 values, each ok; asked, as `hp`: the spelling of a value with ok has at
     least one byte, since R1.9 holds the number of values against the bytes left): from the parts'
     laws.
   `whole_of_undoes`: so, under `Undoes r sp ok` and ok x, the reader on the whole string sp x gives
     x.
   `inj_of_undoes`: so, under `Undoes r sp ok`, sp is one to one on ok.

4. What is not claimed. The other law: that whatever a reader accepts is the spelling of what it
returns (so that each value has one spelling: R1.3's last sentence). It is in Fmt/Rules1Only.lean.
Nothing on what the page leaves open (see the head of Fmt/Rules1.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1

namespace Fmt

/-! ## 1. The known answers -/

theorem try_two_0 : Fld.two.tryWord 0 = some 0 := by decide
theorem try_two_last : Fld.two.tryWord 18446744069414584320 = some 18446744069414584320 := by decide
theorem try_two_p : Fld.two.tryWord 18446744069414584321 = none := by decide
theorem try_two_max : Fld.two.tryWord 18446744073709551615 = none := by decide
theorem try_one_0 : Fld.one.tryWord 0 = some 0 := by decide
theorem try_one_last : Fld.one.tryWord 2305843009213693950 = some 2305843009213693950 := by decide
theorem try_one_p : Fld.one.tryWord 2305843009213693951 = none := by decide
theorem try_one_next : Fld.one.tryWord 2305843009213693952 = some 0 := by decide
theorem try_one_max : Fld.one.tryWord 18446744073709551615 = none := by decide
theorem try_one_max1 : Fld.one.tryWord 18446744073709551614 = some 2305843009213693950 := by decide

theorem spell_two_0 : whole (rdElt .two) (unhex "0000000000000000") = some 0 := by decide +kernel
theorem spell_two_last :
    whole (rdElt .two) (unhex "00000000ffffffff") = some 18446744069414584320 := by decide +kernel
theorem spell_two_p : whole (rdElt .two) (unhex "01000000ffffffff") = none := by decide +kernel
theorem spell_two_max : whole (rdElt .two) (unhex "ffffffffffffffff") = none := by decide +kernel
theorem spell_one_0 : whole (rdElt .one) (unhex "0000000000000000") = some 0 := by decide +kernel
theorem spell_one_last :
    whole (rdElt .one) (unhex "feffffffffffff1f") = some 2305843009213693950 := by decide +kernel
theorem spell_one_p : whole (rdElt .one) (unhex "ffffffffffffff1f") = none := by decide +kernel
theorem spell_one_next : whole (rdElt .one) (unhex "0000000000000020") = none := by decide +kernel
theorem spell_one_max : whole (rdElt .one) (unhex "ffffffffffffffff") = none := by decide +kernel

/-! ## 2. A word -/

theorem getElem_mod256 (v : BitVec 64) (k : Nat) (h : k < 64) :
    (v % 256#64)[k] = (decide (k < 8) && v[k]) := by
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  simp only [BitVec.getLsbD, BitVec.toNat_umod]
  exact Nat.testBit_mod_two_pow v.toNat 8 k

theorem bterm (v : BitVec 64) (i : Nat) (hi : i < 64) (s : Nat) :
    (!decide (i < s) && (decide (i - s < 8) && v.getLsbD (s + (i - s)))) =
      (decide (s ≤ i ∧ i < s + 8) && v[i]) := by
  by_cases hs : i < s
  · have h0 : ¬ (s ≤ i ∧ i < s + 8) := by omega
    simp [hs, h0]
  · have h1 : s + (i - s) = i := by omega
    rw [h1, BitVec.getLsbD_eq_getElem hi]
    by_cases h8 : i - s < 8
    · have h2 : s ≤ i ∧ i < s + 8 := by omega
      simp [hs, h8, h2]
    · have h2 : ¬ (s ≤ i ∧ i < s + 8) := by omega
      simp [hs, h8, h2]

theorem wordAt_u64 (x : UInt64) : wordAt (u64 x) 0 = x := by
  simp only [wordAt, u64, byteAt_eq]
  simp
  apply UInt64.eq_of_toBitVec_eq
  simp
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, getElem_mod256,
    BitVec.getElem_ushiftRight, bterm _ i hi]
  cases x.toBitVec[i]
  · simp
  · simp
    omega

theorem size_u64 (x : UInt64) : (u64 x).size = 8 := rfl

/-! ## 3. In the middle of a string -/

theorem byteAt_mid (pre s post : ByteArray) (k : Nat) (hk : k < s.size) :
    byteAt (pre ++ s ++ post) (pre.size + k) = byteAt s k := by
  rw [byteAt_eq, byteAt_eq, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    ByteArray.data_append, ByteArray.data_append,
    Array.getElem?_append_left
      (by rw [Array.size_append, ByteArray.size_data, ByteArray.size_data]; omega),
    Array.getElem?_append_right (by rw [ByteArray.size_data]; omega),
    ByteArray.size_data, Nat.add_sub_cancel_left]

theorem wordAt_mid (pre s post : ByteArray) (j : Nat) (h : j + 8 ≤ s.size) :
    wordAt (pre ++ s ++ post) (pre.size + j) = wordAt s j := by
  unfold wordAt
  simp only [Nat.add_assoc]
  rw [byteAt_mid pre s post j (by omega), byteAt_mid pre s post (j + 1) (by omega),
    byteAt_mid pre s post (j + 2) (by omega), byteAt_mid pre s post (j + 3) (by omega),
    byteAt_mid pre s post (j + 4) (by omega), byteAt_mid pre s post (j + 5) (by omega),
    byteAt_mid pre s post (j + 6) (by omega), byteAt_mid pre s post (j + 7) (by omega)]

theorem extract_mid (pre s post : ByteArray) :
    (pre ++ s ++ post).extract pre.size (pre.size + s.size) = s := by
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, ByteArray.data_append, Array.append_assoc,
    ← ByteArray.size_data, ← ByteArray.size_data, Array.extract_append_right,
    Array.extract_append_left, Array.extract_size]

/-! ## 4. Readers undo spellings -/

/-- The reader r undoes the spelling sp on the values with ok, at any place in a longer string. -/
def Undoes {α : Type} (r : Rd α) (sp : α → ByteArray) (ok : α → Prop) : Prop :=
  ∀ x, ok x →
    ∀ pre post : ByteArray, r (pre ++ sp x ++ post) pre.size = some (x, pre.size + (sp x).size)

theorem undoes_word : Undoes rdWord u64 fun _ => True := by
  intro x _ pre post
  unfold rdWord
  rw [if_pos (by rw [ByteArray.size_append, ByteArray.size_append, size_u64]; omega)]
  have h := wordAt_mid pre (u64 x) post 0 (by rw [size_u64]; omega)
  rw [Nat.add_zero] at h
  rw [h, wordAt_u64, size_u64]

theorem undoes_elt (f : Fld) : Undoes (rdElt f) elt fun x => x.toNat < f.p := by
  intro x hx pre post
  unfold rdElt elt
  rw [undoes_word x trivial pre post]
  simp [Fld.ok, hx]

theorem undoes_pair {α β : Type} {ra : Rd α} {rb : Rd β} {sa : α → ByteArray} {sb : β → ByteArray}
    {oa : α → Prop} {ob : β → Prop} (ha : Undoes ra sa oa) (hb : Undoes rb sb ob) :
    Undoes (rdPair ra rb) (pair sa sb) fun x => oa x.1 ∧ ob x.2 := by
  intro x hx pre post
  unfold rdPair pair
  have e1 : pre ++ (sa x.1 ++ sb x.2) ++ post = pre ++ sa x.1 ++ (sb x.2 ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ (sa x.1 ++ sb x.2) ++ post = (pre ++ sa x.1) ++ sb x.2 ++ post := by
    simp only [ByteArray.append_assoc]
  have h1 := ha x.1 hx.1 pre (sb x.2 ++ post)
  have h2 := hb x.2 hx.2 (pre ++ sa x.1) post
  rw [ByteArray.size_append] at h2
  rw [← e1] at h1
  rw [← e2] at h2
  rw [h1]
  simp only
  rw [h2, ByteArray.size_append, Nat.add_assoc]

theorem undoes_ext (f : Fld) :
    Undoes (rdExt f) ext fun e => e.1.toNat < f.p ∧ e.2.1.toNat < f.p ∧ e.2.2.toNat < f.p := by
  have h := undoes_pair (undoes_elt f) (undoes_pair (undoes_elt f) (undoes_elt f))
  intro e he pre post
  have e0 : ext e = pair elt (pair elt elt) e := by
    unfold ext pair elt
    rw [ByteArray.append_assoc]
  rw [e0]
  exact h e he pre post

theorem undoes_bytes (n : Nat) : Undoes (rdBytes n) id fun b => b.size = n := by
  intro b hb pre post
  subst hb
  unfold rdBytes slice
  rw [if_pos (by rw [ByteArray.size_append, ByteArray.size_append]; simp only [id]; omega)]
  simp only [id, Option.map_some, extract_mid]

theorem undoes_digest : Undoes rdDigest id fun b => b.size = 32 := undoes_bytes 32

theorem undoes_text : Undoes rdText text fun b => b.size < 2 ^ 64 := by
  intro b hb pre post
  unfold rdText text u64n
  have e1 : pre ++ (u64 (UInt64.ofNat b.size) ++ b) ++ post =
      pre ++ u64 (UInt64.ofNat b.size) ++ (b ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ (u64 (UInt64.ofNat b.size) ++ b) ++ post =
      (pre ++ u64 (UInt64.ofNat b.size)) ++ b ++ post := by
    simp only [ByteArray.append_assoc]
  have h1 := undoes_word (UInt64.ofNat b.size) trivial pre (b ++ post)
  rw [← e1] at h1
  rw [h1]
  simp only
  have hn : (UInt64.ofNat b.size).toNat = b.size := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hb
  have h2 := undoes_bytes b.size b rfl (pre ++ u64 (UInt64.ofNat b.size)) post
  simp only [id] at h2
  rw [ByteArray.size_append] at h2
  rw [← e2] at h2
  rw [hn, h2, ByteArray.size_append, Nat.add_assoc]

theorem undoes_name : Undoes rdName text fun b => b.size < 2 ^ 64 ∧ isName b = true := by
  intro b hb pre post
  unfold rdName
  rw [undoes_text b hb.1 pre post]
  simp [hb.2]

theorem undoes_enum {α : Type} (num : α → Nat) (dec : Nat → Option α) :
    Undoes (rdEnum dec) (enum num) fun x => num x < 2 ^ 64 ∧ dec (num x) = some x := by
  intro x hx pre post
  unfold rdEnum enum u64n
  rw [undoes_word _ trivial pre post]
  have hn : (UInt64.ofNat (num x)).toNat = num x := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hx.1
  simp [hn, hx.2]

theorem undoes_bool : Undoes rdBool bool fun _ => True := by
  intro x _ pre post
  unfold rdBool bool
  rw [undoes_word _ trivial pre post]
  cases x <;> simp [size_u64]

theorem foldl_cat (l : List ByteArray) (acc : ByteArray) : l.foldl (· ++ ·) acc = acc ++ cat l := by
  induction l generalizing acc with
  | nil => simp [cat]
  | cons x l ih =>
    unfold cat
    rw [List.foldl_cons, List.foldl_cons, ih, ih (ByteArray.empty ++ x),
      ByteArray.empty_append, ByteArray.append_assoc]

theorem cat_cons (x : ByteArray) (l : List ByteArray) : cat (x :: l) = x ++ cat l := by
  unfold cat
  rw [List.foldl_cons, ByteArray.empty_append, foldl_cat]
  rfl

theorem cat_nil : cat [] = ByteArray.empty := rfl

theorem undoes_many {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (h : Undoes r sp ok)
    (l : List α) (hl : ∀ x ∈ l, ok x) (pre post : ByteArray) :
    rdMany r l.length (pre ++ cat (l.map sp) ++ post) pre.size =
      some (l, pre.size + (cat (l.map sp)).size) := by
  induction l generalizing pre with
  | nil => simp [rdMany, cat_nil]
  | cons x l ih =>
    rw [List.map_cons, cat_cons, List.length_cons]
    unfold rdMany
    have e1 : pre ++ (sp x ++ cat (l.map sp)) ++ post =
        pre ++ sp x ++ (cat (l.map sp) ++ post) := by
      simp only [ByteArray.append_assoc]
    have e2 : pre ++ (sp x ++ cat (l.map sp)) ++ post =
        (pre ++ sp x) ++ cat (l.map sp) ++ post := by
      simp only [ByteArray.append_assoc]
    have h1 := h x (hl x (List.mem_cons_self)) pre (cat (l.map sp) ++ post)
    rw [← e1] at h1
    rw [h1]
    simp only
    have h2 := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (pre ++ sp x)
    rw [ByteArray.size_append, ← e2] at h2
    rw [h2, ByteArray.size_append, Nat.add_assoc]

theorem length_le_cat {α : Type} {sp : α → ByteArray} (l : List α) (h : ∀ x ∈ l, 1 ≤ (sp x).size) :
    l.length ≤ (cat (l.map sp)).size := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, cat_cons, ByteArray.size_append, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem undoes_list {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Undoes r sp ok) (hp : ∀ x, ok x → 1 ≤ (sp x).size) :
    Undoes (rdList r) (list sp) fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, ok x := by
  intro l hl pre post
  unfold rdList list u64n
  have e1 : pre ++ (u64 (UInt64.ofNat l.length) ++ cat (l.map sp)) ++ post =
      pre ++ u64 (UInt64.ofNat l.length) ++ (cat (l.map sp) ++ post) := by
    simp only [ByteArray.append_assoc]
  have e2 : pre ++ (u64 (UInt64.ofNat l.length) ++ cat (l.map sp)) ++ post =
      (pre ++ u64 (UInt64.ofNat l.length)) ++ cat (l.map sp) ++ post := by
    simp only [ByteArray.append_assoc]
  have h1 := undoes_word (UInt64.ofNat l.length) trivial pre (cat (l.map sp) ++ post)
  rw [← e1] at h1
  rw [h1]
  simp only
  have hn : (UInt64.ofNat l.length).toNat = l.length := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hl.1
  have h2 := undoes_many h l hl.2 (pre ++ u64 (UInt64.ofNat l.length)) post
  rw [ByteArray.size_append, ← e2] at h2
  have hc := length_le_cat (sp := sp) l fun x hx => hp x (hl.2 x hx)
  rw [hn,
    if_pos (by rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append]; omega), h2,
    ByteArray.size_append, Nat.add_assoc]

/-- So, under `Undoes r sp ok` and ok x, the reader on the whole spelling gives the value back. -/
theorem whole_of_undoes {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Undoes r sp ok) (x : α) (hx : ok x) : whole r (sp x) = some x := by
  have h1 := h x hx ByteArray.empty ByteArray.empty
  rw [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty, Nat.zero_add] at h1
  unfold whole
  rw [h1]
  simp

/-- So, under `Undoes r sp ok`, the spelling is one to one on the values with ok. -/
theorem inj_of_undoes {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : Undoes r sp ok) (x y : α) (hx : ok x) (hy : ok y) (e : sp x = sp y) : x = y := by
  have h1 := whole_of_undoes h x hx
  rw [e, whole_of_undoes h y hy] at h1
  exact (Option.some.inj h1).symm

end Fmt
