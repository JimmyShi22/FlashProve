-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules1Only.lean: the other law of the readers of Fmt/Rules1.lean: what a reader accepts is the
spelling of what it returns, so each value has one spelling.

Fmt/Rules1Laws.lean has: a reader undoes its spelling. Here is the converse. For an enumeration, a
pair, a list and `rdMany` it is proved under the hypotheses named in 3.

A spelling is an encoding of values as bytes (`sp : α → ByteArray`). A reader (`Rd α`,
Fmt/Rules1.lean) is a decoder: from a string of bytes and a place (an offset in bytes) it gives a
value and the place behind it, or it refuses (`none`).

Sources. Section 1 of the format page (docs/format/FORMAT.md);
this file has not been held against the page as it ships,
and may differ from it. No Mathlib; the
file imports Fmt/Rules1Laws.lean alone.


1. What the file contains. Theorems.
   `Only r sp ok`, `word8` (definitions).

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   `u64_wordAt`: the spelling of the word read at a place is the 8 bytes at that place (if they lie
     inside the string).
   `only_word`, `only_elt` (ok: below p), `only_ext`, `only_bool`, `only_bytes`, `only_digest`,
     `only_text`, `only_name` (ok: a name), `only_enum` (asked, as `hd`: a member that dec gives for
     a number has that number).
   `only_pair`, `only_many` (asked, as `hi`: the place is at most the length of the string),
     `only_list`: from the parts' laws.
   `whole_only`: under `Only r sp ok`, whole r b = some x gives b = sp x and ok x. With
     Fmt/Rules1Laws.lean: on the values with ok, reader and spelling are inverse to each other.

4. What is not claimed. These are laws of this library's readers: their refusals are R1.9's, and
this library's own where the page is silent (see the head of Fmt/Rules1.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1Laws

namespace Fmt

/-- a word from its eight bytes, the lowest first -/
def word8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

theorem wordAt_eq (b : ByteArray) (i : Nat) :
    wordAt b i =
      word8 (byteAt b i) (byteAt b (i + 1)) (byteAt b (i + 2)) (byteAt b (i + 3)) (byteAt b (i + 4))
        (byteAt b (i + 5)) (byteAt b (i + 6)) (byteAt b (i + 7)) := rfl

theorem byte_of_word (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (word8 b0 b1 b2 b3 b4 b5 b6 b7).toUInt8 = b0 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 8).toUInt8 = b1 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 16).toUInt8 = b2 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 24).toUInt8 = b3 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 32).toUInt8 = b4 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 40).toUInt8 = b5 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 48).toUInt8 = b6 ∧
    (word8 b0 b1 b2 b3 b4 b5 b6 b7 >>> 56).toUInt8 = b7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply UInt8.eq_of_toBitVec_eq
    ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [word8]

theorem byteAt_in (b : ByteArray) (i : Nat) (h : i < b.data.size) : byteAt b i = b.data[i] := by
  rw [byteAt_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

theorem u64_wordAt (b : ByteArray) (i : Nat) (h : i + 8 ≤ b.size) :
    u64 (wordAt b i) = b.extract i (i + 8) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    byte_of_word (byteAt b i) (byteAt b (i + 1)) (byteAt b (i + 2)) (byteAt b (i + 3))
      (byteAt b (i + 4)) (byteAt b (i + 5)) (byteAt b (i + 6)) (byteAt b (i + 7))
  have hs : b.data.size = b.size := ByteArray.size_data
  apply ByteArray.ext
  rw [ByteArray.data_extract, wordAt_eq]
  unfold u64
  simp only
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  apply Array.ext
  · rw [Array.size_extract]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  · intro k hk1 hk2
    have hk : k < 8 := by simpa using hk1
    rw [Array.getElem_extract]
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals exact byteAt_in b _ (by omega)

/-- What the reader r accepts is the spelling sp of what it returns, and that value has ok. -/
def Only {α : Type} (r : Rd α) (sp : α → ByteArray) (ok : α → Prop) : Prop :=
  ∀ (b : ByteArray) (i : Nat) (x : α) (j : Nat),
    r b i = some (x, j) → ok x ∧ j = i + (sp x).size ∧ j ≤ b.size ∧ b.extract i j = sp x

theorem only_word : Only rdWord u64 fun _ => True := by
  intro b i x j h
  unfold rdWord at h
  by_cases hb : i + 8 ≤ b.size
  · rw [if_pos hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨trivial, by rw [size_u64], hb, (u64_wordAt b i hb).symm⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

theorem only_elt (f : Fld) : Only (rdElt f) elt fun x => x.toNat < f.p := by
  intro b i x j h
  unfold rdElt at h
  rcases hw : rdWord b i with _ | ⟨w, k⟩
  · rw [hw] at h
    exact absurd h (by simp)
  · rw [hw] at h
    simp only at h
    by_cases ho : f.ok w = true
    · rw [if_pos ho] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨-, a, c, d⟩ := only_word b i w k hw
      exact ⟨by simpa [Fld.ok] using ho, a, c, d⟩
    · rw [if_neg ho] at h
      exact absurd h (by simp)

theorem only_pair {α β : Type} {ra : Rd α} {rb : Rd β} {sa : α → ByteArray} {sb : β → ByteArray}
    {oa : α → Prop} {ob : β → Prop} (ha : Only ra sa oa) (hb : Only rb sb ob) :
    Only (rdPair ra rb) (pair sa sb) fun x => oa x.1 ∧ ob x.2 := by
  intro b i x j h
  unfold rdPair at h
  rcases h1 : ra b i with _ | ⟨u, k⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    rcases h2 : rb b k with _ | ⟨v, l⟩
    · rw [h2] at h
      exact absurd h (by simp)
    · rw [h2] at h
      simp only at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a1, a2, -, a4⟩ := ha b i u k h1
      obtain ⟨c1, c2, c3, c4⟩ := hb b k v l h2
      refine ⟨⟨a1, c1⟩, ?_, c3, ?_⟩
      · unfold pair
        rw [ByteArray.size_append]
        simp only
        omega
      · unfold pair
        rw [ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4]

theorem only_ext (f : Fld) :
    Only (rdExt f) ext fun e => e.1.toNat < f.p ∧ e.2.1.toNat < f.p ∧ e.2.2.toNat < f.p := by
  have h := only_pair (only_elt f) (only_pair (only_elt f) (only_elt f))
  intro b i e j he
  have e0 : ext e = pair elt (pair elt elt) e := by
    unfold ext pair elt
    rw [ByteArray.append_assoc]
  rw [e0]
  exact h b i e j he

theorem only_bytes (n : Nat) : Only (rdBytes n) id fun b => b.size = n := by
  intro b i x j h
  unfold rdBytes slice at h
  by_cases hb : i + n ≤ b.size
  · rw [if_pos hb] at h
    simp only [Option.map_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hs : (b.extract i (i + n)).size = n := by
      rw [ByteArray.size_extract]
      omega
    exact ⟨hs, by simp only [id]; rw [hs], hb, rfl⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

theorem only_digest : Only rdDigest id fun b => b.size = 32 := only_bytes 32

theorem only_text : Only rdText text fun b => b.size < 2 ^ 64 := by
  intro b i x j h
  unfold rdText at h
  rcases hw : rdWord b i with _ | ⟨n, k⟩
  · rw [hw] at h
    exact absurd h (by simp)
  · rw [hw] at h
    simp only at h
    obtain ⟨-, a2, -, a4⟩ := only_word b i n k hw
    obtain ⟨c1, c2, c3, c4⟩ := only_bytes n.toNat b k x j h
    simp only [id] at c2 c4
    have hn : u64n x.size = u64 n := by
      unfold u64n
      rw [c1, UInt64.ofNat_toNat]
    rw [size_u64] at a2
    refine ⟨by show x.size < 2 ^ 64; rw [c1]; exact n.toNat_lt, ?_, c3, ?_⟩
    · unfold text
      rw [ByteArray.size_append, hn, size_u64]
      omega
    · unfold text
      rw [ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4, hn]

theorem only_name : Only rdName text fun b => b.size < 2 ^ 64 ∧ isName b = true := by
  intro b i x j h
  unfold rdName at h
  rcases ht : rdText b i with _ | ⟨y, k⟩
  · rw [ht] at h
    exact absurd h (by simp)
  · rw [ht] at h
    simp only at h
    by_cases hn : isName y = true
    · rw [if_pos hn] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a1, a2, a3, a4⟩ := only_text b i y k ht
      exact ⟨⟨a1, hn⟩, a2, a3, a4⟩
    · rw [if_neg hn] at h
      exact absurd h (by simp)

theorem only_enum {α : Type} (num : α → Nat) (dec : Nat → Option α)
    (hd : ∀ n x, dec n = some x → num x = n) :
    Only (rdEnum dec) (enum num) fun x => num x < 2 ^ 64 ∧ dec (num x) = some x := by
  intro b i x j h
  unfold rdEnum at h
  rcases hw : rdWord b i with _ | ⟨w, k⟩
  · rw [hw] at h
    exact absurd h (by simp)
  · rw [hw] at h
    simp only at h
    rcases hx : dec w.toNat with _ | y
    · rw [hx] at h
      exact absurd h (by simp)
    · rw [hx] at h
      simp only [Option.map_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨-, a2, a3, a4⟩ := only_word b i w k hw
      have hn := hd _ _ hx
      have he : enum num y = u64 w := by
        unfold enum u64n
        rw [hn, UInt64.ofNat_toNat]
      exact ⟨⟨by rw [hn]; exact w.toNat_lt, by rw [hn]; exact hx⟩, by rw [he]; exact a2,
        a3, by rw [he]; exact a4⟩

theorem only_bool : Only rdBool bool fun _ => True := by
  intro b i x j h
  unfold rdBool at h
  rcases hw : rdWord b i with _ | ⟨w, k⟩
  · rw [hw] at h
    exact absurd h (by simp)
  · rw [hw] at h
    simp only at h
    obtain ⟨-, a2, a3, a4⟩ := only_word b i w k hw
    by_cases h0 : w = 0
    · rw [if_pos h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst h0
      exact ⟨trivial, a2, a3, a4⟩
    · rw [if_neg h0] at h
      by_cases h1 : w = 1
      · rw [if_pos h1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        subst h1
        exact ⟨trivial, a2, a3, a4⟩
      · rw [if_neg h1] at h
        exact absurd h (by simp)

theorem only_many {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (hr : Only r sp ok) (n : Nat) (b : ByteArray) (i : Nat) (l : List α) (j : Nat)
    (hi : i ≤ b.size) (h : rdMany r n b i = some (l, j)) :
    l.length = n ∧ (∀ x ∈ l, ok x) ∧ j = i + (cat (l.map sp)).size ∧
    j ≤ b.size ∧ b.extract i j = cat (l.map sp) := by
  induction n generalizing i l j with
  | zero =>
    unfold rdMany at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, fun _ hx => absurd hx (by simp), by simp [cat_nil], hi, ?_⟩
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    simp [cat_nil]
    omega
  | succ n ih =>
    unfold rdMany at h
    rcases h1 : r b i with _ | ⟨x, k⟩
    · rw [h1] at h
      exact absurd h (by simp)
    · rw [h1] at h
      simp only at h
      rcases h2 : rdMany r n b k with _ | ⟨l', m⟩
      · rw [h2] at h
        exact absurd h (by simp)
      · rw [h2] at h
        simp only at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a1, a2, a3, a4⟩ := hr b i x k h1
        obtain ⟨c0, c1, c2, c3, c4⟩ := ih k l' m a3 h2
        refine ⟨by rw [List.length_cons, c0], ?_, ?_, c3, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact a1
          · exact c1 y hy
        · rw [List.map_cons, cat_cons, ByteArray.size_append]
          omega
        · rw [List.map_cons, cat_cons,
            ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4]

theorem only_list {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (hr : Only r sp ok) :
    Only (rdList r) (list sp) fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, ok x := by
  intro b i l j h
  unfold rdList at h
  rcases hw : rdWord b i with _ | ⟨n, k⟩
  · rw [hw] at h
    exact absurd h (by simp)
  · rw [hw] at h
    simp only at h
    obtain ⟨-, a2, a3, a4⟩ := only_word b i n k hw
    by_cases hle : k + n.toNat ≤ b.size
    case neg =>
      rw [if_neg hle] at h
      exact absurd h (by simp)
    rw [if_pos hle] at h
    obtain ⟨c0, c1, c2, c3, c4⟩ := only_many hr n.toNat b k l j a3 h
    have hn : u64n l.length = u64 n := by
      unfold u64n
      rw [c0, UInt64.ofNat_toNat]
    rw [size_u64] at a2
    refine ⟨⟨by rw [c0]; exact n.toNat_lt, c1⟩, ?_, c3, ?_⟩
    · unfold list
      rw [ByteArray.size_append, hn, size_u64]
      omega
    · unfold list
      rw [ByteArray.extract_eq_extract_append_extract k (by omega) (by omega), a4, c4, hn]

/-- One spelling: under `Only r sp ok`, a whole string that the reader accepts is the spelling of
the value. -/
theorem whole_only {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (hr : Only r sp ok)
    (b : ByteArray) (x : α) (h : whole r b = some x) : b = sp x ∧ ok x := by
  unfold whole at h
  rcases h1 : r b 0 with _ | ⟨y, j⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    by_cases hj : j = b.size
    · rw [if_pos hj] at h
      obtain rfl := Option.some.inj h
      obtain ⟨a1, -, -, a4⟩ := hr b 0 y j h1
      rw [hj, ByteArray.extract_zero_size] at a4
      exact ⟨a4, a1⟩
    · rw [if_neg hj] at h
      exact absurd h (by simp)

end Fmt
