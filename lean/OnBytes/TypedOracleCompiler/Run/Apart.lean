-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Apart.lean: how strings of the format are told apart: the two words of a call's
label, read off a string at fixed places; the tags of the numbers 173 and 178; and a way to join two
partial codes on ONE type by a test on the points.

Every string of the format is one byte (the half), a parameter block of 64 bytes, a label of two
words, and the call's bytes (library, Fmt/Rules23.lean: `oStr`, `pblock`, `label`). The label's
first word holds the call's number in its low 16 bits and a second number above them; the second
word is the index. A page joins partial codes into one, and each joining asks that no string is
written by both. The library tells codes apart by the 16 bits of the number (`tag16`,
Run/CodingTag.lean). A page for a file with several chains also has to tell two first values (number
160) and two rounds' calls (number 162) of different chains apart: by the label's words whole.
 - `lw1 s`, `lw2 s`: the 64 bits from bit 520 and from bit 584 of s; `lw_at`: what they are at a
   string with 520 bits before two words;
 - `lw_hdr`: at a string that begins with the library's header `hdr half number tree index start`,
   for a start of 32 bytes: the words number + 65536 · tree, and index; `lw_160`: at `hdr160 lab`:
   160, and lab; `lw_162`: at the form in which a round's call is written: its two words; `lw_173`:
   at `SeamAt.head173 cfg place index`: 173 + 65536 · place, and index;
 - `word_inj`: two numbers below 2 ^ 64 with the same word's bits are equal;
 - `apart1`, `apart2`: two codes whose strings have different first words, or different second
   words, have no string in common;
 - `tag_lw1`: the library's tag is the first 16 bits of `lw1`; `t173`, `t178`, `t173_differs`,
   `t178_differs`;
 - `Is160 l s`, `Is162 l s`, `Is173 p s`: what is known of a string under 160 with the label l,
   under 162 with the label l, under 173: the label's words and the first byte; `is160_of_hdr`,
   `is162_of_shape`, `is173_of_head`: strings of these forms; `no_160_160`, `no_160_162`,
   `no_162_162`, `no_173_160`, `no_173_162`: no string is of two of these kinds, for labels below 2
   ^ 48 that differ; `tag_160`, `tag_162`, `tag_173`;
 - `split p q c h`: the code on one type that writes p's string where the test c is true and q's
   where it is false, given that p and q have no string in common; `split_true`, `split_false`,
   `split_put`.

Main definitions: `lw1`, `lw2`, `t173`, `t178`, `Is160`, `Is162`, `Is173`, `split`.
Main theorems: `lw_at`, `lw_hdr`, `lw_160`, `lw_162`, `lw_173`, `word_inj`, `apart1`, `apart2`,
`t173_differs`, `t178_differs`, `split_true`, `split_false`, `split_put`.

Not claimed. Tools alone: no page. Nothing on any hash. Nothing on soundness. The sibling is a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/. The compiler under OnBytes/TypedOracleCompiler/ is
the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.SeamAt
import OnBytes.TypedOracleCompiler.Run.Tag174

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run TypedOracleCompiler.Run.PutSome
open _root_.Run

/-! ## The label's two words -/

/-- The 64 bits from bit 520 on: in a string of the format, the label's first word. -/
def lw1 (s : List Bool) : List Bool := (s.drop 520).take 64

/-- The 64 bits from bit 584 on: in a string of the format, the label's second word. -/
def lw2 (s : List Bool) : List Bool := (s.drop 584).take 64

/-- What they are at a string with 520 bits before two words. -/
theorem lw_at (a w1 w2 r : List Bool) (ha : a.length = 520) (h1 : w1.length = 64)
    (h2 : w2.length = 64) :
    lw1 (a ++ (w1 ++ (w2 ++ r))) = w1 ∧ lw2 (a ++ (w1 ++ (w2 ++ r))) = w2 := by
  constructor
  · unfold lw1
    rw [List.drop_left' ha]
    exact List.take_left' h1
  · unfold lw2
    rw [← List.append_assoc, List.drop_left' (by rw [List.length_append, ha, h1])]
    exact List.take_left' h2

/-- At a string that begins with a call's header, for a start of 32 bytes. -/
theorem lw_hdr (half : UInt8) (number tree index : ℕ) (start : ByteArray) (hs : start.size = 32)
    (x : List Bool) :
    lw1 (hdr half number tree index start ++ x) =
        bytesToBits (_root_.Fmt.u64n (number + 65536 * tree)) ∧
      lw2 (hdr half number tree index start ++ x) = bytesToBits (_root_.Fmt.u64n index) := by
  unfold hdr _root_.Fmt.label
  have e : bytesToBits
          (⟨#[half]⟩ ++ _root_.Fmt.pblock number start ++
            (_root_.Fmt.u64n (number + 65536 * tree) ++ _root_.Fmt.u64n index)) ++ x =
      (bytesToBits ⟨#[half]⟩ ++ bytesToBits (_root_.Fmt.pblock number start)) ++
        (bytesToBits (_root_.Fmt.u64n (number + 65536 * tree)) ++
          (bytesToBits (_root_.Fmt.u64n index) ++ x)) := by
    simp only [bytesToBits_append, List.append_assoc]
  rw [e]
  exact lw_at _ _ _ _
    (by rw [List.length_append, length_bytesToBits, length_bytesToBits,
      _root_.Fmt.size_pblock number start hs]; rfl) (length_u64n _) (length_u64n _)

/-- At a string that begins with the header of a first value under the label lab. -/
theorem lw_160 (lab : ℕ) (x : List Bool) :
    lw1 (hdr160 lab ++ x) = bytesToBits (_root_.Fmt.u64n 160) ∧
      lw2 (hdr160 lab ++ x) = bytesToBits (_root_.Fmt.u64n lab) :=
  lw_hdr 0 160 0 lab _root_.Fmt.zero32 rfl x

/-- At the form in which a round's call is written. -/
theorem lw_162 (hb : UInt8) (ρ r : List Bool) (hρ : ρ.length = 256) (a b : ℕ) :
    lw1 (bitsOfByte hb ++ (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n a) ++
        (bytesToBits (_root_.Fmt.u64n b) ++ r))))) = bytesToBits (_root_.Fmt.u64n a) ∧
      lw2 (bitsOfByte hb ++ (mid32 ++ (ρ ++ (bytesToBits (_root_.Fmt.u64n a) ++
        (bytesToBits (_root_.Fmt.u64n b) ++ r))))) = bytesToBits (_root_.Fmt.u64n b) := by
  rw [← List.append_assoc, ← List.append_assoc]
  exact lw_at _ _ _ _
    (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])
    (length_u64n _) (length_u64n _)

/-- At a string that begins with the fixed string of the hash under 173, for a start of 32 bytes. -/
theorem lw_173 (cfg : ByteArray) (hc : cfg.size = 32) (place index : ℕ) (x : List Bool) :
    lw1 (SeamAt.head173 cfg place index ++ x) =
        bytesToBits (_root_.Fmt.u64n (173 + 65536 * place)) ∧
      lw2 (SeamAt.head173 cfg place index ++ x) = bytesToBits (_root_.Fmt.u64n index) := by
  unfold SeamAt.head173 _root_.Fmt.label
  have e : pre33 ++ (bytesToBits cfg ++
        bytesToBits (_root_.Fmt.u64n (173 + 65536 * place) ++ _root_.Fmt.u64n index)) ++ x =
      (pre33 ++ bytesToBits cfg) ++ (bytesToBits (_root_.Fmt.u64n (173 + 65536 * place)) ++
        (bytesToBits (_root_.Fmt.u64n index) ++ x)) := by
    simp only [bytesToBits_append, List.append_assoc]
  rw [e]
  exact lw_at _ _ _ _ (by rw [List.length_append, length_pre33, length_bytesToBits, hc])
    (length_u64n _) (length_u64n _)

/-- Two numbers below 2 ^ 64 with the same word's bits are equal. -/
theorem word_inj (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : bytesToBits (_root_.Fmt.u64n a) = bytesToBits (_root_.Fmt.u64n b)) : a = b := by
  have h1 : pWord.put a = some (bytesToBits (_root_.Fmt.u64n a)) := if_pos ha
  have h2 : pWord.put b = some (bytesToBits (_root_.Fmt.u64n a)) := by
    rw [h]
    exact if_pos hb
  exact pWord.inj h1 h2

/-- Two codes whose strings have different first words of the label have no string in common. -/
theorem apart1 {A B : Type} (p : PCode A) (q : PCode B) (P Q : List Bool → Prop)
    (hPQ : ∀ w, P w → ¬ Q w) (hp : ∀ x s, p.put x = some s → P (lw1 s))
    (hq : ∀ y s, q.put y = some s → Q (lw1 s)) : ∀ x y s, p.put x = some s → q.put y ≠ some s :=
  fun x y s h1 h2 => hPQ _ (hp x s h1) (hq y s h2)

/-- The same by the second words. -/
theorem apart2 {A B : Type} (p : PCode A) (q : PCode B) (P Q : List Bool → Prop)
    (hPQ : ∀ w, P w → ¬ Q w) (hp : ∀ x s, p.put x = some s → P (lw2 s))
    (hq : ∀ y s, q.put y = some s → Q (lw2 s)) : ∀ x y s, p.put x = some s → q.put y ≠ some s :=
  fun x y s h1 h2 => hPQ _ (hp x s h1) (hq y s h2)

/-! ## Tags -/

/-- The library's tag is the first 16 bits of the label's first word. -/
theorem tag_lw1 (s : List Bool) : tag16 s = (lw1 s).take 16 := by
  unfold tag16 lw1
  rw [List.take_take]
  rfl

/-- The 16 bits of the number 173. -/
def t173 : List Bool := (bytesToBits (_root_.Fmt.u64n 173)).take 16

/-- The 16 bits of the number 178. -/
def t178 : List Bool := (bytesToBits (_root_.Fmt.u64n 178)).take 16

/-- The tag of 173 is none of the five tags of a page, nor that of 178. -/
theorem t173_differs :
    t173 ≠ t160 ∧ t173 ≠ t162 ∧ t173 ≠ t164 ∧ t173 ≠ t166 ∧ t173 ≠ t174 ∧ t173 ≠ t178 := by
  decide +kernel

/-- The tag of 178 is none of the five tags of a page. -/
theorem t178_differs : t178 ≠ t160 ∧ t178 ≠ t162 ∧ t178 ≠ t164 ∧ t178 ≠ t166 ∧ t178 ≠ t174 := by
  decide +kernel

/-! ## What is known of a string under 160, 162 or 173 -/

/-- A word's bits. -/
abbrev Wd (n : ℕ) : List Bool := bytesToBits (_root_.Fmt.u64n n)

/-- What is known of a string under 160 with the label l. -/
def Is160 (l : ℕ) (s : List Bool) : Prop :=
  lw1 s = Wd 160 ∧ lw2 s = Wd l ∧ ∀ b : UInt8, b ≠ 0 → ¬ bitsOfByte b <+: s

/-- What is known of a string under 162 with the label l. -/
def Is162 (l : ℕ) (s : List Bool) : Prop :=
  lw1 s = Wd (162 + 65536 * l) ∧ ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s

/-- What is known of a string under 173. -/
def Is173 (p : ℕ) (s : List Bool) : Prop :=
  lw1 s = Wd (173 + 65536 * p) ∧ ∀ b : UInt8, b ≠ 0 → ¬ bitsOfByte b <+: s

/-- A string that begins with the header of a first value. -/
theorem is160_of_hdr (l : ℕ) (s : List Bool) (h : ∃ r, s = hdr160 l ++ r) : Is160 l s := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨(lw_160 l r).1, (lw_160 l r).2,
    fun b hb => hdr_not_prefix b 0 hb 160 0 l _root_.Fmt.zero32 r⟩

/-- A string in the form in which a round's call is written. -/
theorem is162_of_shape (l j : ℕ) (hb : Bool) (ρ r : List Bool) (hρ : ρ.length = 256) :
    Is162 l (bitsOfByte (if hb then 1 else 0) ++ (mid32 ++ (ρ ++ (Wd (162 + 65536 * l) ++
      (Wd j ++ r))))) := by
  refine ⟨(lw_162 _ ρ r hρ _ _).1, fun b h0 h1 => ?_⟩
  cases hb
  · exact byte_prefix b 0 h0 _
  · exact byte_prefix b 1 h1 _

/-! ## No string in common -/

/-- Two words' bits differ if the numbers, below 2 ^ 64, differ. -/
theorem wd_ne (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) : Wd a ≠ Wd b :=
  fun e => h (word_inj a b ha hb e)

/-- No string is under 160 with two different labels below 2 ^ 48. -/
theorem no_160_160 (l l' : ℕ) (hl : l < 2 ^ 48) (hl' : l' < 2 ^ 48) (h : l ≠ l') (s : List Bool)
    (h1 : Is160 l s) (h2 : Is160 l' s) : False :=
  wd_ne l l' (by omega) (by omega) h (h1.2.1.symm.trans h2.2.1)

/-- No string is under 160 and under 162. -/
theorem no_160_162 (l l' : ℕ) (hl' : l' < 2 ^ 48) (s : List Bool) (h1 : Is160 l s)
    (h2 : Is162 l' s) : False :=
  wd_ne 160 (162 + 65536 * l') (by omega) (by omega) (by omega) (h1.1.symm.trans h2.1)

/-- No string is under 162 with two different labels below 2 ^ 48. -/
theorem no_162_162 (l l' : ℕ) (hl : l < 2 ^ 48) (hl' : l' < 2 ^ 48) (h : l ≠ l') (s : List Bool)
    (h1 : Is162 l s) (h2 : Is162 l' s) : False :=
  wd_ne (162 + 65536 * l) (162 + 65536 * l') (by omega) (by omega) (by omega)
    (h1.1.symm.trans h2.1)

/-- The tag of a string from the first word of its label. -/
theorem tag_of_lw1 (n x : ℕ) (s : List Bool) (h : lw1 s = Wd (n + 65536 * x)) :
    tag16 s = (Wd n).take 16 := by
  rw [tag_lw1, h]
  exact tag_low n x

/-- No string is under 173 and under 160. -/
theorem no_173_160 (p l : ℕ) (s : List Bool) (h1 : Is173 p s) (h2 : Is160 l s) : False :=
  t173_differs.1 ((tag_of_lw1 173 p s h1.1).symm.trans (tag_of_lw1 160 0 s h2.1))

/-- No string is under 173 and under 162. -/
theorem no_173_162 (p l : ℕ) (s : List Bool) (h1 : Is173 p s) (h2 : Is162 l s) : False :=
  t173_differs.2.1 ((tag_of_lw1 173 p s h1.1).symm.trans (tag_of_lw1 162 l s h2.1))

/-- The tags of the three kinds. -/
theorem tag_160 (l : ℕ) (s : List Bool) (h : Is160 l s) : tag16 s = t160 := tag_of_lw1 160 0 s h.1

/-- See `tag_160`. -/
theorem tag_162 (l : ℕ) (s : List Bool) (h : Is162 l s) : tag16 s = t162 := tag_of_lw1 162 l s h.1

/-- See `tag_160`. -/
theorem tag_173 (p : ℕ) (s : List Bool) (h : Is173 p s) : tag16 s = t173 := tag_of_lw1 173 p s h.1

/-- A string that begins with the fixed string of the hash under 173, for a start of 32 bytes. -/
theorem is173_of_head (cfg : ByteArray) (hc : cfg.size = 32) (place index : ℕ) (r : List Bool) :
    Is173 place (SeamAt.head173 cfg place index ++ r) := by
  refine ⟨(lw_173 cfg hc place index r).1, fun b hb => ?_⟩
  unfold SeamAt.head173
  rw [List.append_assoc]
  exact pre33_not_prefix b hb _

/-! ## Two codes on one type, by a test -/

section
variable {A : Type} (p q : PCode A) (c : A → Bool)
  (h : ∀ a b s, p.put a = some s → q.put b ≠ some s)

/-- By the test: left or right. -/
def selC (x : A) : Option (A ⊕ A) := if c x = true then some (.inl x) else some (.inr x)

/-- And back: refused where the side is not the test's. -/
def mkC : A ⊕ A → Option A
  | .inl x => if c x = true then some x else none
  | .inr x => if c x = true then none else some x

/-- The way back undoes the way there. -/
theorem mkC_selC (x : A) (y : A ⊕ A) (hy : selC c x = some y) : mkC c y = some x := by
  unfold selC at hy
  by_cases hc : c x = true
  · rw [if_pos hc] at hy
    rw [← Option.some.inj hy]
    exact if_pos hc
  · rw [if_neg hc] at hy
    rw [← Option.some.inj hy]
    exact if_neg hc

/-- The way there undoes the way back. -/
theorem selC_mkC (y : A ⊕ A) (x : A) (hx : mkC c y = some x) : selC c x = some y := by
  rcases y with y | y
  · have h0 : (if c y = true then some y else none) = some x := hx
    by_cases hc : c y = true
    · rw [if_pos hc] at h0
      rw [← Option.some.inj h0]
      exact if_pos hc
    · rw [if_neg hc] at h0
      cases h0
  · have h0 : (if c y = true then none else some y) = some x := hx
    by_cases hc : c y = true
    · rw [if_pos hc] at h0
      cases h0
    · rw [if_neg hc] at h0
      rw [← Option.some.inj h0]
      exact if_neg hc

/-- The code that writes p's string where the test is true and q's where it is false. -/
def split : PCode A := (p.sum q h).pull (selC c) (mkC c) (mkC_selC c) (selC_mkC c)

/-- Where the test is true it writes what p writes. -/
theorem split_true (x : A) (hc : c x = true) : (split p q c h).put x = p.put x := by
  show (selC c x).bind (p.sum q h).put = _
  unfold selC
  rw [if_pos hc]
  rfl

/-- Where the test is false it writes what q writes. -/
theorem split_false (x : A) (hc : c x = false) : (split p q c h).put x = q.put x := by
  show (selC c x).bind (p.sum q h).put = _
  unfold selC
  rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
  rfl

/-- Whatever it writes, p or q writes at the same point. -/
theorem split_put (x : A) (s : List Bool) (hs : (split p q c h).put x = some s) :
    p.put x = some s ∨ q.put x = some s := by
  cases hc : c x with
  | true => rw [split_true p q c h x hc] at hs; exact Or.inl hs
  | false => rw [split_false p q c h x hc] at hs; exact Or.inr hs

end

end TypedOracleCompiler.Run.Apart
