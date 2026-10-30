-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyChalLaw.lean: the words that the format reads off a block's 32 bytes are the words of the
block's 256 bits; and positions drawn by the format from uniform blocks are exactly uniform (n at
most 4 K positions below 2^k, k at most 64, from K blocks).

Statements (each a `Prop` in the namespace `Run.Spec`) and proofs. Nothing is defined but these
statements.
The file is about the Fiat-Shamir step: how a round's verifier message is drawn from blocks of hash
output. A block is a string of 256 bits (`Iop.Dig`, Iop/Wire.lean). The wiring of a round (`WireRB`,
Iop/BatchWire.lean) has a field `chal`, a map from K blocks to the round's verifier message.

Two definitions make a row of 64-bit words out of blocks.
The one that runs: a block of 256 bits becomes 32 bytes (`digToBytes`, Run/CodingBits.lean: bit i is
bit (i mod 8), from the lowest, of byte (i div 8)), and the format reads four words off them, each
lowest byte first (`rowOfBlocks`, Fmt/Rules6.lean; R6.1, R1.5; `rowOfDigs`, Run/ToyChal.lean).
The one for which counts are proved: bit 64 j + t of the block is bit t of word j (`wordBits`,
`e64`, `rowOf`, Run/DrawBS.lean).
Run/DrawTie.lean declares that their agreement is not said there. It is stated and proved here
(`Spec.row_tie`).

Main names:
  `Spec.word_bit`: for k < 64, bit k of the word at byte i of a string is bit (k mod 8) of
    byte i + k div 8.
  `Spec.byte_bit_dig`: for r < 8 and 8 m + r < 256, bit r of byte m of a block's 32 bytes is
    bit 8 m + r of the block.
  `Spec.row_tie`: `rowOfDigs u` = the row of Run/DrawBS.lean (`rowOf e64 K u`), 0 beyond its end:
    for all blocks.
  `Spec.bs_bytes`: what the block sampler of a round (`bsOf`, Run/DrawPage.lean) gives, as it is
    handed on (`outAll`), is `chalAll` of the blocks (Run/ToyChal.lean). That is, by `row_tie`,
    `drawTie_bs` of Run/DrawTie.lean is about the bytes that run.
  `Spec.poss_unif`: for n at most 4 K and k at most 64: the image of K uniform blocks under
    `chalPoss k n` is the uniform distribution on n positions below 2^k (R6.6: independent, uniform,
    repeats allowed). This is the clause `chal_unif` of the conditions on a wiring
    (Iop/BatchWire.lean: `WireRB.OK`, `WireRB.OKG`), for a round whose verifier messages are these
    vectors of positions and whose `chal` is `chalPoss k n`.
  `Spec.toy1_unif`: that clause at the wiring of a toy of this library's own: `Toy1.w1.chal`
    (Run/ToyQ.lean; one block, three positions below 16).

Limits: this file says nothing on the other clauses of the conditions on a wiring. Draws of field
elements are not exactly uniform (Run/DrawPage.lean has their bias).

Terms: lean/GLOSSARY.md.
-/
import Run.ToyChalTie
import Run.DrawTieProofs
import Run.DrawPageProofs
import Fmt.Rules5Laws
import Iop.WireOK

set_option autoImplicit false

namespace Run
open Iop Prob

namespace Spec

def word_bit : Prop :=
  ∀ (b : ByteArray) (i k : ℕ), k < 64 →
    (_root_.Fmt.wordAt b i).toNat.testBit k =
      (_root_.Fmt.byteAt b (i + k / 8)).toNat.testBit (k % 8)

def byte_bit_dig : Prop :=
  ∀ (x : Dig 256) (m r : ℕ) (h : 8 * m + r < 256),
    r < 8 → (_root_.Fmt.byteAt (digToBytes x) m).toNat.testBit r = x ⟨8 * m + r, h⟩

/-- States that the two rows of words are one, for every number of blocks and all blocks. -/
def row_tie : Prop := ∀ (K : ℕ) (u : Fin K → Dig 256), rowOfDigs u = rowFn 0 (rowOf e64 K u)

/-- States that the value of a round's block sampler, taken through `outAll`, is the format's list
of draws on the blocks' bytes. -/
def bs_bytes : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) (u : Fin (bsOf f ds).b → Dig 256),
    outAll f ds ((bsOf f ds).φ u) = chalAll f ds u

/-- States that positions are exactly uniform, for n ≤ 4 K and k ≤ 64. -/
def poss_unif : Prop :=
  ∀ (K k n : ℕ),
    n ≤ 4 * K → k ≤ 64 → (unif (Fin K → Dig 256)).map (chalPoss k n) = unif (Fin n → Fin (2 ^ k))

def toy1_unif : Prop := (unif (Fin 1 → Dig 256)).map Toy1.w1.chal = unif Toy1.r1.Chal

end Spec

theorem word_bit : Spec.word_bit := by
  intro b i k hk
  have e0 : ((_root_.Fmt.byteAt b i).toUInt64.toNat).testBit k =
      (decide (k / 8 = 0) && (_root_.Fmt.byteAt b i).toNat.testBit (k % 8)) := by
    rw [UInt8.toNat_toUInt64, ← _root_.Fmt.pick]
    simp
  have e (j : ℕ) (s : UInt64) (hs : s.toNat = 8 * j) (hj : j < 8) : (((_root_.Fmt.byteAt
          b (i + j)).toUInt64
        <<< s).toNat).testBit k =
      (decide (k / 8 = j) && (_root_.Fmt.byteAt b (i + j)).toNat.testBit (k % 8)) := by
    rw [_root_.Fmt.sh_testBit _ s (by omega) k hk, hs, _root_.Fmt.pick]
  unfold _root_.Fmt.wordAt
  simp only [UInt64.toNat_or, Nat.testBit_or]
  rw [e0, e 1 8 rfl (by decide), e 2 16 rfl (by decide), e 3 24 rfl (by decide),
    e 4 32 rfl (by decide), e 5 40 rfl (by decide), e 6 48 rfl (by decide), e 7 56 rfl (by decide)]
  have hq : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 ∨ k / 8 = 4 ∨ k / 8 = 5 ∨
      k / 8 = 6 ∨ k / 8 = 7 := by omega
  rcases hq with h | h | h | h | h | h | h | h <;> simp [h]

/-- The bits of a byte made of eight bits. -/
theorem byteOf_testBit :
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (r : Fin 8),
      (byteOf [b0, b1, b2, b3, b4, b5, b6, b7]).toNat.testBit r.val =
        [b0, b1, b2, b3, b4, b5, b6, b7].getD r.val false := by decide +kernel

/-- The bits of the bytes of a bit string of whole bytes. -/
theorem bytesL_testBit :
    ∀ (n : ℕ) (l : List Bool), l.length = 8 * n →
      ∀ m r : ℕ, m < n → r < 8 → ((bytesL l).getD m 0).toNat.testBit r = l.getD (8 * m + r) false
  | 0, _, _, _, _, hm, _ => absurd hm (Nat.not_lt_zero _)
  | n + 1, l, h, m, r, hm, hr => by
    match l, h with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t, h =>
      have ht : t.length = 8 * n := by simp only [List.length_cons] at h; omega
      show ((byteOf [b0, b1, b2, b3, b4, b5, b6, b7] :: bytesL t).getD m 0).toNat.testBit r = _
      cases m with
      | zero =>
        have h1 := byteOf_testBit b0 b1 b2 b3 b4 b5 b6 b7 ⟨r, hr⟩
        show (byteOf [b0, b1, b2, b3, b4, b5, b6, b7]).toNat.testBit r = _
        rw [h1]
        have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      | succ m =>
        have ih := bytesL_testBit n t ht m r (by omega) hr
        show ((bytesL t).getD m 0).toNat.testBit r = _
        rw [ih, show 8 * (m + 1) + r = (8 * m + r) + 8 by omega]
        rfl
    | [], h => simp at h
    | [_], h => simp at h; omega
    | [_, _], h => simp at h; omega
    | [_, _, _], h => simp at h; omega
    | [_, _, _, _], h => simp at h; omega
    | [_, _, _, _, _], h => simp at h; omega
    | [_, _, _, _, _, _], h => simp at h; omega
    | [_, _, _, _, _, _, _], h => simp at h; omega

theorem byte_bit_dig : Spec.byte_bit_dig := by
  intro x m r h hr
  have h1 := bytesL_testBit 32 (List.ofFn x) (List.length_ofFn (f := x)) m r (by omega) hr
  have gen : ∀ (l : List UInt8) (i : ℕ), l.toArray.getD i 0 = l.getD i 0 := by
    intro l i
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  have h2 : _root_.Fmt.byteAt (digToBytes x) m = (bytesL (List.ofFn x)).getD m 0 := gen _ m
  rw [h2, h1, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

/-- Word j off a block's 32 bytes is word j of the block's bits, for each of the four words. -/
theorem word_tie (x : Dig 256) (j : Fin 4) :
    _root_.Fmt.wordAt (digToBytes x) (8 * j.val) = e64 (wordBits x j) := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 64
  · have hj := j.isLt
    rw [word_bit _ _ _ hk,
      byte_bit_dig x (8 * j.val + k / 8) (k % 8) (by omega) (Nat.mod_lt _ (by decide)),
      e64_testBit (wordBits x j) ⟨k, hk⟩]
    show x _ = x _
    congr 1
    apply Fin.ext
    show 8 * (8 * j.val + k / 8) + k % 8 = 64 * j.val + k
    omega
  · have hp : (2 : ℕ) ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _) hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt _) hp)]

/-- Every word read off the empty string is 0. -/
theorem wordAt_empty (i : ℕ) : _root_.Fmt.wordAt ByteArray.empty i = 0 := by
  have h : ∀ j, _root_.Fmt.byteAt ByteArray.empty j = 0 := fun j => by
    show (#[] : Array UInt8).getD j 0 = 0
    simp
  unfold _root_.Fmt.wordAt
  simp only [h]
  rfl

theorem row_tie : Spec.row_tie := by
  intro K u
  funext t
  show _root_.Fmt.wordAt
      ((Array.ofFn fun i => digToBytes (u i)).getD (t / 4) ByteArray.empty) (8 * (t % 4)) = _
  unfold rowFn
  by_cases h : t < 4 * K
  · rw [dif_pos h]
    have h4 : t / 4 < K := by omega
    have e : (Array.ofFn fun i => digToBytes (u i)).getD (t / 4) ByteArray.empty =
        digToBytes (u ⟨t / 4, h4⟩) := by
      simp [Array.getD, h4]
    rw [e]
    exact word_tie (u ⟨t / 4, h4⟩) ⟨t % 4, Nat.mod_lt _ (by decide)⟩
  · rw [dif_neg h]
    have h4 : ¬ t / 4 < K := by omega
    have e : (Array.ofFn fun i => digToBytes (u i)).getD (t / 4) ByteArray.empty =
        ByteArray.empty := by
      simp [Array.getD, h4]
    rw [e]
    exact wordAt_empty _

theorem bs_bytes : Spec.bs_bytes := by
  intro f ds u
  rw [drawTie_bs f ds u, ← row_tie]
  rfl

/-- For k ≤ 64, the low k bits of a uniform word are uniform. -/
theorem low_unif (k : ℕ) (hk : k ≤ 64) : (unif UInt64).map (low k) = unif (Fin (2 ^ k)) := by
  rw [map_unif_eq_unif_iff]
  intro c
  rw [drawWord_low k hk c, Fintype.card_fin, ← pow_add, Fintype.card_congr e64.symm,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  congr 1
  omega

theorem poss_unif : Spec.poss_unif := by
  intro K k n hn hk
  have e : ∀ u : Fin K → Dig 256, chalPoss k n u = (fun (w : Fin n → UInt64) i => low k (w i))
      ((fun (v : Fin (4 * K) → UInt64) (i : Fin n) =>
          if h' : i.val < 4 * K then v ⟨i.val, h'⟩ else 0)
        (rowEquiv e64 K u)) := by
    intro u
    funext i
    have hi : i.val < 4 * K := Nat.lt_of_lt_of_le i.isLt hn
    have hr : rowOfDigs u i.val = rowOf e64 K u ⟨i.val, hi⟩ :=
      (congrFun (row_tie K u) i.val).trans (dif_pos hi)
    apply Fin.ext
    show (rowOfDigs u i.val).toNat % 2 ^ k =
      (if h' : i.val < 4 * K then rowOf e64 K u ⟨i.val, h'⟩ else 0).toNat % 2 ^ k
    rw [dif_pos hi, hr]
  rw [map_eq_map_map
        (f := fun u =>
            (fun (v : Fin (4 * K) → UInt64) (i : Fin n) =>
                if h' : i.val < 4 * K then v ⟨i.val, h'⟩ else 0)
              (rowEquiv e64 K u))
        (g := fun (w : Fin n → UInt64) i => low k (w i)) _ e,
    map_eq_map_map (f := rowEquiv e64 K)
      (g := fun (v : Fin (4 * K) → UInt64) (i : Fin n) =>
          if h' : i.val < 4 * K then v ⟨i.val, h'⟩ else 0)
      _ fun _ => rfl,
    map_unif_equiv, map_firstBlocks_unif UInt64 0 n (4 * K) hn]
  exact map_unif_pi (fun _ => low k) fun _ => low_unif k hk

theorem toy1_unif : Spec.toy1_unif := by
  show (unif (Fin 1 → Dig 256)).map Toy1.w1.chal = unif (Fin 3 → Fin 16)
  rw [toy1_chal]
  exact poss_unif 1 4 3 (by decide) (by decide)

end Run
