-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawCountNum.lean: the six kinds of draw of the format, as readers of a row of words: how many
rows give a value, for arbitrary parameters; and, under the hypotheses below, the bias at both
fields' numerals: 1 + 2^-128 for each drawn element of the base field is enough.

A reader (`Tr W C`, Run/DrawRow.lean) makes a value from the next words of a row. For each reader
the file counts or bounds the rows of words that give a value and proves, under the hypotheses told
under Main names, the law `Tr.Good d t K w κ`: t asks for at most K words, every value has at most
w rows of K words, and w · |C| ≤ κ · |W|^K, so that, C being finite, one value takes at most κ
times its even share of all rows (κ bounds the bias).
Definitions, and theorems with their proofs, on Run/DrawRow.lean, Run/DrawCount.lean. The words are
any finite type, the base field's elements any finite type A with a marked element z: no field type
stands in this file, so nothing can make Lean list one. The numerals are natural numbers.

The kinds (restated from the format's section on drawing):
  `trF ok z`: an element of the base field: at most six tries, a word each; the first try that does
    not fail gives the element; if all six fail: z (the element 0), and the six words are used up.
  `trE ok z`: an element of the extension: three of the base field, one after the other.
  `trNZ ok z o`: an element of the extension other than 0: at most two by `trE`; the first that is
    not (z, z, z); if both are: o (the element 1).
  `trOne g`: a value read off one word by a function; its law is proved for a function whose fibres
    all have the same size (a position: the low k bits).
  `trMany k g`: a value read off k words by a function; its law is proved for such a function
    (matrix entries as pairs of bits, 32 to a word; a seal: four words).

Main names:
  `TryNum ok m f`: what is counted of a try: every element is given by exactly m words; exactly f
    words fail.
  Under `TryNum ok m f`, at Q = |W|:
    `wx m f Q`: the rows of six words that give an element other than z.
    `w0 m f Q`: those that give z.
    `wN m f Q`: a bound for every element other than 0 of the extension, met at o if o has two
      coordinates z.
  `N_trF`, `N_trE`: the exact counts, the first under `TryNum ok m f`.
  `good_trF` (6 words, w0, κ), `good_trE` (18, w0^3, κ^3), `good_trNZ` (36, wN, κ^3), with κ :=
    `Iop.kapSl 128` = 1 + 2^-128: from `TryNum ok m f`, |A| = p and `FldNum m f p Q` at Q = |W|.
  `good_trOne` (1, m, 1), `good_trMany` (k, m, 1): for a function all of whose fibres have exactly
    m elements, with m · |C| = |W|, or |W|^k.
  `good_mapEven`: one more rule by which the law is kept: under a function all of whose fibres have
    exactly r elements: (K, w · r, κ).
  `FldNum m f p Q`: the numerals' facts (its fields: see the record).
  `fldNum_one` : `FldNum 8 8 (2^61 - 1) (2^64)`: a try reads the low 61 bits: eight words an
    element, eight words fail.
  `fldNum_two` : `FldNum 1 (2^32 - 1) (2^64 - 2^32 + 1) (2^64)`: a try reads the word: one word an
    element, 2^32 - 1 words fail.

Since 4 e ≤ K in every kind (e the exponent of κ, K the words), a round whose draws take at most K
words, that is b = K / 4 blocks rounded up, has the bias at most κ^b. That is not stated in this
file: see `Spec.drawBS_pow` (Run/DrawBS.lean) and `Spec.drawPage_bs` (Run/DrawPage.lean), with
their hypotheses.

Limits: this file does not say that the format's try on 64-bit words has these counts (`TryNum` at
the two fields), nor that its functions on bytes are these trees' runs, and it says nothing on the
passage from words to blocks: other files of this folder. It says nothing on the least bias that
would serve. It says nothing on where the words come from.
-/
import Run.DrawCount
import Iop.DrawOf

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- from natural numbers to the bias -/
theorem le_kap (a b e : ℕ) (h : a * (2 ^ 128) ^ e ≤ (2 ^ 128 + 1) ^ e * b) :
    (a : ℝ≥0∞) ≤ kapSl 128 ^ e * (b : ℝ≥0∞) := by
  have hX0 : (2 ^ 128 : ℝ≥0∞) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hXt : (2 ^ 128 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hk : kapSl 128 * 2 ^ 128 = 2 ^ 128 + 1 := by
    unfold kapSl
    rw [add_mul, one_mul, ENNReal.inv_mul_cancel hX0 hXt]
  have hc : (a : ℝ≥0∞) * (2 ^ 128) ^ e ≤ (2 ^ 128 + 1) ^ e * (b : ℝ≥0∞) := by exact_mod_cast h
  have h2 : (a : ℝ≥0∞) * (2 ^ 128) ^ e ≤ kapSl 128 ^ e * (b : ℝ≥0∞) * (2 ^ 128) ^ e := by
    calc (a : ℝ≥0∞) * (2 ^ 128) ^ e ≤ (2 ^ 128 + 1) ^ e * (b : ℝ≥0∞) := hc
      _ = kapSl 128 ^ e * (b : ℝ≥0∞) * (2 ^ 128) ^ e := by rw [← hk, mul_pow]; ring
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero e hX0) (ENNReal.pow_ne_top hXt)).1 h2

/-- What is counted of a try. -/
structure TryNum {W A : Type} [Fintype W] (ok : W → Option A) (m f : ℕ) : Prop where
  hit : ∀ a, cnt (fun w => ok w = some a) = m
  miss : cnt (fun w => ok w = none) = f

def wx (m f Q : ℕ) : ℕ := m * geo f Q 6
def w0 (m f Q : ℕ) : ℕ := m * geo f Q 6 + f ^ 6
def wN (m f Q : ℕ) : ℕ :=
  wx m f Q * w0 m f Q ^ 2 * Q ^ 18 + w0 m f Q ^ 3 * (wx m f Q * w0 m f Q ^ 2) + (w0 m f Q ^ 3) ^ 2

/-- The numerals' facts. -/
structure FldNum (m f p Q : ℕ) : Prop where
  kF : w0 m f Q * p * (2 ^ 128) ^ 1 ≤ (2 ^ 128 + 1) ^ 1 * Q ^ 6
  kN : wN m f Q * (p ^ 3 - 1) * (2 ^ 128) ^ 3 ≤ (2 ^ 128 + 1) ^ 3 * Q ^ 36

theorem fldNum_one : FldNum 8 8 (2 ^ 61 - 1) (2 ^ 64) :=
  ⟨by norm_num [w0, geo], by norm_num [wN, wx, w0, geo]⟩

theorem fldNum_two : FldNum 1 (2 ^ 32 - 1) (2 ^ 64 - 2 ^ 32 + 1) (2 ^ 64) :=
  ⟨by norm_num [w0, geo], by norm_num [wN, wx, w0, geo]⟩

section
variable {W A C : Type}

/-- an element of the base field -/
def trF (ok : W → Option A) (z : A) : Tr W A := Tr.tries ok z 6

/-- an element of the extension -/
def trE (ok : W → Option A) (z : A) : Tr W (A × A × A) :=
  (trF ok z).pair ((trF ok z).pair (trF ok z))

/-- an element of the extension other than 0 -/
def trNZ [DecidableEq A] (ok : W → Option A) (z : A) (o : {e : A × A × A // e ≠ (z, z, z)}) :
    Tr W {e : A × A × A // e ≠ (z, z, z)} :=
  (trE ok z).again (z, z, z) o

/-- a value read off one word -/
def trOne (g : W → C) : Tr W C := Tr.ask fun w => Tr.ret (g w)

/-- a value read off k words -/
def trMany (k : ℕ) (g : (Fin k → W) → C) : Tr W C := (Tr.vec k Tr.word).map g

theorem most_trF (ok : W → Option A) (z : A) : (trF ok z).Most 6 := Tr.most_tries ok z 6
theorem most_trE (ok : W → Option A) (z : A) : (trE ok z).Most 18 :=
  Tr.most_pair (most_trF ok z) (Tr.most_pair (most_trF ok z) (most_trF ok z))
theorem most_trNZ [DecidableEq A] (ok : W → Option A) (z : A)
    (o : {e : A × A × A // e ≠ (z, z, z)}) : (trNZ ok z o).Most 36 :=
  Tr.most_again (most_trE ok z) _ o

variable [Fintype W] (d : W)

open Classical in
theorem N_trF {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) (z c : A) :
    Tr.N d 6 (trF ok z) c = if z = c then w0 m f (Fintype.card W) else wx m f (Fintype.card W) := by
  show Tr.N d 6 (Tr.tries ok z 6) c = _
  rw [Tr.N_tries, T.hit, T.miss]
  split
  · rfl
  · rfl

theorem wx_le_w0 (m f Q : ℕ) : wx m f Q ≤ w0 m f Q := Nat.le_add_right _ _

theorem N_trF_le {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) (z c : A) :
    Tr.N d 6 (trF ok z) c ≤ w0 m f (Fintype.card W) := by
  classical
  rw [N_trF d T]
  split
  · exact le_rfl
  · exact wx_le_w0 _ _ _

theorem N_trF_ne {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) {z c : A} (h : c ≠ z) :
    Tr.N d 6 (trF ok z) c = wx m f (Fintype.card W) := by
  classical
  rw [N_trF d T, if_neg (Ne.symm h)]

theorem N_trF_z {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) (z : A) :
    Tr.N d 6 (trF ok z) z = w0 m f (Fintype.card W) := by
  classical
  rw [N_trF d T, if_pos rfl]

theorem N_trE [Fintype A] (ok : W → Option A) (z : A) (x : A × A × A) :
    Tr.N d 18 (trE ok z) x =
      Tr.N d 6 (trF ok z) x.1 * (Tr.N d 6 (trF ok z) x.2.1 * Tr.N d 6 (trF ok z) x.2.2) := by
  obtain ⟨a, b, c⟩ := x
  show Tr.N d (6 + (6 + 6)) ((trF ok z).pair ((trF ok z).pair (trF ok z))) (a, b, c) = _
  rw [Tr.N_pair d (most_trF ok z) (Tr.most_pair (most_trF ok z) (most_trF ok z)),
    Tr.N_pair d (most_trF ok z) (most_trF ok z)]

theorem N_trE_z [Fintype A] {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) (z : A) :
    Tr.N d 18 (trE ok z) (z, z, z) = w0 m f (Fintype.card W) ^ 3 := by
  rw [N_trE, N_trF_z d T]
  ring

/-- an element other than (z, z, z) -/
theorem NE_le [Fintype A] {ok : W → Option A} {m f : ℕ} (T : TryNum ok m f) (z : A)
    (x : A × A × A) (hx : x ≠ (z, z, z)) :
    Tr.N d 18 (trE ok z) x ≤ wx m f (Fintype.card W) * w0 m f (Fintype.card W) ^ 2 := by
  obtain ⟨a, b, c⟩ := x
  rw [N_trE]
  have la := N_trF_le d T z a
  have lb := N_trF_le d T z b
  have lc := N_trF_le d T z c
  by_cases ha : a = z
  · by_cases hb : b = z
    · have hc : c ≠ z := fun hc => hx (by rw [ha, hb, hc])
      show Tr.N d 6 (trF ok z) a * (Tr.N d 6 (trF ok z) b * Tr.N d 6 (trF ok z) c) ≤ _
      rw [N_trF_ne d T hc]
      calc Tr.N d 6 (trF ok z) a * (Tr.N d 6 (trF ok z) b * wx m f (Fintype.card W)) ≤ w0 m f (Fintype.card W) * (w0 m f (Fintype.card W) * wx m f (Fintype.card W)) :=
            Nat.mul_le_mul la (Nat.mul_le_mul_right _ lb)
        _ = _ := by ring
    · show Tr.N d 6 (trF ok z) a * (Tr.N d 6 (trF ok z) b * Tr.N d 6 (trF ok z) c) ≤ _
      rw [N_trF_ne d T hb]
      calc Tr.N d 6 (trF ok z) a * (wx m f (Fintype.card W) * Tr.N d 6 (trF ok z) c) ≤ w0 m f (Fintype.card W) * (wx m f (Fintype.card W) * w0 m f (Fintype.card W)) :=
            Nat.mul_le_mul la (Nat.mul_le_mul_left _ lc)
        _ = _ := by ring
  · show Tr.N d 6 (trF ok z) a * (Tr.N d 6 (trF ok z) b * Tr.N d 6 (trF ok z) c) ≤ _
    rw [N_trF_ne d T ha]
    calc wx m f (Fintype.card W) * (Tr.N d 6 (trF ok z) b * Tr.N d 6 (trF ok z) c) ≤ wx m f (Fintype.card W) * (w0 m f (Fintype.card W) * w0 m f (Fintype.card W)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul lb lc)
      _ = _ := by ring

/-! ### The law -/

variable {m f p : ℕ}

theorem good_trF [Fintype A] {ok : W → Option A} (T : TryNum ok m f) (z : A)
    (hA : Fintype.card A = p) (H : FldNum m f p (Fintype.card W)) :
    Tr.Good d (trF ok z) 6 (w0 m f (Fintype.card W)) (kapSl 128 ^ 1) where
  most := most_trF ok z
  fib := N_trF_le d T z
  ratio := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hA]
    have := le_kap _ _ 1 H.kF
    push_cast at this ⊢
    exact this

theorem good_trE [Fintype A] {ok : W → Option A} (T : TryNum ok m f) (z : A)
    (hA : Fintype.card A = p) (H : FldNum m f p (Fintype.card W)) :
    Tr.Good d (trE ok z) 18 (w0 m f (Fintype.card W) ^ 3) (kapSl 128 ^ 3) := by
  have h := good_trF d T z hA H
  have h3 := Tr.good_pair d h (Tr.good_pair d h h)
  have e1 : w0 m f (Fintype.card W) * (w0 m f (Fintype.card W) * w0 m f (Fintype.card W)) =
      w0 m f (Fintype.card W) ^ 3 := by ring
  have e2 : kapSl 128 ^ 1 * (kapSl 128 ^ 1 * kapSl 128 ^ 1) = kapSl 128 ^ 3 := by ring
  rw [e1, e2] at h3
  exact h3

theorem good_trNZ [Fintype A] [DecidableEq A] {ok : W → Option A}
    (T : TryNum ok m f) (z : A) (o : {e : A × A × A // e ≠ (z, z, z)})
    (hA : Fintype.card A = p) (H : FldNum m f p (Fintype.card W)) :
    Tr.Good d (trNZ ok z o) 36 (wN m f (Fintype.card W)) (kapSl 128 ^ 3) where
  most := most_trNZ ok z o
  fib := fun c => by
    classical
    show Tr.N d (18 + 18) ((trE ok z).again (z, z, z) o) c ≤ _
    rw [Tr.N_again d (most_trE ok z), N_trE_z d T]
    have hc := NE_le d T z c.1 c.2
    unfold wN
    refine Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hc) (Nat.mul_le_mul_left _ hc)) ?_
    split
    · exact le_rfl
    · exact Nat.zero_le _
  ratio := by
    have e : Nat.card {e : A × A × A // e ≠ (z, z, z)} = p ^ 3 - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        Fintype.card_prod, Fintype.card_prod, hA]
      congr 1
      ring
    rw [e, Nat.card_eq_fintype_card]
    have := le_kap _ _ 3 H.kN
    push_cast at this ⊢
    exact this

/-- a value read off one word by a function with fibres of one size -/
theorem good_trOne (g : W → C) (hm : ∀ c, cnt (fun w => g w = c) = m)
    (hQ : m * Nat.card C = Fintype.card W) : Tr.Good d (trOne g) 1 m 1 where
  most := Tr.Most.ask _ 0 fun w => Tr.Most.ret _ 0
  fib := fun c => by
    show Tr.N d 1 (Tr.ask fun w => Tr.ret (g w)) c ≤ m
    rw [Tr.N_word_map, hm]
  ratio := by
    rw [Nat.card_eq_fintype_card (α := W), one_mul, pow_one, ← hQ]
    push_cast
    exact le_rfl

open Classical in
/-- under any function: the sum over the values that it sends to c -/
theorem N_map [Fintype A] {t : Tr W A} {K : ℕ} (h : t.Most K) (g : A → C) (c : C) :
    Tr.N d K (t.map g) c = ∑ a, if g a = c then Tr.N d K t a else 0 := by
  have e :=
    Tr.N_bind d h (fun a => (Tr.ret (g a) : Tr W C)) (K₂ := 0) (fun a => Tr.Most.ret (g a) 0) c
  rw [Nat.add_zero] at e
  show Tr.N d K (t.bind fun a => Tr.ret (g a)) c = _
  rw [e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Tr.N_ret, pow_zero]
  split
  · rw [mul_one]
  · rw [mul_zero]

/-- k words: every row is given by itself alone -/
theorem N_words (k : ℕ) (u : Fin k → W) : Tr.N d (k * 1) (Tr.vec k Tr.word) u = 1 := by
  rw [Tr.N_vec d Tr.most_word]
  refine Finset.prod_eq_one fun i _ => ?_
  show Tr.N d 1 (Tr.ask fun w => Tr.ret (id w)) (u i) = 1
  rw [Tr.N_word_map]
  exact cnt_eq_const (u i)

/-- a value read off k words by a function with fibres of one size -/
theorem good_trMany (k : ℕ) (g : (Fin k → W) → C) (hm : ∀ c, cnt (fun u => g u = c) = m)
    (hQ : m * Nat.card C = Fintype.card W ^ k) :
    Tr.Good d (trMany k g) k m 1 where
  most := by
    have := Tr.most_map g (Tr.most_vec (Tr.most_word (W := W)) k)
    rwa [Nat.mul_one] at this
  fib := fun c => by
    classical
    have e := N_map d (Tr.most_vec (Tr.most_word (W := W)) k) g c
    simp_rw [N_words] at e
    rw [Nat.mul_one] at e
    show Tr.N d k ((Tr.vec k Tr.word).map g) c ≤ m
    rw [e, ← Finset.sum_filter, Finset.sum_const, ← cnt_eq_card_filter, hm, smul_eq_mul, mul_one]
  ratio := by
    rw [Nat.card_eq_fintype_card (α := W), one_mul]
    have : ((m * Nat.card C : ℕ) : ℝ≥0∞) = ((Fintype.card W ^ k : ℕ) : ℝ≥0∞) := by rw [hQ]
    push_cast at this
    exact le_of_eq this

/-- Under a function all of whose fibres have exactly r elements. (not all hypotheses are named
here: see the statement below) -/
theorem good_mapEven [Fintype A] [Fintype C] {t : Tr W A} {K w : ℕ} {κ : ℝ≥0∞}
    (h : Tr.Good d t K w κ) (g : A → C) (r : ℕ) (hr : ∀ c, cnt (fun a => g a = c) = r) :
    Tr.Good d (t.map g) K (w * r) κ where
  most := Tr.most_map g h.most
  fib := fun c => by
    classical
    rw [N_map d h.most, ← Finset.sum_filter]
    calc
      ∑ a ∈ Finset.univ.filter (fun a => g a = c), Tr.N d K t a ≤
          ∑ _a ∈ Finset.univ.filter (fun a => g a = c), w :=
        Finset.sum_le_sum fun a _ => h.fib a
      _ = w * r := by rw [Finset.sum_const, ← cnt_eq_card_filter, hr, smul_eq_mul, mul_comm]
  ratio := by
    have e : r * Nat.card C = Nat.card A := by
      have s := sum_cnt_fiber g
      simp_rw [hr] at s
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at s
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← s, mul_comm]
    have e' : (r : ℝ≥0∞) * (Nat.card C : ℝ≥0∞) = (Nat.card A : ℝ≥0∞) := by exact_mod_cast e
    push_cast
    rw [mul_assoc, e']
    exact h.ratio

end
end Run
