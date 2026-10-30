-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawWord.lean: one word of 64 bits and what the format reads off it: a try at an element of the
base field; the low k bits. How many words give a value.

A try is one step of rejection sampling: a word gives an element of the field, or it fails. The
counts here are what the bias of drawing a field element rests on (`TryNum`,
Run/DrawCountNum.lean). Definitions, statements (each a `Prop` in `Run.Spec`) and proofs.
The try is `Fld.tryWord` (Fmt/Rules1.lean), the function on machine words that runs;
`Spec.drawWord_try` states this. Here the try's value is typed as a number below p.

The counts (words are the 2^64 machine words):
  `Spec.drawWord_two`: the field with p = 2^64 - 2^32 + 1: every value comes from exactly one word;
    2^32 - 1 words fail.
  `Spec.drawWord_one`: the field with p = 2^61 - 1: every value comes from exactly 8 words (the
    three high bits are dropped); 8 words fail.
  `Spec.drawWord_low`: k ≤ 64: every number below 2^k comes from exactly 2^(64 - k) words.

Limits: this file says nothing on rows of words: Run/DrawCount.lean, Run/DrawPage.lean.
-/
import Run.DrawBS
import Fmt.Rules6
import Prob.Count

set_option autoImplicit false

namespace Run
open Prob

theorem p_pos (f : _root_.Fmt.Fld) : 0 < f.p := by cases f <;> decide

/-- the values of the base field -/
abbrev FV (f : _root_.Fmt.Fld) : Type := Fin f.p

/-- The try, with its value as a number below p. -/
def okF (f : _root_.Fmt.Fld) (w : UInt64) : Option (FV f) :=
  match _root_.Fmt.Fld.tryWord f w with
  | some x => if h : x.toNat < f.p then some ⟨x.toNat, h⟩ else none
  | none => none

/-- the low k bits -/
def low (k : ℕ) (w : UInt64) : Fin (2 ^ k) := ⟨w.toNat % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

namespace Spec

/-- States that the try is the function that runs: `okF f w` is `Fmt.Fld.tryWord f w`, read as a
number. -/
def drawWord_try : Prop :=
  ∀ (f : _root_.Fmt.Fld) (w : UInt64),
    (okF f w).map (fun x => x.val) = (_root_.Fmt.Fld.tryWord f w).map UInt64.toNat

def drawWord_two : Prop :=
  (∀ x : FV .two, cnt (fun w : UInt64 => okF .two w = some x) = 1) ∧
  cnt (fun w : UInt64 => okF .two w = none) = 2 ^ 32 - 1

def drawWord_one : Prop :=
  (∀ x : FV .one, cnt (fun w : UInt64 => okF .one w = some x) = 8) ∧
  cnt (fun w : UInt64 => okF .one w = none) = 8

def drawWord_low : Prop :=
  ∀ (k : ℕ), k ≤ 64 → ∀ c : Fin (2 ^ k), cnt (fun w : UInt64 => low k w = c) = 2 ^ (64 - k)

end Spec

/-! ### Counting numbers below N -/

/-- the numbers below a · m with a given rest modulo m -/
theorem cnt_mod (N a m x : ℕ) (hN : N = a * m) (hx : x < m) :
    cnt (fun n : Fin N => n.val % m = x) = a := by
  subst hN
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
  have e : {n : Fin (a * m) // n.val % m = x} ≃ Fin a :=
    { toFun := fun n => ⟨n.1.val / m, Nat.div_lt_of_lt_mul ((Nat.mul_comm a m) ▸ n.1.isLt)⟩
      invFun := fun k => ⟨⟨k.val * m + x, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx _) (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right m k.isLt)⟩, by
        show (k.val * m + x) % m = x
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hx]⟩
      left_inv := fun n => Subtype.ext (Fin.ext (by
        show n.1.val / m * m + x = n.1.val
        exact (congrArg (fun y => n.1.val / m * m + y) n.2.symm).trans (Nat.div_add_mod' _ _)))
      right_inv := fun k => Fin.ext (by
        show (k.val * m + x) / m = k.val
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hx, Nat.zero_add]) }
  exact (Nat.card_congr e).trans (Nat.card_fin a)

/-- the numbers below N that are not below p -/
theorem cnt_ge (N p : ℕ) (hp : p ≤ N) : cnt (fun n : Fin N => p ≤ n.val) = N - p := by
  have e : {n : Fin N // p ≤ n.val} ≃ Fin (N - p) :=
    { toFun := fun n => ⟨n.1.val - p, by have := n.1.isLt; have := n.2; omega⟩
      invFun := fun k => ⟨⟨k.val + p, by have := k.isLt; omega⟩, Nat.le_add_left _ _⟩
      left_inv := fun n =>
        Subtype.ext (Fin.ext (by show n.1.val - p + p = n.1.val; have := n.2; omega))
      right_inv := fun k => Fin.ext (by show k.val + p - p = k.val; omega) }
  exact (Nat.card_congr e).trans (Nat.card_fin _)

/-- a machine word is a number below 2^64 -/
def eWord : UInt64 ≃ Fin (2 ^ 64) := ⟨UInt64.toFin, UInt64.ofFin, fun _ => rfl, fun _ => rfl⟩

/-- a count of words is a count of numbers -/
theorem cnt_word (P : ℕ → Prop) :
    cnt (fun w : UInt64 => P w.toNat) = cnt fun n : Fin (2 ^ 64) => P n.val :=
  cnt_equiv eWord fun n : Fin (2 ^ 64) => P n.val

/-! ### The try -/

theorem try_lt (f : _root_.Fmt.Fld) (w x : UInt64) (h : _root_.Fmt.Fld.tryWord f w = some x) :
    x.toNat < f.p := by
  cases f with
  | one =>
    have h' : (if (w &&& 0x1FFFFFFFFFFFFFFF).toNat < _root_.Fmt.Fld.one.p then
            some (w &&& 0x1FFFFFFFFFFFFFFF)
          else none) = some x := h
    split at h'
    · rename_i hlt
      rw [← Option.some.inj h']
      exact hlt
    · cases h'
  | two =>
    have h' : (if w.toNat < _root_.Fmt.Fld.two.p then some w else none) = some x := h
    split at h'
    · rename_i hlt
      rw [← Option.some.inj h']
      exact hlt
    · cases h'

theorem drawWord_try : Spec.drawWord_try := by
  intro f w
  unfold okF
  cases h : _root_.Fmt.Fld.tryWord f w with
  | none => rfl
  | some x =>
    show (if hx : x.toNat < f.p then some (⟨x.toNat, hx⟩ : FV f) else none).map (fun y => y.val) =
      some x.toNat
    rw [dif_pos (try_lt f w x h)]
    rfl

theorem okF_some (f : _root_.Fmt.Fld) (w : UInt64) (x : FV f) :
    okF f w = some x ↔ (_root_.Fmt.Fld.tryWord f w).map UInt64.toNat = some x.val := by
  rw [← drawWord_try f w]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    obtain ⟨y, hy, hv⟩ := Option.map_eq_some_iff.1 h
    rw [hy, Fin.ext hv]

theorem okF_none (f : _root_.Fmt.Fld) (w : UInt64) :
    okF f w = none ↔ (_root_.Fmt.Fld.tryWord f w).map UInt64.toNat = none := by
  rw [← drawWord_try f w, Option.map_eq_none_iff]

theorem drawWord_two : Spec.drawWord_two := by
  have hm : ∀ w : UInt64, (_root_.Fmt.Fld.tryWord .two w).map UInt64.toNat =
      if w.toNat < 18446744069414584321 then some w.toNat else none := fun w => by
    rw [_root_.Fmt.try_two w]
    split <;> rfl
  refine ⟨fun x => ?_, ?_⟩
  · have hx : x.val < 18446744069414584321 := x.isLt
    rw [cnt_congr (Q := fun w : UInt64 => w.toNat % 2 ^ 64 = x.val) fun w => by
      show okF .two w = some x ↔ w.toNat % 2 ^ 64 = x.val
      rw [okF_some, hm, Nat.mod_eq_of_lt w.toNat_lt]
      constructor
      · intro h
        split at h
        · exact Option.some.inj h
        · cases h
      · intro h
        rw [if_pos (h ▸ hx), h]]
    rw [cnt_word fun n => n % 2 ^ 64 = x.val]
    exact cnt_mod (2 ^ 64) 1 (2 ^ 64) x.val (Nat.one_mul _).symm (Nat.lt_trans hx (by norm_num))
  · rw [cnt_congr (Q := fun w : UInt64 => 18446744069414584321 ≤ w.toNat) fun w => by
      show okF .two w = none ↔ 18446744069414584321 ≤ w.toNat
      rw [okF_none, hm]
      constructor
      · intro h
        split at h
        · cases h
        · omega
      · intro h
        rw [if_neg (by omega)]]
    rw [cnt_word fun n => 18446744069414584321 ≤ n, cnt_ge _ _ (by norm_num)]
    norm_num

theorem drawWord_one : Spec.drawWord_one := by
  refine ⟨fun x => ?_, ?_⟩
  · have hx : x.val < 2305843009213693951 := x.isLt
    rw [cnt_congr (Q := fun w : UInt64 => w.toNat % 2 ^ 61 = x.val) fun w => by
      show okF .one w = some x ↔ w.toNat % 2 ^ 61 = x.val
      rw [okF_some, _root_.Fmt.try_one w]
      constructor
      · intro h
        split at h
        · cases h
        · exact Option.some.inj h
      · intro h
        rw [if_neg (by rw [h]; norm_num; omega), h]]
    rw [cnt_word fun n => n % 2 ^ 61 = x.val]
    exact cnt_mod (2 ^ 64) 8 (2 ^ 61) x.val (by norm_num) (Nat.lt_trans hx (by norm_num))
  · rw [cnt_congr (Q := fun w : UInt64 => w.toNat % 2 ^ 61 = 2 ^ 61 - 1) fun w => by
      show okF .one w = none ↔ w.toNat % 2 ^ 61 = 2 ^ 61 - 1
      rw [okF_none, _root_.Fmt.try_one w]
      constructor
      · intro h
        split at h
        · assumption
        · cases h
      · intro h
        rw [if_pos h]]
    rw [cnt_word fun n => n % 2 ^ 61 = 2 ^ 61 - 1]
    exact cnt_mod (2 ^ 64) 8 (2 ^ 61) (2 ^ 61 - 1) (by norm_num) (by norm_num)

theorem drawWord_low : Spec.drawWord_low := by
  intro k hk c
  rw [cnt_congr (Q := fun w : UInt64 => w.toNat % 2 ^ k = c.val) fun w =>
      ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩]
  rw [cnt_word fun n => n % 2 ^ k = c.val]
  exact cnt_mod (2 ^ 64) (2 ^ (64 - k)) (2 ^ k) c.val (by rw [← pow_add]; congr 1; omega) c.isLt

end Run
