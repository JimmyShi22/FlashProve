-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawPageProofs.lean: the proofs of the statements of Run/DrawPage.lean (the format's draws as
readers of a row of machine words; a round's draws as one block sampler; its bias).

The theorems `drawPage_one`, `drawPage_all`, `drawPage_bs` prove the statements of the same names
in `Run.Spec`.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.DrawPage
import Run.DrawBSProofs

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

theorem card_u64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_word e64

theorem tryNum (f : _root_.Fmt.Fld) : TryNum (okF f) (nGive f) (nFail f) := by
  cases f with
  | one => exact ⟨drawWord_one.1, drawWord_one.2⟩
  | two => exact ⟨drawWord_two.1, drawWord_two.2⟩

theorem fldNum (f : _root_.Fmt.Fld) : FldNum (nGive f) (nFail f) f.p (Fintype.card UInt64) := by
  rw [card_u64]
  cases f with
  | one => exact fldNum_one
  | two => exact fldNum_two

/-! ### Bits of a machine word -/

theorem two_bool (k : Fin 2) : finTwoEquiv k = decide (k.val = 1) := by
  fin_cases k <;> rfl

/-- bit t of the word of 64 bits -/
theorem e64_testBit (v : Dig 64) (t : Fin 64) : (e64 v).toNat.testBit t.val = v t := by
  have h1 : (e64 v).toNat = (eFin64 v).val := rfl
  have h2 : v t = finTwoEquiv ((finFunctionFinEquiv (m := 2) (n := 64)).symm (eFin64 v) t) := by
    have : (finFunctionFinEquiv (m := 2) (n := 64)).symm (eFin64 v) =
        fun i => finTwoEquiv.symm (v i) :=
      Equiv.symm_apply_apply _ _
    rw [this, Equiv.apply_symm_apply]
  rw [h1, h2, two_bool, finFunctionFinEquiv_symm_apply_val, Nat.testBit_eq_decide_div_mod_eq]

/-- tuples of words are tables of bits -/
def eTab (m : ℕ) : (Fin m × Fin 64 → Bool) ≃ (Fin m → UInt64) :=
  (Equiv.curry (Fin m) (Fin 64) Bool).trans (Equiv.piCongrRight fun _ => e64)

/-- where the two bits of pair j are -/
def placeOf (n : ℕ) (x : Fin n × Bool) : Fin ((n + 31) / 32) × Fin 64 :=
  (⟨x.1.val / 32, by have := x.1.isLt; omega⟩,
    ⟨2 * (x.1.val % 32) + (if x.2 then 1 else 0), by split <;> omega⟩)

theorem placeOf_inj (n : ℕ) : Function.Injective (placeOf n) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  have h1 : j.val / 32 = j'.val / 32 := congrArg (fun z : Fin ((n + 31) / 32) × Fin 64 => z.1.val) h
  have h2 : 2 * (j.val % 32) + (if b then 1 else 0) = 2 * (j'.val % 32) + (if b' then 1 else 0) :=
    congrArg (fun z : Fin ((n + 31) / 32) × Fin 64 => z.2.val) h
  cases b <;> cases b' <;> simp only [if_true, if_false, Bool.false_eq_true] at h2
  · exact Prod.ext (Fin.ext (by show j.val = j'.val; omega)) rfl
  · omega
  · omega
  · exact Prod.ext (Fin.ext (by show j.val = j'.val; omega)) rfl

theorem bits_le (n : ℕ) (y : Fin n → Bool × Bool) :
    cnt (fun ws : Fin ((n + 31) / 32) → UInt64 => bitsOf n ws = y) ≤
      2 ^ (64 * ((n + 31) / 32) - 2 * n) := by
  rw [← cnt_equiv (eTab ((n + 31) / 32)) fun ws => bitsOf n ws = y]
  have e : ∀ b : Fin ((n + 31) / 32) × Fin 64 → Bool,
      bitsOf n (eTab ((n + 31) / 32) b) = y ↔
      ∀ x : Fin n × Bool, b (placeOf n x) = if x.2 then (y x.1).2 else (y x.1).1 := by
    intro b
    have hb : ∀ (j : Fin n) (c : Bool), b (placeOf n (j, c)) =
        (eTab ((n + 31) / 32) b ⟨j.val / 32, by have := j.isLt; omega⟩).toNat.testBit
          (2 * (j.val % 32) + (if c then 1 else 0)) := fun j c =>
      (e64_testBit (fun t => b (⟨j.val / 32, by have := j.isLt; omega⟩, t))
        ⟨2 * (j.val % 32) + (if c then 1 else 0), by split <;> omega⟩).symm
    constructor
    · rintro rfl ⟨j, c⟩
      rw [hb]
      cases c <;> rfl
    · intro h
      funext j
      refine Prod.ext ?_ ?_
      · have := h (j, false)
        rw [hb] at this
        exact this
      · have := h (j, true)
        rw [hb] at this
        exact this
  rw [cnt_congr e]
  refine le_trans
    (BS.cnt_restrict_le (placeOf n) (placeOf_inj n) fun x => if x.2 then (y x.1).2 else (y x.1).1)
    (le_of_eq ?_)
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool, Nat.mul_comm _ 64, Nat.mul_comm n 2]

/-- fibres that are all at most r, and r · |C| = |A|: all are r -/
theorem even_of_le {A C : Type} [Fintype A] [Fintype C] (g : A → C) (r : ℕ)
    (hle : ∀ c, cnt (fun a => g a = c) ≤ r) (hr : r * Fintype.card C = Fintype.card A) (c : C) :
    cnt (fun a => g a = c) = r := by
  by_contra hne
  have hlt : cnt (fun a => g a = c) < r := lt_of_le_of_ne (hle c) hne
  have s := sum_cnt_fiber g
  have : ∑ c', cnt (fun a => g a = c') < ∑ _c' : C, r :=
    Finset.sum_lt_sum (fun c' _ => hle c') ⟨c, Finset.mem_univ c, hlt⟩
  rw [s, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm, hr] at this
  exact lt_irrefl _ this

theorem bits_card (n : ℕ) :
    2 ^ (64 * ((n + 31) / 32) - 2 * n) * Fintype.card (Fin n → Bool × Bool) =
      Fintype.card UInt64 ^ ((n + 31) / 32) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, card_u64, ← pow_mul,
    show (2 * 2 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem bits_eq (n : ℕ) (y : Fin n → Bool × Bool) :
    cnt (fun ws : Fin ((n + 31) / 32) → UInt64 => bitsOf n ws = y) =
      2 ^ (64 * ((n + 31) / 32) - 2 * n) :=
  even_of_le (bitsOf n) _ (bits_le n) (by rw [bits_card, Fintype.card_fun, Fintype.card_fin]) y

/-! ### The draws -/

theorem drawPage_one : Spec.drawPage_one := by
  intro f d hd
  cases d with
  | elem =>
    have h := good_trE (0 : UInt64) (tryNum f) (zF f) (Fintype.card_fin _) (fldNum f)
    rw [card_u64] at h
    exact ⟨h, by decide⟩
  | elemNZ =>
    have h := good_trNZ (0 : UInt64) (tryNum f) (zF f) (oE f) (Fintype.card_fin _) (fldNum f)
    rw [card_u64] at h
    exact ⟨h, by decide⟩
  | pos k =>
    have hk : k ≤ 64 := hd
    have h := good_trOne (0 : UInt64) (low k) (drawWord_low k hk) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, card_u64, ← pow_add]
      congr 1
      omega)
    refine ⟨?_, Nat.zero_le _⟩
    show (trOne (low k)).Good 0 1 (2 ^ (64 - k)) (kapSl 128 ^ 0)
    rw [pow_zero]
    exact h
  | trits n =>
    have h := good_trMany (0 : UInt64) ((n + 31) / 32) (bitsOf n) (bits_eq n)
      (by rw [Nat.card_eq_fintype_card]; exact bits_card n)
    refine ⟨?_, Nat.zero_le _⟩
    show (trMany ((n + 31) / 32) (bitsOf n)).Good
      0 ((n + 31) / 32) (2 ^ (64 * ((n + 31) / 32) - 2 * n)) (kapSl 128 ^ 0)
    rw [pow_zero]
    exact h
  | sealed =>
    have h := good_trMany (0 : UInt64) 4 (id : (Fin 4 → UInt64) → Fin 4 → UInt64) (m := 1) (fun c => cnt_eq_const c) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.one_mul])
    refine ⟨?_, Nat.zero_le _⟩
    show (trMany 4 (id : (Fin 4 → UInt64) → Fin 4 → UInt64)).Good 0 4 1 (kapSl 128 ^ 0)
    rw [pow_zero]
    exact h

/-- the values of a draw, of a list of draws, are finitely many -/
theorem finite_DVal (f : _root_.Fmt.Fld) : ∀ d : _root_.Fmt.Draw, Finite (DVal f d)
  | .elem => inferInstanceAs (Finite (EV f))
  | .elemNZ => inferInstanceAs (Finite (NZ f))
  | .pos k => inferInstanceAs (Finite (Fin (2 ^ k)))
  | .trits n => inferInstanceAs (Finite (Fin n → Bool × Bool))
  | .sealed => inferInstanceAs (Finite (Fin 4 → UInt64))

theorem finite_Vals (f : _root_.Fmt.Fld) : ∀ ds : List _root_.Fmt.Draw, Finite (Vals f ds)
  | [] => inferInstanceAs (Finite Unit)
  | d :: ds => haveI := finite_DVal f d; haveI := finite_Vals f ds; inferInstanceAs (Finite (DVal f d × Vals f ds))

theorem drawPage_all : Spec.drawPage_all := by
  intro f ds
  induction ds with
  | nil =>
    intro _
    refine ⟨⟨Tr.Most.ret _ _, fun c => ?_, ?_⟩, Nat.le_refl _⟩
    · show Tr.N 0 0 (Tr.ret () : Tr UInt64 Unit) c ≤ 1
      rw [Tr.N_ret]
      split
      · rw [pow_zero]
      · exact Nat.zero_le _
    · show ((1 : ℕ) : ℝ≥0∞) * (Nat.card Unit : ℝ≥0∞) ≤ kapSl 128 ^ 0 * (Nat.card UInt64 : ℝ≥0∞) ^ 0
      rw [pow_zero, pow_zero, Nat.card_eq_fintype_card, Fintype.card_unit, Nat.cast_one]
  | cons d ds ih =>
    intro h
    obtain ⟨h1, e1⟩ := drawPage_one f d (h d (List.mem_cons_self))
    obtain ⟨h2, e2⟩ := ih fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    haveI := finite_DVal f d
    haveI := finite_Vals f ds
    haveI : Fintype (DVal f d) := Fintype.ofFinite _
    haveI : Fintype (Vals f ds) := Fintype.ofFinite _
    have g := Tr.good_pair (0 : UInt64) h1 h2
    rw [← pow_add] at g
    exact ⟨g, by show 4 * (ex d + exAll ds) ≤ d.most + _root_.Fmt.mostAll ds; omega⟩

theorem drawPage_bs : Spec.drawPage_bs := fun f ds h =>
  ⟨drawBS_pow UInt64 (Vals f ds) e64 0 (all f ds) (_root_.Fmt.mostAll ds) (wtAll f ds) (exAll ds)
      (kapSl 128) (one_le_kapSl 128) (drawPage_all f ds h).2 (drawPage_all f ds h).1,
    rfl⟩

end Run
