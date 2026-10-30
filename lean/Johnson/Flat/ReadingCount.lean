-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingCount.lean: how many typed values of a round hit: the count that
Johnson/Flat/ReadingBad.lean leaves open.

The setting. A round draws a list of draws ds. Bf names a set of values by the elements that are
drawn before in the round. A typed value v of the round hits if some drawn element is read into its
set (`hitL`). deg j bounds the number of typed elements that are read into the set of element
number j.

Main names:
  `hitBound deg ds j`: a number, by recursion on the draws. At an element: deg j times the number
    of the later draws' values, plus the number of the element's values times the bound behind it.
    At a position, matrix entries or a sealing: the number of its values times the bound behind it.
  `cnt_hit_le`: if for all xs at most deg (j + xs.length) typed elements are read into Bf xs, then
    at most `hitBound deg ds j` typed values hit.
  `sumDeg deg ds j`: the sum of deg over the round's elements, the first of them numbered j. A
    position, matrix entries and a sealing add nothing and take no number.
  `hitBound_share`: hitBound times q is at most sumDeg times the number of the round's typed
    values, q the number of elements other than 0. As a share: at most (the sum of the degrees) /
    (|E| - 1). This is the price before the bits of work are counted.
  `cnt_hit_share_ds`, `cnt_hit_share`: the share in the form of `BadHeld`, for a list of draws and
    for a round.
  `hitV_iff_hitL`, `cnt_hitV_share`: the same for one set B (`hitV`), as `BadHeld` and `BadHeldEx`
    ask for it.
  `cnt_mem_le`: where the reading is one to one on typed elements, at most |s| of them are read
    into a finite set s.

Three cases, each as a theorem:
  All degrees 0: `hitBound_zero`, `sumDeg_zero`, `cnt_hit_zero`: nothing hits.
  No element among the draws (`NoElem`): `hitBound_noElem`, `sumDeg_noElem`, `cnt_hit_noElem`:
    nothing hits.
  One element: `hitBound_one`, `hitBound_oneNZ`, `sumDeg_one`: deg j times the number of the other
    draws' values: the share deg j / |E| at a plain element, deg j / (|E| - 1) at one other than 0.
    `cnt_hit_ge`, `cnt_hit_eq_one`: there the bound is met, so no smaller number serves.
    `toy_one`: at the draws [.elem, .trits 0] and a set of one element exactly one typed value hits.

Limits. The premise of `cnt_hit_le` is asked at all lists xs, also at such as no round draws. With
two or more elements `hitBound` is a union bound, not the exact count. `hitBound_share` holds
whatever the size of deg; where sumDeg is q or more it says nothing.

-/
import Johnson.Flat.ReadingBad

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice

variable {K : Type} (rd : Fmt.Ext → K)

theorem not_hitL_nil (Bf : List Fmt.Ext → Set K) : ¬ hitL rd Bf [] := by
  rintro ⟨xs, x, ys, h, _⟩
  cases xs <;> cases h

theorem hitL_cons {Bf : List Fmt.Ext → Set K} {x₀ : Fmt.Ext} {l : List Fmt.Ext}
    (h : hitL rd Bf (x₀ :: l)) : rd x₀ ∈ Bf [] ∨ hitL rd (fun xs => Bf (x₀ :: xs)) l := by
  obtain ⟨xs, x, ys, h, hB⟩ := h
  cases xs with
  | nil =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    exact .inl hB
  | cons a xs' =>
    obtain ⟨rfl, h2⟩ := List.cons.inj h
    exact .inr ⟨xs', x, ys, h2, hB⟩

/-- A bound on the typed values that hit. -/
noncomputable def hitBound (deg : ℕ → ℕ) : List Fmt.Draw → ℕ → ℕ
  | [], _ => 0
  | .elem :: ds, j =>
    deg j * Fintype.card (Vals .two ds) + Fintype.card (EV .two) * hitBound deg ds (j + 1)
  | .elemNZ :: ds, j =>
    deg j * Fintype.card (Vals .two ds) + Fintype.card (NZ .two) * hitBound deg ds (j + 1)
  | .pos k :: ds, j => Fintype.card (DVal .two (.pos k)) * hitBound deg ds j
  | .trits n :: ds, j => Fintype.card (DVal .two (.trits n)) * hitBound deg ds j
  | .sealed :: ds, j => Fintype.card (DVal .two .sealed) * hitBound deg ds j

theorem cnt_nz_le (P : EV .two → Prop) : cnt (fun a : NZ .two => P a.1) ≤ cnt P := by
  have h := cnt_comp_le (fun a : NZ .two => a.1) (w := 1)
    (fun c => cnt_le_one fun a b ha hb => Subtype.ext (ha.trans hb.symm)) P
  rwa [Nat.mul_one] at h

theorem cnt_hit_le (deg : ℕ → ℕ) : ∀ (ds : List Fmt.Draw) (j : ℕ) (Bf : List Fmt.Ext → Set K),
    (∀ xs, cnt (fun a : EV .two => rd (toU3 a) ∈ Bf xs) ≤ deg (j + xs.length)) →
    cnt (fun v : Vals .two ds => hitL rd Bf (Fmt.collect (outAll .two ds v)).elems) ≤
      hitBound deg ds j
  | [], _, Bf, _ => le_of_eq (cnt_false fun _ h => not_hitL_nil rd Bf h)
  | .elem :: ds, j, Bf, H => by
      refine (cnt_le_add (C := EV .two × Vals .two ds)
        (P := fun v => hitL rd Bf (toU3 v.1 :: (Fmt.collect (outAll .two ds v.2)).elems))
        (Q := fun v => rd (toU3 v.1) ∈ Bf [])
        (R := fun v => hitL rd (fun xs => Bf (toU3 v.1 :: xs))
          (Fmt.collect (outAll .two ds v.2)).elems)
        (fun _ hv => hitL_cons rd hv)).trans ?_
      refine Nat.add_le_add ?_ ?_
      · rw [cnt_fst (fun a : EV .two => rd (toU3 a) ∈ Bf [])]
        exact Nat.mul_le_mul_right _ (H [])
      · exact cnt_prod_le _ _ fun a => cnt_hit_le deg ds (j + 1) (fun xs => Bf (toU3 a :: xs))
          fun xs => by
            have h := H (toU3 a :: xs)
            rwa [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm] at h
  | .elemNZ :: ds, j, Bf, H => by
      refine (cnt_le_add (C := NZ .two × Vals .two ds)
        (P := fun v => hitL rd Bf (toU3 v.1.1 :: (Fmt.collect (outAll .two ds v.2)).elems))
        (Q := fun v => rd (toU3 v.1.1) ∈ Bf [])
        (R := fun v => hitL rd (fun xs => Bf (toU3 v.1.1 :: xs))
          (Fmt.collect (outAll .two ds v.2)).elems)
        (fun _ hv => hitL_cons rd hv)).trans ?_
      refine Nat.add_le_add ?_ ?_
      · rw [cnt_fst (fun a : NZ .two => rd (toU3 a.1) ∈ Bf [])]
        exact Nat.mul_le_mul_right _
          ((cnt_nz_le fun a => rd (toU3 a) ∈ Bf []).trans (H []))
      · exact cnt_prod_le _ _ fun a => cnt_hit_le deg ds (j + 1) (fun xs => Bf (toU3 a.1 :: xs))
          fun xs => by
            have h := H (toU3 a.1 :: xs)
            rwa [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm] at h
  | .pos k :: ds, j, Bf, H =>
      cnt_prod_le (C := DVal .two (.pos k)) (D := Vals .two ds)
        (fun v => hitL rd Bf (Fmt.collect (outAll .two ds v.2)).elems) _
        fun _ => cnt_hit_le deg ds j Bf H
  | .trits n :: ds, j, Bf, H =>
      cnt_prod_le (C := DVal .two (.trits n)) (D := Vals .two ds)
        (fun v => hitL rd Bf (Fmt.collect (outAll .two ds v.2)).elems) _
        fun _ => cnt_hit_le deg ds j Bf H
  | .sealed :: ds, j, Bf, H =>
      cnt_prod_le (C := DVal .two .sealed) (D := Vals .two ds)
        (fun v => hitL rd Bf (Fmt.collect (outAll .two ds v.2)).elems) _
        fun _ => cnt_hit_le deg ds j Bf H

/-- Where the reading is one to one on typed elements, at most |s| of them are read into a finite
set s. -/
theorem cnt_mem_le (inj : Function.Injective fun a : EV .two => rd (toU3 a)) (s : Finset K) :
    cnt (fun a : EV .two => rd (toU3 a) ∈ (s : Set K)) ≤ s.card :=
  cnt_le_of_forall_finset fun _ hY =>
    Finset.card_le_card_of_injOn (fun a => rd (toU3 a)) (fun a ha => hY a ha) (inj.injOn)

/-! ### the bound as a share -/

/-- The sum of deg over the elements among the draws, the first of them numbered j. -/
def sumDeg (deg : ℕ → ℕ) : List Fmt.Draw → ℕ → ℕ
  | [], _ => 0
  | .elem :: ds, j => deg j + sumDeg deg ds (j + 1)
  | .elemNZ :: ds, j => deg j + sumDeg deg ds (j + 1)
  | .pos _ :: ds, j => sumDeg deg ds j
  | .trits _ :: ds, j => sumDeg deg ds j
  | .sealed :: ds, j => sumDeg deg ds j

/-- The step at an element, on numbers: a the degree, V the later draws' values, Q the element's
values. -/
theorem share_step (a V Q q h s : ℕ) (hq : q ≤ Q) (ih : h * q ≤ s * V) :
    (a * V + Q * h) * q ≤ (a + s) * (Q * V) :=
  calc (a * V + Q * h) * q = a * V * q + Q * (h * q) := by ring
    _ ≤ a * V * Q + Q * (s * V) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hq) (Nat.mul_le_mul_left _ ih)
    _ = (a + s) * (Q * V) := by ring

/-- The step at a draw that is no element, on numbers. -/
theorem share_skip (c V q h s : ℕ) (ih : h * q ≤ s * V) : c * h * q ≤ s * (c * V) :=
  calc c * h * q = c * (h * q) := by ring
    _ ≤ c * (s * V) := Nat.mul_le_mul_left _ ih
    _ = s * (c * V) := by ring

theorem card_sub_le {α : Type} [Fintype α] (p : α → Prop) [Fintype {a : α // p a}] :
    Fintype.card {a : α // p a} ≤ Fintype.card α :=
  Fintype.card_le_of_injective (fun a : {a : α // p a} => a.1) Subtype.val_injective

theorem card_nz_le : Fintype.card (NZ .two) ≤ Fintype.card (EV .two) := card_sub_le _

theorem card_nz_pos : 0 < Fintype.card (NZ .two) := Fintype.card_pos_iff.2 ⟨oE .two⟩

theorem card_vals_cons (d : Fmt.Draw) (ds : List Fmt.Draw) :
    Fintype.card (Vals .two (d :: ds)) =
      Fintype.card (DVal .two d) * Fintype.card (Vals .two ds) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Nat.card_prod _ _

/-- The bound, as a share of the round's typed values: at most (the sum of the degrees) /
(|E| - 1). -/
theorem hitBound_share (deg : ℕ → ℕ) : ∀ (ds : List Fmt.Draw) (j : ℕ),
    hitBound deg ds j * Fintype.card (NZ .two) ≤ sumDeg deg ds j * Fintype.card (Vals .two ds)
  | [], _ => by
      show 0 * _ ≤ 0 * _
      rw [Nat.zero_mul, Nat.zero_mul]
  | .elem :: ds, j => by
      rw [card_vals_cons]
      exact share_step (deg j) (Fintype.card (Vals .two ds)) (Fintype.card (EV .two))
        (Fintype.card (NZ .two)) (hitBound deg ds (j + 1)) (sumDeg deg ds (j + 1)) card_nz_le
        (hitBound_share deg ds (j + 1))
  | .elemNZ :: ds, j => by
      rw [card_vals_cons]
      exact share_step (deg j) (Fintype.card (Vals .two ds)) (Fintype.card (NZ .two))
        (Fintype.card (NZ .two)) (hitBound deg ds (j + 1)) (sumDeg deg ds (j + 1)) le_rfl
        (hitBound_share deg ds (j + 1))
  | .pos k :: ds, j => by
      rw [card_vals_cons]
      exact share_skip (Fintype.card (DVal .two (.pos k))) (Fintype.card (Vals .two ds))
        (Fintype.card (NZ .two)) (hitBound deg ds j) (sumDeg deg ds j) (hitBound_share deg ds j)
  | .trits n :: ds, j => by
      rw [card_vals_cons]
      exact share_skip (Fintype.card (DVal .two (.trits n))) (Fintype.card (Vals .two ds))
        (Fintype.card (NZ .two)) (hitBound deg ds j) (sumDeg deg ds j) (hitBound_share deg ds j)
  | .sealed :: ds, j => by
      rw [card_vals_cons]
      exact share_skip (Fintype.card (DVal .two .sealed)) (Fintype.card (Vals .two ds))
        (Fintype.card (NZ .two)) (hitBound deg ds j) (sumDeg deg ds j) (hitBound_share deg ds j)

/-- The typed values that hit, as a share, for a list of draws. -/
theorem cnt_hit_share_ds (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (Bf : List Fmt.Ext → Set K)
    (H : ∀ xs, cnt (fun a : EV .two => rd (toU3 a) ∈ Bf xs) ≤ deg (j + xs.length)) :
    ((cnt (fun v : Vals .two ds => hitL rd Bf (Fmt.collect (outAll .two ds v)).elems) : ℕ) : ℝ≥0∞) ≤
      ((sumDeg deg ds j : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) *
        ((Nat.card (Vals .two ds) : ℕ) : ℝ≥0∞) := by
  rw [Nat.card_eq_fintype_card]
  exact share_le _ _ _ _ card_nz_pos
    ((Nat.mul_le_mul_right _ (cnt_hit_le rd deg ds j Bf H)).trans (hitBound_share deg ds j))

/-- At a round, in the form of `BadHeld`: the price with the work not counted is
(the sum of the degrees) / (|E| - 1). -/
theorem cnt_hit_share (deg : ℕ → ℕ) (e : Fmt.Entry) (k : Fmt.Kind) (Bf : List Fmt.Ext → Set K)
    (H : ∀ xs, cnt (fun a : EV .two => rd (toU3 a) ∈ Bf xs) ≤ deg xs.length) :
    ((cnt (fun v : Vals .two (Fmt.dsOf e k) => hitL rd Bf (drawnOf .two e k v).elems) : ℕ) : ℝ≥0∞) ≤
      ((sumDeg deg (Fmt.dsOf e k) 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) *
        ((Nat.card (Vals .two (Fmt.dsOf e k)) : ℕ) : ℝ≥0∞) :=
  cnt_hit_share_ds rd deg (Fmt.dsOf e k) 0 Bf fun xs => by
    rw [Nat.zero_add]
    exact H xs

/-- One set for all elements: `hitV` is `hitL` at the constant family. -/
theorem hitV_iff_hitL (B : Set K) (e : Fmt.Entry) (k : Fmt.Kind) (v : Vals .two (Fmt.dsOf e k)) :
    hitV rd B e k v ↔ hitL rd (fun _ => B) (drawnOf .two e k v).elems := by
  constructor
  · rintro ⟨x, hx, hB⟩
    obtain ⟨xs, ys, h⟩ := List.append_of_mem hx
    exact ⟨xs, x, ys, h, hB⟩
  · rintro ⟨xs, x, ys, h, hB⟩
    exact ⟨x, by rw [h]; exact List.mem_append_right _ (List.mem_cons_self ..), hB⟩

/-- The first clause of `BadHeld` and of `BadHeldEx` at a round, where at most n typed elements are
read into B: c := (n for each element of the round) / (|E| - 1). -/
theorem cnt_hitV_share (B : Set K) (n : ℕ) (e : Fmt.Entry) (k : Fmt.Kind)
    (H : cnt (fun a : EV .two => rd (toU3 a) ∈ B) ≤ n) :
    ((cnt (hitV rd B e k) : ℕ) : ℝ≥0∞) ≤
      ((sumDeg (fun _ => n) (Fmt.dsOf e k) 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) *
        ((Nat.card (Vals .two (Fmt.dsOf e k)) : ℕ) : ℝ≥0∞) := by
  rw [cnt_congr (hitV_iff_hitL rd B e k)]
  exact cnt_hit_share rd (fun _ => n) e k (fun _ => B) fun _ => H

/-! ### first case: deg = 0 -/

theorem hitBound_zero : ∀ (ds : List Fmt.Draw) (j : ℕ), hitBound (fun _ => 0) ds j = 0
  | [], _ => rfl
  | .elem :: ds, j => by
      show 0 * _ + _ * hitBound (fun _ => 0) ds (j + 1) = 0
      rw [hitBound_zero ds (j + 1), Nat.zero_mul, Nat.mul_zero]
  | .elemNZ :: ds, j => by
      show 0 * _ + _ * hitBound (fun _ => 0) ds (j + 1) = 0
      rw [hitBound_zero ds (j + 1), Nat.zero_mul, Nat.mul_zero]
  | .pos _ :: ds, j => by
      show _ * hitBound (fun _ => 0) ds j = 0
      rw [hitBound_zero ds j, Nat.mul_zero]
  | .trits _ :: ds, j => by
      show _ * hitBound (fun _ => 0) ds j = 0
      rw [hitBound_zero ds j, Nat.mul_zero]
  | .sealed :: ds, j => by
      show _ * hitBound (fun _ => 0) ds j = 0
      rw [hitBound_zero ds j, Nat.mul_zero]

theorem sumDeg_zero : ∀ (ds : List Fmt.Draw) (j : ℕ), sumDeg (fun _ => 0) ds j = 0
  | [], _ => rfl
  | .elem :: ds, j => by
      show 0 + sumDeg (fun _ => 0) ds (j + 1) = 0
      rw [sumDeg_zero ds (j + 1)]
  | .elemNZ :: ds, j => by
      show 0 + sumDeg (fun _ => 0) ds (j + 1) = 0
      rw [sumDeg_zero ds (j + 1)]
  | .pos _ :: ds, j => sumDeg_zero ds j
  | .trits _ :: ds, j => sumDeg_zero ds j
  | .sealed :: ds, j => sumDeg_zero ds j

/-- Where no typed element is read into any of the sets, no typed value hits. -/
theorem cnt_hit_zero (ds : List Fmt.Draw) (Bf : List Fmt.Ext → Set K)
    (H : ∀ xs (a : EV .two), rd (toU3 a) ∉ Bf xs) :
    cnt (fun v : Vals .two ds => hitL rd Bf (Fmt.collect (outAll .two ds v)).elems) = 0 :=
  Nat.le_zero.1 ((cnt_hit_le rd (fun _ => 0) ds 0 Bf fun xs =>
    le_of_eq (cnt_false (H xs))).trans (le_of_eq (hitBound_zero ds 0)))

/-! ### second case: no element among the draws -/

/-- No draw of the list is an element. -/
def NoElem (ds : List Fmt.Draw) : Prop := ∀ d ∈ ds, d ≠ .elem ∧ d ≠ .elemNZ

theorem NoElem.tail {d : Fmt.Draw} {ds : List Fmt.Draw} (h : NoElem (d :: ds)) : NoElem ds :=
  fun d' hd' => h d' (List.mem_cons_of_mem _ hd')

theorem hitBound_noElem (deg : ℕ → ℕ) : ∀ (ds : List Fmt.Draw) (j : ℕ), NoElem ds →
    hitBound deg ds j = 0
  | [], _, _ => rfl
  | .elem :: _, _, h => absurd rfl (h _ (List.mem_cons_self ..)).1
  | .elemNZ :: _, _, h => absurd rfl (h _ (List.mem_cons_self ..)).2
  | .pos _ :: ds, j, h => by
      show _ * hitBound deg ds j = 0
      rw [hitBound_noElem deg ds j h.tail, Nat.mul_zero]
  | .trits _ :: ds, j, h => by
      show _ * hitBound deg ds j = 0
      rw [hitBound_noElem deg ds j h.tail, Nat.mul_zero]
  | .sealed :: ds, j, h => by
      show _ * hitBound deg ds j = 0
      rw [hitBound_noElem deg ds j h.tail, Nat.mul_zero]

theorem sumDeg_noElem (deg : ℕ → ℕ) : ∀ (ds : List Fmt.Draw) (j : ℕ), NoElem ds →
    sumDeg deg ds j = 0
  | [], _, _ => rfl
  | .elem :: _, _, h => absurd rfl (h _ (List.mem_cons_self ..)).1
  | .elemNZ :: _, _, h => absurd rfl (h _ (List.mem_cons_self ..)).2
  | .pos _ :: ds, j, h => sumDeg_noElem deg ds j h.tail
  | .trits _ :: ds, j, h => sumDeg_noElem deg ds j h.tail
  | .sealed :: ds, j, h => sumDeg_noElem deg ds j h.tail

/-- A round without an element: no typed value hits, whatever the sets. -/
theorem cnt_hit_noElem (ds : List Fmt.Draw) (hn : NoElem ds) (Bf : List Fmt.Ext → Set K) :
    cnt (fun v : Vals .two ds => hitL rd Bf (Fmt.collect (outAll .two ds v)).elems) = 0 :=
  Nat.le_zero.1 ((cnt_hit_le rd (fun _ => Fintype.card (EV .two)) ds 0 Bf fun _ =>
    cnt_le_card _).trans (le_of_eq (hitBound_noElem _ ds 0 hn)))

/-- The draws of a round of matrix entries, and of a sealing. -/
theorem noElem_toys :
    NoElem [.trits 40] ∧ NoElem [.trits 0, .sealed] ∧ NoElem [.pos 10, .trits 0] := by
  unfold NoElem
  decide

/-! ### third case: one element -/

theorem hitBound_one (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds) :
    hitBound deg (.elem :: ds) j = deg j * Fintype.card (Vals .two ds) := by
  show deg j * _ + _ * hitBound deg ds (j + 1) = _
  rw [hitBound_noElem deg ds (j + 1) hn, Nat.mul_zero, Nat.add_zero]

theorem hitBound_oneNZ (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds) :
    hitBound deg (.elemNZ :: ds) j = deg j * Fintype.card (Vals .two ds) := by
  show deg j * _ + _ * hitBound deg ds (j + 1) = _
  rw [hitBound_noElem deg ds (j + 1) hn, Nat.mul_zero, Nat.add_zero]

theorem sumDeg_one (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds) :
    sumDeg deg (.elem :: ds) j = deg j ∧ sumDeg deg (.elemNZ :: ds) j = deg j := by
  constructor <;>
  · show deg j + sumDeg deg ds (j + 1) = deg j
    rw [sumDeg_noElem deg ds (j + 1) hn, Nat.add_zero]

/-- One plain element: the share is deg j / |E|, which is better than deg j / (|E| - 1). -/
theorem hitBound_one_share (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds) :
    hitBound deg (.elem :: ds) j * Fintype.card (EV .two) =
      deg j * Fintype.card (Vals .two (.elem :: ds)) := by
  rw [hitBound_one deg ds j hn, card_vals_cons]
  exact Nat.mul_assoc _ _ _ |>.trans (congrArg _ (Nat.mul_comm _ _))

/-- One element other than 0: the share is deg j / (|E| - 1): `hitBound_share` with equality. -/
theorem hitBound_oneNZ_share (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds) :
    hitBound deg (.elemNZ :: ds) j * Fintype.card (NZ .two) =
      sumDeg deg (.elemNZ :: ds) j * Fintype.card (Vals .two (.elemNZ :: ds)) := by
  rw [hitBound_oneNZ deg ds j hn, (sumDeg_one deg ds j hn).2, card_vals_cons]
  exact Nat.mul_assoc _ _ _ |>.trans (congrArg _ (Nat.mul_comm _ _))

/-- From below: whatever is read into the first set hits, with any values of the later draws. -/
theorem cnt_hit_ge (ds : List Fmt.Draw) (Bf : List Fmt.Ext → Set K) :
    cnt (fun a : EV .two => rd (toU3 a) ∈ Bf []) * Fintype.card (Vals .two ds) ≤
      cnt (fun v : Vals .two (.elem :: ds) =>
        hitL rd Bf (Fmt.collect (outAll .two (.elem :: ds) v)).elems) := by
  rw [← cnt_fst (D := Vals .two ds) (fun a : EV .two => rd (toU3 a) ∈ Bf [])]
  exact cnt_mono (α := EV .two × Vals .two ds) fun v hv =>
    ⟨[], toU3 v.1, (Fmt.collect (outAll .two ds v.2)).elems, rfl, hv⟩

/-- One plain element whose set takes exactly deg j typed elements: the bound is met. -/
theorem cnt_hit_eq_one (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) (hn : NoElem ds)
    (Bf : List Fmt.Ext → Set K)
    (H : ∀ xs, cnt (fun a : EV .two => rd (toU3 a) ∈ Bf xs) ≤ deg (j + xs.length))
    (h0 : cnt (fun a : EV .two => rd (toU3 a) ∈ Bf []) = deg j) :
    cnt (fun v : Vals .two (.elem :: ds) =>
      hitL rd Bf (Fmt.collect (outAll .two (.elem :: ds) v)).elems) =
      hitBound deg (.elem :: ds) j :=
  le_antisymm (cnt_hit_le rd deg (.elem :: ds) j Bf H) (by
    rw [hitBound_one deg ds j hn, ← h0]
    exact cnt_hit_ge rd ds Bf)

theorem card_vals_trits0 : Fintype.card (Vals .two [.trits 0]) = 1 := by
  rw [← Nat.card_eq_fintype_card, card_vals_all]
  rfl

/-- The draws of the toy plan's first round, the reading that changes nothing, the set of one typed
element: deg = 1, and exactly one typed value hits. -/
theorem toy_one (a₀ : EV .two) :
    cnt (fun v : Vals .two [.elem, .trits 0] =>
      hitL id (fun _ => ({toU3 a₀} : Set Fmt.Ext))
        (Fmt.collect (outAll .two [.elem, .trits 0] v)).elems) = 1 := by
  have h1 : cnt (fun a : EV .two => id (toU3 a) ∈ ({toU3 a₀} : Set Fmt.Ext)) = 1 := by
    refine (cnt_congr (Q := fun a : EV .two => a = a₀) fun a =>
      ⟨fun h => toU3_inj (Set.mem_singleton_iff.1 h),
        fun h => Set.mem_singleton_iff.2 (congrArg toU3 h)⟩).trans ?_
    exact cnt_eq_const a₀
  have hn : NoElem [.trits 0] := by
    unfold NoElem
    decide
  rw [cnt_hit_eq_one id (fun _ => 1) [.trits 0] 0 hn (fun _ => {toU3 a₀}) (fun _ => le_of_eq h1) h1,
    hitBound_one _ _ _ hn, card_vals_trits0]

/-- There the price with the work not counted is 1 / (|E| - 1). -/
theorem toy_one_sumDeg : sumDeg (fun _ => 1) [.elem, .trits 0] 0 = 1 := rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.cnt_hit_le
#print axioms OnBytes.Flat.cnt_mem_le
#print axioms OnBytes.Flat.hitBound_share
#print axioms OnBytes.Flat.cnt_hit_share_ds
#print axioms OnBytes.Flat.cnt_hit_share
#print axioms OnBytes.Flat.hitV_iff_hitL
#print axioms OnBytes.Flat.cnt_hitV_share
#print axioms OnBytes.Flat.hitBound_zero
#print axioms OnBytes.Flat.sumDeg_zero
#print axioms OnBytes.Flat.cnt_hit_zero
#print axioms OnBytes.Flat.hitBound_noElem
#print axioms OnBytes.Flat.sumDeg_noElem
#print axioms OnBytes.Flat.cnt_hit_noElem
#print axioms OnBytes.Flat.noElem_toys
#print axioms OnBytes.Flat.hitBound_one
#print axioms OnBytes.Flat.hitBound_oneNZ
#print axioms OnBytes.Flat.sumDeg_one
#print axioms OnBytes.Flat.hitBound_one_share
#print axioms OnBytes.Flat.hitBound_oneNZ_share
#print axioms OnBytes.Flat.cnt_hit_ge
#print axioms OnBytes.Flat.cnt_hit_eq_one
#print axioms OnBytes.Flat.toy_one
#print axioms OnBytes.Flat.toy_one_sumDeg
