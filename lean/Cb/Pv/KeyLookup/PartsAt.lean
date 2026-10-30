-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsAt.lean: the mathematics of Cb/Pv/KeyLookup/PartsAlg.lean and
Cb/Pv/KeyLookup/PartsMu.lean at the records of Cb/Pv/KeyLookup/Letters.lean: the count of the first
draw of a lookup with parts.

The file imports no file of the program. S is a record of public numbers and shapes (Pub), A a
record of data over it (Dat).

Main names.
  S.pads            the public list of padding: the one pair (padRow, padCount).
  Pub.allKeys_sum   S.allKeys, a sum over the list of parts, is allKeys S.m S.v.
  Pub.padCount_le_of   if every run's part is a part and no part is all padding, then padCount ≤
                    allKeys. So the clause pads of Pub.Adm follows from inPart and notAll.
  Pub.Adm.alg, Pub.Adm.padsOK   S.Adm p gives Adm p m v d mu pl and the test padsOKQ.
  Dat.in_iff, rest_eq, fac_eq, pow_range   the values of the record are those of PartsAlg.lean.
  Dat.mid_iff       (Bts ∧ Num) ∧ "rest 0 = fac * pow 0", which is what the joint after the first
                    draw says beside the rows, holds exactly if MidQ holds.
  Dat.cnt_draw      the count of the first draw: under A.Adm p, for every state and all entries,
                    that claim holds while A.In fails at no more than A.allKeys - 1 values of the
                    draw.
  Dat.err_lt        that bound is below the number of elements of the field.
  Dat.fac_zero      with padding the factor is 0, so not 1, at the padding's row.
  Run.holds_iff, Run.card_own, card_any, Pub.card_pad   under S.Adm p the places that isPad names,
                    all parts together, are padCount.
  Dat.MuOn, Dat.ValidMu, Dat.muOn_valid   MuOnQ and ValidQ at the record; under A.Adm p the
                    predicate ValidMu meets MuOn.
  Dat.IsMult        every key is the row chosen for it (row: an argument), a place of padding has
                    padRow chosen, and the cells of the real planes hold the digits of the counts,
                    padding not counted.
  Dat.muOn_mult, Dat.isMult_in, Dat.isMult_validMu   under A.Adm p the predicate IsMult meets MuOn;
                    IsMult gives In and ValidMu.
  Dat.CellsApart    the cells of the real planes are different entries.

Conditions: A.Adm p, on public numbers and shapes, alone.

Limits. IsMult can hold only at data whose places of padding hold the padding's row (Dat.PadIs of
Letters.lean) and whose cells differ wherever the digits differ (CellsApart suffices). Neither is a
premise here: without them IsMult is empty and muOn_mult says nothing. No witness against emptiness
rides here. Nothing on rounds or blocks.

-/
import Cb.Pv.KeyLookup.Letters
import Cb.Pv.KeyLookup.PartsMu

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Prob Cb.Lkp

theorem sum_map_getD (f : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map f).sum = ∑ i ∈ range l.length, f (l.getD i 0)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', sum_map_getD f l]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact Nat.add_comm _ _

theorem sum_padIn (m : ℕ) : ∀ l : List Run, (∀ r ∈ l, r.part < m) →
    ∑ i ∈ range m, ((l.filter fun r => r.part == i).map (·.length)).sum = (l.map (·.length)).sum
  | [], _ => by simp
  | r :: l, h => by
    have ih := sum_padIn m l fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have hr : r.part < m := h r List.mem_cons_self
    have e : ∀ i, (((r :: l).filter fun r' => r'.part == i).map (·.length)).sum =
        (if r.part = i then r.length else 0) +
          ((l.filter fun r' => r'.part == i).map (·.length)).sum := by
      intro i
      by_cases hi : r.part = i
      · simp [hi]
      · simp [hi]
    simp only [e]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq, if_pos (mem_range.2 hr)]
    simp

/-! ### the places of padding are as many as the runs' lengths say -/

theorem Run.holds_iff (r : Run) (i b : ℕ) :
    r.holds i b = true ↔ r.part = i ∧ ∃ k < r.length, b = r.first + k * 2 ^ r.logStep := by
  have hpos : 0 < 2 ^ r.logStep := by positivity
  unfold Run.holds
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, (b - r.first) / 2 ^ r.logStep, h4, ?_⟩
    have h5 := Nat.div_add_mod (b - r.first) (2 ^ r.logStep)
    rw [h3, Nat.add_zero, Nat.mul_comm] at h5
    omega
  · rintro ⟨h1, k, hk, rfl⟩
    refine ⟨⟨⟨h1, Nat.le_add_right _ _⟩, ?_⟩, ?_⟩
    · rw [Nat.add_sub_cancel_left, Nat.mul_mod_left]
    · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hpos]
      exact hk

theorem Run.card_own (r : Run) (n : ℕ) (h1 : 1 ≤ r.length)
    (h2 : r.first + (r.length - 1) * 2 ^ r.logStep < n) :
    ((range n).filter fun b => r.holds r.part b = true).card = r.length := by
  have hpos : 0 < 2 ^ r.logStep := by positivity
  have e : ((range n).filter fun b => r.holds r.part b = true) =
      (range r.length).image fun k => r.first + k * 2 ^ r.logStep := by
    ext b
    simp only [mem_filter, mem_range, mem_image, Run.holds_iff, true_and]
    constructor
    · rintro ⟨_, k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨lt_of_le_of_lt ?_ h2, k, hk, rfl⟩
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  rw [e, Finset.card_image_of_injective, card_range]
  intro k k' hkk
  exact Nat.eq_of_mul_eq_mul_right hpos (Nat.add_left_cancel hkk)

theorem Run.sum_card (r : Run) (m : ℕ) (v : ℕ → ℕ) (h0 : r.part < m) (h1 : 1 ≤ r.length)
    (h2 : r.first + (r.length - 1) * 2 ^ r.logStep < 2 ^ v r.part) :
    ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => r.holds i b = true).card = r.length := by
  rw [Finset.sum_eq_single r.part, r.card_own _ h1 h2]
  · intro i _ hi
    rw [Finset.filter_false_of_mem, Finset.card_empty]
    intro b _ hb
    exact hi ((r.holds_iff i b).1 hb).1.symm
  · intro h
    exact absurd (mem_range.2 h0) h

theorem card_any (m : ℕ) (v : ℕ → ℕ) : ∀ l : List Run,
    (∀ r ∈ l, r.part < m ∧ 1 ≤ r.length ∧
      r.first + (r.length - 1) * 2 ^ r.logStep < 2 ^ v r.part) →
    l.Pairwise (fun a b => ∀ i k, ¬ (a.holds i k = true ∧ b.holds i k = true)) →
    ∑ i ∈ range m, ((range (2 ^ v i)).filter fun b => l.any (fun r => r.holds i b) = true).card =
      (l.map (·.length)).sum
  | [], _, _ => by simp
  | r :: l, h, hp => by
    have ih := card_any m v l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      (List.pairwise_cons.1 hp).2
    have hr := h r List.mem_cons_self
    have hd := (List.pairwise_cons.1 hp).1
    have e : ∀ i,
        ((range (2 ^ v i)).filter fun b => (r :: l).any (fun r => r.holds i b) = true).card =
        ((range (2 ^ v i)).filter fun b => r.holds i b = true).card +
        ((range (2 ^ v i)).filter fun b => l.any (fun r => r.holds i b) = true).card := by
      intro i
      have hdis : Disjoint ((range (2 ^ v i)).filter fun b => r.holds i b = true)
          ((range (2 ^ v i)).filter fun b => l.any (fun r => r.holds i b) = true) :=
        Finset.disjoint_filter.2 fun b _ h1 h2 => by
          obtain ⟨r', hr', h3⟩ := List.any_eq_true.1 h2
          exact hd r' hr' i b ⟨h1, h3⟩
      rw [← Finset.card_union_of_disjoint hdis, ← Finset.filter_or]
      refine congrArg card (Finset.filter_congr fun b _ => ?_)
      simp [List.any_cons]
    simp only [e]
    rw [Finset.sum_add_distrib, ih, r.sum_card m v hr.1 hr.2.1 hr.2.2]
    simp

namespace Pub
variable (S : Pub)

/-- The public list of padding: one row, all places. -/
def pads : List (ℕ × ℕ) := [(S.padRow, S.padCount)]

theorem padNum_pads : padNum S.pads = S.padCount := by simp [pads, padNum]

theorem allKeys_sum : S.allKeys = Lk6.allKeys S.m S.v := sum_map_getD (fun x => 2 ^ x) S.parts

theorem padCount_le_of (h1 : ∀ r ∈ S.runs, r.part < S.m) (h2 : ∀ i < S.m, S.padIn i < 2 ^ S.v i) :
    S.padCount ≤ S.allKeys := by
  rw [allKeys_sum]
  unfold padCount Lk6.allKeys
  rw [← sum_padIn S.m S.runs h1]
  exact Finset.sum_le_sum fun i hi => le_of_lt (h2 i (mem_range.1 hi))

/-- The places of padding, all parts together, are padCount. -/
theorem card_pad {p : ℕ} (h : S.Adm p) :
    ∑ i ∈ range S.m, ((range (2 ^ S.v i)).filter fun b => S.isPad i b = true).card = S.padCount :=
  card_any S.m S.v S.runs h.inPart h.apart

theorem Adm.alg {S : Pub} {p : ℕ} (h : S.Adm p) : Lk6.Adm p S.m S.v S.d S.mu S.pl :=
  ⟨h.room, S.allKeys_sum ▸ h.keys, h.char⟩

theorem Adm.rows {S : Pub} {p : ℕ} (h : S.Adm p) : ∀ e ∈ S.pads, e.1 < 2 ^ S.d := by
  intro e he
  obtain rfl : e = (S.padRow, S.padCount) := by simpa [Pub.pads] using he
  exact h.row

theorem Adm.padsOK {S : Pub} {p : ℕ} (h : S.Adm p) :
    padsOKQ (Lk6.allKeys S.m S.v) S.d S.pads = true := by
  unfold padsOKQ
  rw [Bool.and_eq_true_iff]
  refine ⟨List.all_eq_true.mpr fun e he => decide_eq_true (h.rows e he), decide_eq_true ?_⟩
  rw [S.padNum_pads, ← S.allKeys_sum]
  exact h.pads

end Pub

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)

theorem in_iff (st : A.St) (μ : A.J → E) :
    A.In st μ ↔ InParts A.m A.v A.d (A.key st μ) (A.tab st) := Iff.rfl

theorem rest_eq (st : A.St) (μ : A.J → E) (al : E) (k : ℕ) :
    A.rest st μ al k = restProd A.m A.v (A.key st μ) al k := rfl

theorem rest_zero (st : A.St) (μ : A.J → E) (al : E) :
    A.rest st μ al 0 = rootsProd A.m A.v (A.key st μ) al :=
  restProd_zero A.m A.v (A.key st μ) al

theorem fac_eq (st : A.St) (al : E) : A.fac st al = padFac (A.tab st) A.pads al := by
  simp [fac, Pub.pads, padFac]

theorem pow_range (st : A.St) (μ : A.J → E) (al : E) :
    A.pow st μ al 0 = ∏ j ∈ range A.pl, tabProd A.d (A.tab st) (A.bit μ) al j ^ 2 ^ j := by
  unfold pow plane
  rw [Finset.range_eq_Ico]
  exact Finset.prod_congr rfl fun j _ => by rw [Nat.sub_zero]

/-- What the joint after the draw says beside the rows is the algebra's relation after the
challenge. -/
theorem mid_iff (st : A.St) (μ : A.J → E) (al : E) :
    ((A.Bts μ ∧ A.Num μ) ∧ A.rest st μ al 0 = A.fac st al * A.pow st μ al 0) ↔
      MidQ A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads (A.bit μ) al := by
  unfold MidQ Ident Pin Bts Num
  rw [A.rest_zero, A.fac_eq, A.pow_range, A.padNum_pads, A.allKeys_sum, and_assoc]

/-- The count of the first draw. -/
theorem cnt_draw (p : ℕ) [CharP E p] (hA : A.Adm p) (st : A.St) (μ : A.J → E) :
    cnt (fun al : E =>
      ((A.Bts μ ∧ A.Num μ) ∧ A.rest st μ al 0 = A.fac st al * A.pow st μ al 0) ∧ ¬ A.In st μ) ≤
      A.allKeys - 1 := by
  rw [A.allKeys_sum]
  refine le_trans (cnt_mono fun al h => ?_)
    (cnt_badAl_le p A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads (A.bit μ) hA.alg hA.padsOK)
  exact ⟨(A.mid_iff st μ al).1 h.1, h.2⟩

theorem err_lt (p : ℕ) [CharP E p] (hA : A.Adm p) : A.allKeys - 1 < Fintype.card E := by
  rw [A.allKeys_sum]
  exact err_lt_card p hA.alg

/-- MuOnQ at the record. -/
def MuOn (Mu : A.St → (A.J → E) → Prop) : Prop :=
  ∀ st μ, A.In st μ → Mu st μ → ∀ al : E,
    (A.Bts μ ∧ A.Num μ) ∧ A.rest st μ al 0 = A.fac st al * A.pow st μ al 0

/-- ValidQ at the record. -/
def ValidMu : A.St → (A.J → E) → Prop := fun st μ =>
  ValidQ A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads (A.bit μ)

theorem muOn_iff (Mu : A.St → (A.J → E) → Prop) :
    A.MuOn Mu ↔ MuOnQ A.m A.v A.d A.mu A.pl A.key A.tab A.pads A.bit Mu :=
  ⟨fun h st μ hin hm al => (A.mid_iff st μ al).1 (h st μ hin hm al),
    fun h st μ hin hm al => (A.mid_iff st μ al).2 (h st μ hin hm al)⟩

/-- ValidMu meets MuOn. -/
theorem muOn_valid {p : ℕ} (hA : A.Adm p) : A.MuOn A.ValidMu :=
  (A.muOn_iff _).2 (muOnQ_valid A.m A.v A.d A.mu A.pl A.key A.tab A.pads A.bit hA.room hA.rows)

/-! ### the digits of the counts at the record -/

/-- The honest side at the letters. row: the prover's choice of a row for each key (an argument).
Every key is the row chosen for it; a place of padding has the padding's row chosen; the live
entries are the binary digits of the counts, PADDING NOT COUNTED. -/
def IsMult (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) : A.St → (A.J → E) → Prop := fun st μ =>
  (∀ i < A.m, ∀ b < 2 ^ A.v i,
    row st μ i b < 2 ^ A.d ∧ A.key st μ i b = A.tab st (row st μ i b)) ∧
  (∀ i < A.m, ∀ b < 2 ^ A.v i, A.isPad i b = true → row st μ i b = A.padRow) ∧
  ∀ u < 2 ^ A.d, ∀ j < A.pl, μ (A.bAt u j) = hbitQ A.m A.v A.pl A.isPad (row st μ) u j

theorem isMult_laid {p : ℕ} (hA : A.Adm p) (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) (st : A.St)
    (μ : A.J → E) (h : A.IsMult row st μ) :
    LaidQ A.m A.v A.d (A.key st μ) (A.tab st) A.pads A.isPad (row st μ) := by
  refine ⟨fun i hi b hb => (h.1 i hi b hb).1, fun i hi b hb => (h.1 i hi b hb).2, fun u _ => ?_⟩
  have e : padCnt A.pads u = if A.padRow = u then A.padCount else 0 := by simp [Pub.pads, padCnt]
  rw [e]
  by_cases hu : A.padRow = u
  · rw [if_pos hu, ← A.card_pad hA]
    refine Finset.sum_congr rfl fun i hi => congrArg card ?_
    refine (Finset.filter_true_of_mem fun b hb => ?_).symm
    rw [← hu]
    exact h.2.1 i (mem_range.1 hi) b (mem_range.1 (mem_filter.1 hb).1) (mem_filter.1 hb).2
  · rw [if_neg hu]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [Finset.filter_false_of_mem, Finset.card_empty]
    intro b hb he
    exact hu ((h.2.1 i (mem_range.1 hi) b (mem_range.1 (mem_filter.1 hb).1)
      (mem_filter.1 hb).2).symm.trans he)

theorem isMult_bit (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) (st : A.St) (μ : A.J → E)
    (h : A.IsMult row st μ) :
    ∀ u < 2 ^ A.d, ∀ j < 2 ^ A.mu, A.bit μ u j = hbitQ A.m A.v A.pl A.isPad (row st μ) u j := by
  intro u hu j _
  unfold bit
  by_cases hj : j < A.pl
  · rw [if_pos hj]
    exact h.2.2 u hu j hj
  · rw [if_neg hj]
    unfold hbitQ
    rw [if_neg fun hc => hj hc.1]

/-- The digits of the counts, padding not counted, meet MuOn. -/
theorem muOn_mult {p : ℕ} (hA : A.Adm p) (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) :
    A.MuOn (A.IsMult row) := fun st μ _ hm al =>
  (A.mid_iff st μ al).2
    (midQ_congr A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads _ _ al hA.room
      (A.isMult_bit row st μ hm)
      (honestQ A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads A.isPad (row st μ) hA.room
        hA.alg.fits hA.rows (A.isMult_laid hA row st μ hm) al))

/-- The honest counts are a valid vector. -/
theorem isMult_validMu {p : ℕ} (hA : A.Adm p) (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) (st : A.St)
    (μ : A.J → E) (h : A.IsMult row st μ) : A.ValidMu st μ :=
  validQ_congr A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads _ _ hA.room
    (A.isMult_bit row st μ h)
    (laidQ_valid A.m A.v A.d A.mu A.pl (A.key st μ) (A.tab st) A.pads A.isPad (row st μ)
      hA.alg.fits (A.isMult_laid hA row st μ h))

theorem isMult_in (row : A.St → (A.J → E) → ℕ → ℕ → ℕ) (st : A.St) (μ : A.J → E)
    (h : A.IsMult row st μ) : A.In st μ :=
  fun i hi b hb => ⟨row st μ i b, (h.1 i hi b hb).1, (h.1 i hi b hb).2⟩

/-- A property of the data, on shapes: the live cells lie apart. -/
def CellsApart : Prop :=
  ∀ u < 2 ^ A.d, ∀ j < A.pl, ∀ u' < 2 ^ A.d, ∀ j' < A.pl, A.bAt u j = A.bAt u' j' → u = u' ∧ j = j'

/-- With padding the factor is 0 at the padding's row. -/
theorem fac_zero (st : A.St) (h : 0 < A.padCount) : A.fac st (A.tab st A.padRow) = 0 := by
  unfold fac
  rw [sub_self, zero_pow (by omega)]

end Dat
end Lk6

#print axioms Lk6.Pub.padCount_le_of
#print axioms Lk6.Dat.mid_iff
#print axioms Lk6.Dat.cnt_draw
#print axioms Lk6.Dat.err_lt
#print axioms Lk6.Dat.muOn_valid
#print axioms Lk6.Pub.card_pad
#print axioms Lk6.Dat.muOn_mult
#print axioms Lk6.Dat.isMult_validMu
#print axioms Lk6.Dat.fac_zero
