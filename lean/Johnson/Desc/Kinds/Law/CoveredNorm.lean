-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CoveredNorm.lean: FOR THE SUB-ROW reads_covered_K06, THE NORMALIZATION's SHARE: EVERY ENTRY THAT THE FINAL NORMALIZATION's 29 FORMS AND
FOUR KEYS NAME IS AN ENTRY OF ONE OF ITS SEVEN READS, OR OF THE HEAD's WIDE READ, BELOW THE LENGTH SPENT. Beside Law/Covered.lean (the head's own
eleven forms).
  readLenN r   the length that the text spends of read r: the stream's two: 5 d / S2 (five limbs, an entry a block) · act at the keys:
               2 d · the row at the keys: NR + 21 (the norm's 99 digits and the head's 21) · the row's three others: NR.
  wideLenN     of the head's wide read ("wide i"): 4 d / S2 (aw and the remainder's high part, two limbs each).
  CoveredN f   each entry (array, virtual row, index) in f's own list of entries is one that "entry r i" names at an i < readLenN r, or
               that "wide i" names at an i < wideLenN. Closed under the forms' arithmetic (all of it is Aff.addMul).
  coveredN_forms   all 29 of FinalNorm.forms · coveredN_key: the four keys at more = 21. GENERIC IN THE READS' PLACES.
WHAT IT DOES NOT SAY: where "entry r i" lies (the seat's text) and that the table of tables gives each read a stretch of at least readLenN:
Law/ReadsFitNorm.lean. THE VARIABLES OF WHAT WAS HEARD (the nine sums, the seven products, the claimed sums, the end values, the three sumchecks'
start forms) ARE ASKED TO BE COVERED (HeardCovered): at a hearing's return they are bare slots, or forms on slots: not shown here. S2 ∣ d is a
premise (the tests on the plan ask it). Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Covered
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.NormSquares

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Ent)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)

variable [Sizes]

/-- The length that the text spends of a read of the normalization's. -/
def readLenN : FinalNorm.Read → Nat
  | .streamAtSquares | .streamAtNormed => 5 * d / S2
  | .actAtKeys => 2 * d
  | .rowAtKeys => NR + 21
  | .rowAtPV | .rowAtProducts | .rowAtNormed => NR

/-- The length that it spends of the head's wide read. -/
def wideLenN : Nat := 4 * d / S2

variable [Policy] [Request] [Token] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- Every entry that the form names is a read's entry below the length spent. -/
def CoveredN (f : Form) : Prop :=
  ∀ x, x ∈ f.ents.toList →
    (∃ (r : FinalNorm.Read) (i : Nat), i < readLenN r ∧
      ∃ y, y ∈ (FinalNorm.entry r i).ents.toList ∧ y.tree = x.tree ∧ y.row = x.row ∧ y.idx = x.idx) ∨
    ∃ i : Nat, i < wideLenN ∧
      ∃ y, y ∈ (FinalNorm.wide i).ents.toList ∧ y.tree = x.tree ∧ y.row = x.row ∧ y.idx = x.idx

theorem cN_addMul {a b : Form} (ha : CoveredN a) (hb : CoveredN b) (k : E) :
    CoveredN (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_ents] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact hb z hz

theorem cN_noEnts {f : Form} (h : f.ents = #[]) : CoveredN f := by
  intro x hx
  rw [h] at hx
  simp at hx

theorem cN_const (v : E) : CoveredN (Aff.ofConst v) := cN_noEnts rfl
theorem cN_slot (j : Nat) : CoveredN (Aff.slot j) := cN_noEnts rfl
theorem cN_entry {r : FinalNorm.Read} {i : Nat} (h : i < readLenN r) :
    CoveredN (FinalNorm.entry r i) := fun x hx => Or.inl ⟨r, i, h, x, hx, rfl, rfl, rfl⟩
theorem cN_wide {i : Nat} (h : i < wideLenN) : CoveredN (FinalNorm.wide i) :=
  fun x hx => Or.inr ⟨i, h, x, hx, rfl, rfl, rfl⟩
theorem cN_add {f g : Form} (hf : CoveredN f) (hg : CoveredN g) : CoveredN (f + g) :=
  cN_addMul hf hg _
theorem cN_sub {f g : Form} (hf : CoveredN f) (hg : CoveredN g) : CoveredN (f - g) :=
  cN_addMul hf hg _
theorem cN_scale {f : Form} (hf : CoveredN f) (k : E) : CoveredN (Aff.scale f k) :=
  cN_addMul (cN_noEnts rfl) hf _
theorem cN_smulE (k : E) {f : Form} (hf : CoveredN f) : CoveredN (k • f) := cN_scale hf _
theorem cN_smulN (n : Nat) {f : Form} (hf : CoveredN f) : CoveredN (n • f) := cN_scale hf _
theorem cN_sm (n : Nat) {f : Form} (hf : CoveredN f) : CoveredN (OnBytes.Desc.First.P6.sm n f) :=
  cN_scale hf _
theorem cN_addN {f : Form} (hf : CoveredN f) (n : Nat) :
    CoveredN (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) := cN_addMul hf (cN_const _) _

theorem cN_sumTo (n : Nat) (f : Nat → Form) (h : ∀ i, i < n → CoveredN (f i)) :
    CoveredN (sumTo n f) := by
  unfold sumTo
  induction n with
  | zero => exact cN_const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact cN_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

theorem cN_sumTo6 (n : Nat) (f : Nat → Form) (h : ∀ i, i < n → CoveredN (f i)) :
    CoveredN (OnBytes.Desc.First.P6.sumTo n f) := by
  unfold OnBytes.Desc.First.P6.sumTo
  induction n with
  | zero => exact cN_const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact cN_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

/-! ## The part's row -/

/-- n digits from j on, at the radix 256. -/
theorem cN_dig (D : Nat → Form) (hD : ∀ j, j < 99 → CoveredN (D j)) (j n : Nat) (h : j + n ≤ 99) :
    CoveredN (OnBytes.Desc.First.P6.dig D j n) :=
  cN_sumTo6 n _ fun i hi => cN_sm _ (hD _ (by omega))

/-- Every field of the row that the forms read is covered. -/
structure RowCovered (r : P6.Row) : Prop where
  Vlo : CoveredN r.Vlo
  Vhi : CoveredN r.Vhi
  a : CoveredN r.a
  b : CoveredN r.b
  s0 : CoveredN r.s0
  sig : CoveredN r.sig
  l1 : CoveredN r.l1
  h1 : CoveredN r.h1
  Blo : CoveredN r.Blo
  Bhi : CoveredN r.Bhi
  kap : CoveredN r.kap
  Rlo : CoveredN r.Rlo
  Rhi : CoveredN r.Rhi
  R : CoveredN r.R
  q1 : CoveredN r.q1
  rr : CoveredN r.rr
  rq : CoveredN r.rq
  c : ∀ s, s ≤ 9 → CoveredN (r.c s)

open OnBytes.Desc.First.P6 (sm nat dig) in
theorem rowCovered (D : Nat → Form) (hD : ∀ j, j < 99 → CoveredN (D j)) :
    RowCovered (P6.Row.ofDigits D) := by
  have dg := cN_dig D hD
  have ha : CoveredN (P6.Row.ofDigits D).a := by
    show CoveredN (sm 2 (D 58) + D 59 + sm (2 ^ 8) (D 60) + sm (2 ^ 16) (D 61))
    exact cN_add (cN_add (cN_add (cN_sm _ (hD 58 (by omega))) (hD 59 (by omega)))
      (cN_sm _ (hD 60 (by omega)))) (cN_sm _ (hD 61 (by omega)))
  have hb : CoveredN (P6.Row.ofDigits D).b := by
    show CoveredN (D 62 + sm (2 ^ 8) (D 63))
    exact cN_add (hD 62 (by omega)) (cN_sm _ (hD 63 (by omega)))
  have hlo : CoveredN (P6.Row.ofDigits D).Rlo := by
    show CoveredN (dig D 80 3)
    exact dg 80 3 (by omega)
  have hhi : CoveredN (P6.Row.ofDigits D).Rhi := by
    show CoveredN (dig D 83 3)
    exact dg 83 3 (by omega)
  constructor
  · show CoveredN (dig D 0 6)
    exact dg 0 6 (by omega)
  · show CoveredN (dig D 6 4)
    exact dg 6 4 (by omega)
  · exact ha
  · exact hb
  · exact hD 59 (by omega)
  · show CoveredN ((P6.Row.ofDigits D).a + sm (2 ^ 24) (P6.Row.ofDigits D).b)
    exact cN_add ha (cN_sm _ hb)
  · show CoveredN (dig D 64 5)
    exact dg 64 5 (by omega)
  · show CoveredN (dig D 69 5)
    exact dg 69 5 (by omega)
  · show CoveredN (dig D 74 3)
    exact dg 74 3 (by omega)
  · show CoveredN (dig D 77 2)
    exact dg 77 2 (by omega)
  · show CoveredN (D 79 - nat 4)
    exact cN_sub (hD 79 (by omega)) (cN_const _)
  · exact hlo
  · exact hhi
  · show CoveredN ((P6.Row.ofDigits D).Rlo + sm (2 ^ 24) (P6.Row.ofDigits D).Rhi)
    exact cN_add hlo (cN_sm _ hhi)
  · show CoveredN (dig D 86 3)
    exact dg 86 3 (by omega)
  · show CoveredN (dig D 89 5)
    exact dg 89 5 (by omega)
  · show CoveredN (dig D 94 5)
    exact dg 94 5 (by omega)
  · intro s hs
    show CoveredN (if s == 0 then nat 0 else if s == 9 then D 9
      else dig D (10 + 6 * (s - 1)) 6 - nat (2 ^ 47))
    split
    · exact cN_const _
    · rename_i h0
      split
      · exact hD 9 (by omega)
      · rename_i h9
        have h0' : s ≠ 0 := by simpa using h0
        have h9' : s ≠ 9 := by simpa using h9
        exact cN_sub (dg _ 6 (by omega)) (cN_const _)

/-- The part's nine forms of the carries. -/
theorem cN_carries (D Wf : Nat → Form) (hD : ∀ j, j < 99 → CoveredN (D j))
    (hW : ∀ s, s < 9 → CoveredN (Wf s)) :
    ∀ f, f ∈ OnBytes.Desc.First.P6.carries (P6.Row.ofDigits D) D Wf → CoveredN f := by
  intro f hf
  have R := rowCovered D hD
  rw [OnBytes.Desc.First.P6.carries_eq] at hf
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
  have hs' : s < 9 := List.mem_range.mp hs
  exact cN_sub (cN_sub (cN_add (hW s hs') (R.c s (by omega))) (hD s (by omega)))
    (cN_sm _ (R.c (s + 1) (by omega)))

/-- The part's eight lines. -/
theorem cN_lines (D P : Nat → Form) (eps : E) (two : Form) (hD : ∀ j, j < 99 → CoveredN (D j))
    (hP : ∀ n, n < 7 → CoveredN (P n)) (h2 : CoveredN two) :
    ∀ f, f ∈ OnBytes.Desc.First.P6.lines (P6.Row.ofDigits D) P eps two → CoveredN f := by
  intro f hf
  have R := rowCovered D hD
  rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
    OnBytes.Desc.First.P6.reciprocal_eq] at hf
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cN_sub (cN_sub (hP 1 (by omega)) R.Blo) (cN_sm _ R.Bhi)
  · exact cN_add (cN_sub (cN_sub (cN_sub (cN_add R.Vlo (cN_const _)) (hP 0 (by omega)))
      (cN_sm _ R.Blo)) R.l1) (cN_sm _ R.kap)
  · exact cN_sub (cN_sub (cN_sub R.Vhi R.Bhi) (hP 2 (by omega))) R.kap
  · exact cN_sub (cN_add R.l1 R.h1) (cN_sm _ R.sig)
  · exact cN_sub (cN_add (hP 4 (by omega)) (hP 5 (by omega))) R.q1
  · exact hP 6 (by omega)
  · exact cN_sub (cN_sub (cN_sub (cN_sub (cN_add h2 R.sig) R.s0) (cN_sm _ (hP 3 (by omega))))
      (cN_sm _ R.q1)) (cN_sm _ R.rr)
  · exact cN_add (cN_sub (cN_add R.rr R.rq) R.sig) (cN_const _)

/-! ## A sumcheck's own form -/

theorem cN_onSlots : ∀ (u : List E) (first : Nat) (f : Form), CoveredN f →
    CoveredN (Part.MaskedSum.onSlots f first u) := by
  intro u
  induction u with
  | nil => intro first f hf; exact hf
  | cons x xs ih =>
    intro first f hf
    exact ih (first + 1) _ (cN_addMul hf (cN_slot _) _)

theorem cN_left (s : Sum) (S0 : E) (hs : ∀ h, s.psc = some h → CoveredN h.start) :
    CoveredN (s.left S0) := by
  unfold Sum.left
  cases hp : s.psc with
  | none => exact cN_const _
  | some h =>
    show CoveredN (Part.MaskedSum.rowForm h S0 {})
    unfold Part.MaskedSum.rowForm
    exact cN_addMul (cN_addMul (cN_onSlots _ _ _ (cN_const _))
      (cN_sub (cN_const _) (hs h hp)) _) (cN_noEnts rfl) _

/-! ## The text's forms -/

/-- What is asked of the variables of what was heard. -/
structure HeardCovered : Prop where
  W : ∀ s, s < 9 → CoveredN (Norm.W.getD s {}).var
  P : ∀ n, n < 7 → CoveredN (Norm.P.getD n {}).var
  sqStart : ∀ h, Norm.squares.psc = some h → CoveredN h.start
  sqEnd : ∀ j, j < 2 → CoveredN (Norm.squares.end_ j).var
  prStart : ∀ h, Norm.products.psc = some h → CoveredN h.start
  prClaimed : CoveredN Norm.products.claimed.var
  prEnd : ∀ j, j < 4 → CoveredN (Norm.products.end_ j).var
  nmStart : ∀ h, FinalNorm.normed.psc = some h → CoveredN h.start
  nmClaimed : CoveredN FinalNorm.normed.claimed.var
  nmEnd : ∀ j, j < 2 → CoveredN (FinalNorm.normed.end_ j).var

theorem S2_posC : 0 < S2 := by unfold S2; exact Nat.pos_of_ne_zero (by simp)

/-- Block i of limb l of a matrix of n limbs of d features. -/
theorem limb_lt {l i n : Nat} (hd : S2 ∣ d) (hl : l < n) (hi : i < d / S2) :
    l * d / S2 + i < n * d / S2 := by
  obtain ⟨q, hq⟩ := hd
  have hS := S2_posC
  have e1 : l * d / S2 = l * q := by
    rw [hq, show l * (S2 * q) = S2 * (l * q) by ring, Nat.mul_div_cancel_left _ hS]
  have e2 : n * d / S2 = n * q := by
    rw [hq, show n * (S2 * q) = S2 * (n * q) by ring, Nat.mul_div_cancel_left _ hS]
  have e3 : d / S2 = q := by rw [hq, Nat.mul_div_cancel_left _ hS]
  rw [e1, e2]
  rw [e3] at hi
  have : (l + 1) * q ≤ n * q := Nat.mul_le_mul_right q hl
  nlinarith

theorem cN_digitPV (j : Nat) (hj : j < 99) : CoveredN (Norm.digit .rowsAtPV 0 j) :=
  cN_addN (cN_entry (r := .rowAtPV) hj) _
theorem cN_digitPr (j : Nat) (hj : j < 99) : CoveredN (Norm.digit .rowsAtProducts 0 j) :=
  cN_addN (cN_entry (r := .rowAtProducts) hj) _

/-- **ALL 29 FORMS.** -/
theorem coveredN_forms (hd : S2 ∣ d) (H : HeardCovered) :
    ∀ f, f ∈ FinalNorm.forms → CoveredN f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rw [squareForms_eq] at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact cN_left _ _ H.sqStart
        · exact cN_sub (H.sqEnd 0 (by omega)) (H.sqEnd 1 (by omega))
        · refine cN_sub (H.sqEnd 0 (by omega)) (cN_sumTo _ _ fun i _ => cN_sumTo _ _ fun k hk =>
            cN_sumTo _ _ fun l hl => cN_smulE _ ?_)
          exact cN_entry (r := .streamAtSquares) (limb_lt hd hl hk)
      · rw [productForms_eq] at hf
        have R := rowCovered (Norm.digit .rowsAtProducts 0) cN_digitPr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · exact cN_sub H.prClaimed (cN_sumTo _ _ fun n hn => cN_smulE _ (H.P n hn))
        · exact cN_left _ _ H.prStart
        · exact cN_sub (H.prEnd 0 (by omega)) R.a
        · exact cN_sub (H.prEnd 1 (by omega)) R.b
        · exact cN_sub (H.prEnd 2 (by omega)) R.Rlo
        · exact cN_sub (H.prEnd 3 (by omega)) R.Rhi
    · rw [rowForms_eq, List.mem_append] at hf
      rcases hf with hf | hf
      · exact cN_carries _ _ cN_digitPV (fun s hs => by
          rw [Nat.mul_zero, Nat.zero_add]; exact H.W s hs) f hf
      · exact cN_lines _ _ _ _ cN_digitPV (fun n hn => by
          rw [Nat.mul_zero, Nat.zero_add]; exact H.P n hn) (cN_const _) f hf
  · simp only [FinalNorm.normedForms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact cN_left _ _ H.nmStart
    · exact cN_sub (H.nmEnd 0 (by omega))
        (rowCovered _ fun j hj => cN_addN (cN_entry (r := .rowAtNormed) hj) _).R
    · refine cN_sub (H.nmEnd 1 (by omega)) (cN_sumTo _ _ fun i hi => cN_sumTo _ _ fun l hl =>
        cN_smulE _ ?_)
      exact cN_entry (r := .streamAtNormed) (limb_lt hd hl hi)

/-! ## The four keys -/

theorem cN_addE {f : Form} (hf : CoveredN f) (x : E) :
    CoveredN (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) := cN_addMul hf (cN_const _) _
theorem cN_Eadd (x : E) {f : Form} (hf : CoveredN f) :
    CoveredN (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) := cN_addMul (cN_const _) hf _

/-- Two limbs of the wide matrix from limb m on, m ≤ 2. -/
theorem cN_wideAt (hd : S2 ∣ d) (k : FinalNorm.Key) (m : Nat) (hm : m ≤ 2) :
    CoveredN (FinalNorm.wideAt k (m * d)) := by
  unfold FinalNorm.wideAt
  refine cN_sumTo _ _ fun i hi => cN_sumTo _ _ fun l hl => cN_smulE _ (cN_wide ?_)
  rw [← Nat.add_mul]
  exact limb_lt hd (show m + l < 4 by omega) hi

/-- **THE FOUR KEYS**, with the head's 21 digits behind the norm's 99. -/
theorem coveredN_key (hd : S2 ∣ d) (H : HeardCovered) (k : FinalNorm.Key) :
    CoveredN (FinalNorm.key 21 k) := by
  have w0 : ∀ k, CoveredN (FinalNorm.wideAt k 0) := fun k => by
    have := cN_wideAt hd k 0 (by omega)
    rwa [Nat.zero_mul] at this
  have w2 : ∀ k, CoveredN (FinalNorm.wideAt k (2 * d)) := fun k => cN_wideAt hd k 2 (by omega)
  cases k with
  | remLow =>
    exact cN_sub (cN_sub (cN_addE H.nmClaimed _) (cN_smulN _ (w0 _))) (cN_smulN _ (w2 _))
  | remHigh => exact cN_smulN _ (cN_Eadd _ (w2 _))
  | clamp =>
    refine cN_addE (cN_add (w0 _) (cN_smulN _ (cN_sumTo _ _ fun j hj => cN_smulE _ ?_))) _
    exact cN_add (cN_entry (r := .actAtKeys) (show j < 2 * d by omega))
      (cN_smulN _ (cN_entry (r := .actAtKeys) (show d + j < 2 * d by omega)))
  | digits =>
    exact cN_sumTo _ _ fun j hj => cN_smulE _ (cN_addN (cN_entry (r := .rowAtKeys) hj) _)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.coveredN_forms
#print axioms VerifiableInference.Desc.Kinds.Head.Law.coveredN_key
