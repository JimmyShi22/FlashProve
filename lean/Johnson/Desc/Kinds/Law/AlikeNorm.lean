-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AlikeNorm.lean.
WHAT IT DOES NOT SHOW. No soundness. The use of Law/AlikeHead.lean's tool on the normalization's
forms:
no law by itself. That any two fillings of the reads stand in a relation: premises (hN, hw). That
the
heard variables stand in the relation with themselves: a premise (HeardAlike): at a hearing's return
they name no entry (Law/CoveredNormAt.lean), so Kept2's second field gives it.
LETTERS. N, N': two fillings of the normalization's reads' places; Q: any relation that Kept2 asks;
under "there is": f: a member of the list at N.
OBJECT. Desc/Kinds/HeadNorm.lean's FinalNorm.forms (29) and FinalNorm.key 21 (four), at two fillings
of the class FinalNorm.Reads.
USER. As of Law/AlikeHead.lean.
WHAT IT IS. THE NORMALIZATION's 29 FORMS AND FOUR KEYS, MADE AT TWO FILLINGS OF THE READS' PLACES,
STAND
IN EVERY RELATION THAT THE FORMS' ARITHMETIC KEEPS AND THAT HOLDS OF THE TWO FILLINGS' ENTRIES BELOW
THE
LENGTHS SPENT. The walk, with every index's bound, is Law/CoveredNorm.lean's, for a relation of two.
  Kept2.sm, sumTo6, dig   the part's own arithmetic.
  RowAlike, rowAlike      the part's row, field by field, at two lists of digits.
  alike_carries, alike_lines   the part's nine and eight forms.
  HeardAlike        what is asked of the heard variables.
  alikeN_forms      all 29: to each member at N' a member at N.
  alikeN_key        the four keys.

-/
import Johnson.Desc.Kinds.Law.AlikeHead
import Johnson.Desc.Kinds.Law.CoveredNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)

namespace Kept2

variable {Q : Form → Form → Prop} (C : Kept2 Q)
include C

theorem sm (n : Nat) {f f' : Form} (hf : Q f f') :
    Q (OnBytes.Desc.First.P6.sm n f) (OnBytes.Desc.First.P6.sm n f') := C.scale hf _

theorem sumTo6 (n : Nat) (f f' : Nat → Form) (h : ∀ i, i < n → Q (f i) (f' i)) :
    Q (OnBytes.Desc.First.P6.sumTo n f) (OnBytes.Desc.First.P6.sumTo n f') := by
  unfold OnBytes.Desc.First.P6.sumTo
  induction n with
  | zero => exact C.const _
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact C.add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

theorem dig (D D' : Nat → Form) (hD : ∀ j, j < 99 → Q (D j) (D' j)) (j n : Nat)
    (h : j + n ≤ 99) :
    Q (OnBytes.Desc.First.P6.dig D j n) (OnBytes.Desc.First.P6.dig D' j n) :=
  C.sumTo6 n _ _ fun i hi => C.sm _ (hD _ (by omega))

end Kept2

/-- Every field of the row that the forms read, at two rows. -/
structure RowAlike (Q : Form → Form → Prop) (r r' : P6.Row) : Prop where
  Vlo : Q r.Vlo r'.Vlo
  Vhi : Q r.Vhi r'.Vhi
  a : Q r.a r'.a
  b : Q r.b r'.b
  s0 : Q r.s0 r'.s0
  sig : Q r.sig r'.sig
  l1 : Q r.l1 r'.l1
  h1 : Q r.h1 r'.h1
  Blo : Q r.Blo r'.Blo
  Bhi : Q r.Bhi r'.Bhi
  kap : Q r.kap r'.kap
  Rlo : Q r.Rlo r'.Rlo
  Rhi : Q r.Rhi r'.Rhi
  R : Q r.R r'.R
  q1 : Q r.q1 r'.q1
  rr : Q r.rr r'.rr
  rq : Q r.rq r'.rq
  c : ∀ s, s ≤ 9 → Q (r.c s) (r'.c s)

section Part

variable {Q : Form → Form → Prop} (C : Kept2 Q)
include C

open OnBytes.Desc.First.P6 (sm nat dig) in
theorem rowAlike (D D' : Nat → Form) (hD : ∀ j, j < 99 → Q (D j) (D' j)) :
    RowAlike Q (P6.Row.ofDigits D) (P6.Row.ofDigits D') := by
  have dg := C.dig D D' hD
  have ha : Q (P6.Row.ofDigits D).a (P6.Row.ofDigits D').a := by
    show Q (sm 2 (D 58) + D 59 + sm (2 ^ 8) (D 60) + sm (2 ^ 16) (D 61))
      (sm 2 (D' 58) + D' 59 + sm (2 ^ 8) (D' 60) + sm (2 ^ 16) (D' 61))
    exact C.add (C.add (C.add (C.sm _ (hD 58 (by omega))) (hD 59 (by omega)))
      (C.sm _ (hD 60 (by omega)))) (C.sm _ (hD 61 (by omega)))
  have hb : Q (P6.Row.ofDigits D).b (P6.Row.ofDigits D').b := by
    show Q (D 62 + sm (2 ^ 8) (D 63)) (D' 62 + sm (2 ^ 8) (D' 63))
    exact C.add (hD 62 (by omega)) (C.sm _ (hD 63 (by omega)))
  have hlo : Q (P6.Row.ofDigits D).Rlo (P6.Row.ofDigits D').Rlo := by
    show Q (dig D 80 3) (dig D' 80 3)
    exact dg 80 3 (by omega)
  have hhi : Q (P6.Row.ofDigits D).Rhi (P6.Row.ofDigits D').Rhi := by
    show Q (dig D 83 3) (dig D' 83 3)
    exact dg 83 3 (by omega)
  constructor
  · show Q (dig D 0 6) (dig D' 0 6)
    exact dg 0 6 (by omega)
  · show Q (dig D 6 4) (dig D' 6 4)
    exact dg 6 4 (by omega)
  · exact ha
  · exact hb
  · exact hD 59 (by omega)
  · show Q ((P6.Row.ofDigits D).a + sm (2 ^ 24) (P6.Row.ofDigits D).b)
      ((P6.Row.ofDigits D').a + sm (2 ^ 24) (P6.Row.ofDigits D').b)
    exact C.add ha (C.sm _ hb)
  · show Q (dig D 64 5) (dig D' 64 5)
    exact dg 64 5 (by omega)
  · show Q (dig D 69 5) (dig D' 69 5)
    exact dg 69 5 (by omega)
  · show Q (dig D 74 3) (dig D' 74 3)
    exact dg 74 3 (by omega)
  · show Q (dig D 77 2) (dig D' 77 2)
    exact dg 77 2 (by omega)
  · show Q (D 79 - nat 4) (D' 79 - nat 4)
    exact C.sub (hD 79 (by omega)) (C.const _)
  · exact hlo
  · exact hhi
  · show Q ((P6.Row.ofDigits D).Rlo + sm (2 ^ 24) (P6.Row.ofDigits D).Rhi)
      ((P6.Row.ofDigits D').Rlo + sm (2 ^ 24) (P6.Row.ofDigits D').Rhi)
    exact C.add hlo (C.sm _ hhi)
  · show Q (dig D 86 3) (dig D' 86 3)
    exact dg 86 3 (by omega)
  · show Q (dig D 89 5) (dig D' 89 5)
    exact dg 89 5 (by omega)
  · show Q (dig D 94 5) (dig D' 94 5)
    exact dg 94 5 (by omega)
  · intro s hs
    show Q (if s == 0 then nat 0 else if s == 9 then D 9
        else dig D (10 + 6 * (s - 1)) 6 - nat (2 ^ 47))
      (if s == 0 then nat 0 else if s == 9 then D' 9
        else dig D' (10 + 6 * (s - 1)) 6 - nat (2 ^ 47))
    by_cases h0 : (s == 0) = true
    · rw [if_pos h0, if_pos h0]
      exact C.const _
    · rw [if_neg h0, if_neg h0]
      by_cases h9 : (s == 9) = true
      · rw [if_pos h9, if_pos h9]
        exact hD 9 (by omega)
      · rw [if_neg h9, if_neg h9]
        have h0' : s ≠ 0 := by simpa using h0
        have h9' : s ≠ 9 := by simpa using h9
        exact C.sub (dg _ 6 (by omega)) (C.const _)

/-- The part's nine forms of the carries. -/
theorem alike_carries (D D' Wf : Nat → Form) (hD : ∀ j, j < 99 → Q (D j) (D' j))
    (hW : ∀ s, s < 9 → Q (Wf s) (Wf s)) :
    ∀ f', f' ∈ OnBytes.Desc.First.P6.carries (P6.Row.ofDigits D') D' Wf →
      ∃ f, f ∈ OnBytes.Desc.First.P6.carries (P6.Row.ofDigits D) D Wf ∧ Q f f' := by
  intro f' hf
  have R := rowAlike C D D' hD
  rw [OnBytes.Desc.First.P6.carries_eq] at hf
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
  have hs' : s < 9 := List.mem_range.mp hs
  refine ⟨_, ?_, C.sub (C.sub (C.add (hW s hs') (R.c s (by omega))) (hD s (by omega)))
    (C.sm _ (R.c (s + 1) (by omega)))⟩
  rw [OnBytes.Desc.First.P6.carries_eq]
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

/-- Membership in the part's eight lines, written out. -/
local macro "mem8" : tactic =>
  `(tactic| (rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
    OnBytes.Desc.First.P6.reciprocal_eq]; simp))

/-- The part's eight lines. -/
theorem alike_lines (D D' P : Nat → Form) (eps : E) (two : Form)
    (hD : ∀ j, j < 99 → Q (D j) (D' j)) (hP : ∀ n, n < 7 → Q (P n) (P n)) (h2 : Q two two) :
    ∀ f', f' ∈ OnBytes.Desc.First.P6.lines (P6.Row.ofDigits D') P eps two →
      ∃ f, f ∈ OnBytes.Desc.First.P6.lines (P6.Row.ofDigits D) P eps two ∧ Q f f' := by
  intro f' hf
  have R := rowAlike C D D' hD
  rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
    OnBytes.Desc.First.P6.reciprocal_eq] at hf
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by mem8, C.sub (C.sub (hP 1 (by omega)) R.Blo) (C.sm _ R.Bhi)⟩
  · exact ⟨_, by mem8, C.add (C.sub (C.sub (C.sub (C.add R.Vlo (C.const _)) (hP 0 (by omega)))
      (C.sm _ R.Blo)) R.l1) (C.sm _ R.kap)⟩
  · exact ⟨_, by mem8, C.sub (C.sub (C.sub R.Vhi R.Bhi) (hP 2 (by omega))) R.kap⟩
  · exact ⟨_, by mem8, C.sub (C.add R.l1 R.h1) (C.sm _ R.sig)⟩
  · exact ⟨_, by mem8, C.sub (C.add (hP 4 (by omega)) (hP 5 (by omega))) R.q1⟩
  · exact ⟨_, by mem8, hP 6 (by omega)⟩
  · exact ⟨_, by mem8, C.sub (C.sub (C.sub (C.sub (C.add h2 R.sig) R.s0) (C.sm _ (hP 3 (by omega))))
      (C.sm _ R.q1)) (C.sm _ R.rr)⟩
  · refine ⟨_, ?_, C.add (C.sub (C.add R.rr R.rq) R.sig) (C.const _)⟩
    rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
      OnBytes.Desc.First.P6.reciprocal_eq]
    exact List.mem_of_getElem? (i := 7) rfl

end Part

section Norm

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard]

/-- A form as a function of the filling of the normalization's reads, at the two fillings. -/
abbrev RelN (Q : Form → Form → Prop) (N N' : FinalNorm.Reads) (t : [FinalNorm.Reads] → Form) :
    Prop := Q (@t N) (@t N')

/-- The like of a list: to each member at N' a member at N. -/
abbrev ListRelN (Q : Form → Form → Prop) (N N' : FinalNorm.Reads)
    (t : [FinalNorm.Reads] → List Form) : Prop :=
  ∀ f', f' ∈ @t N' → ∃ f, f ∈ @t N ∧ Q f f'

/-- What is asked of the variables of what was heard: each stands in the relation with itself. -/
structure HeardAlike (Q : Form → Form → Prop) : Prop where
  W : ∀ s, s < 9 → Q (Norm.W.getD s {}).var (Norm.W.getD s {}).var
  P : ∀ n, n < 7 → Q (Norm.P.getD n {}).var (Norm.P.getD n {}).var
  sqLeft : ∀ S0, Q (Norm.squares.left S0) (Norm.squares.left S0)
  sqEnd : ∀ j, j < 2 → Q (Norm.squares.end_ j).var (Norm.squares.end_ j).var
  prLeft : ∀ S0, Q (Norm.products.left S0) (Norm.products.left S0)
  prClaimed : Q Norm.products.claimed.var Norm.products.claimed.var
  prEnd : ∀ j, j < 4 → Q (Norm.products.end_ j).var (Norm.products.end_ j).var
  nmLeft : ∀ S0, Q (FinalNorm.normed.left S0) (FinalNorm.normed.left S0)
  nmClaimed : Q FinalNorm.normed.claimed.var FinalNorm.normed.claimed.var
  nmEnd : ∀ j, j < 2 → Q (FinalNorm.normed.end_ j).var (FinalNorm.normed.end_ j).var

variable {Q : Form → Form → Prop} (C : Kept2 Q) (N N' : FinalNorm.Reads)
  (hN : ∀ r i, i < readLenN r → Q (N.entry r i) (N'.entry r i))
  (hw : ∀ i, i < wideLenN → Q (N.wide i) (N'.wide i))
include C hN

theorem alike_digitPV (j : Nat) (hj : j < 99) : RelN Q N N' (Norm.digit .rowsAtPV 0 j) :=
  C.addN (hN .rowAtPV j hj) _
theorem alike_digitPr (j : Nat) (hj : j < 99) : RelN Q N N' (Norm.digit .rowsAtProducts 0 j) :=
  C.addN (hN .rowAtProducts j hj) _

/-- The three of the squares' level. -/
theorem alike_squares (hd : S2 ∣ d) (H : HeardAlike Q) : ListRelN Q N N' Norm.squareForms := by
  intro f' hf
  beta_reduce at hf ⊢
  rw [@squareForms_eq _ _ _ _ _ _ _ N'] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨_, by rw [@squareForms_eq _ _ _ _ _ _ _ N]; simp, H.sqLeft _⟩
  · exact ⟨_, by rw [@squareForms_eq _ _ _ _ _ _ _ N]; simp,
      C.sub (H.sqEnd 0 (by omega)) (H.sqEnd 1 (by omega))⟩
  · refine ⟨_, by rw [@squareForms_eq _ _ _ _ _ _ _ N]; exact List.mem_of_getElem? (i := 2) rfl,
      C.sub (H.sqEnd 0 (by omega)) (C.sumTo _ _ _ fun i _ => C.sumTo _ _ _ fun k hk =>
        C.sumTo _ _ _ fun l hl => C.smulE _ ?_)⟩
    exact hN .streamAtSquares _ (limb_lt hd hl hk)

/-- The six of the products. -/
theorem alike_products (H : HeardAlike Q) : ListRelN Q N N' Norm.productForms := by
  intro f' hf
  beta_reduce at hf ⊢
  rw [@productForms_eq _ _ _ _ _ _ _ N'] at hf
  have R := rowAlike C (fun j => letI := N; Norm.digit .rowsAtProducts 0 j)
    (fun j => letI := N'; Norm.digit .rowsAtProducts 0 j) (alike_digitPr C N N' hN)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp,
      C.sub H.prClaimed (C.sumTo _ _ _ fun n hn => C.smulE _ (H.P n hn))⟩
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp, H.prLeft _⟩
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp, C.sub (H.prEnd 0 (by omega)) R.a⟩
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp, C.sub (H.prEnd 1 (by omega)) R.b⟩
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp,
      C.sub (H.prEnd 2 (by omega)) R.Rlo⟩
  · exact ⟨_, by rw [@productForms_eq _ _ _ _ _ _ _ N]; simp,
      C.sub (H.prEnd 3 (by omega)) R.Rhi⟩

/-- The seventeen of the row. -/
theorem alike_rows (H : HeardAlike Q) : ListRelN Q N N' Norm.rowForms := by
  intro f' hf
  beta_reduce at hf ⊢
  rw [@rowForms_eq _ _ _ _ _ _ _ N', List.mem_append] at hf
  rcases hf with hf | hf
  · obtain ⟨f, h1, h2⟩ := alike_carries C _ _ _ (alike_digitPV C N N' hN) (fun s hs => by
      rw [Nat.mul_zero, Nat.zero_add]; exact H.W s hs) f' hf
    exact ⟨f, by rw [@rowForms_eq _ _ _ _ _ _ _ N]; exact List.mem_append_left _ h1, h2⟩
  · obtain ⟨f, h1, h2⟩ := alike_lines C _ _ _ _ _ (alike_digitPV C N N' hN) (fun n hn => by
      rw [Nat.mul_zero, Nat.zero_add]; exact H.P n hn) (C.const _) f' hf
    exact ⟨f, by rw [@rowForms_eq _ _ _ _ _ _ _ N]; exact List.mem_append_right _ h1, h2⟩

/-- The three of the stream times the reciprocal. -/
theorem alike_normed (hd : S2 ∣ d) (H : HeardAlike Q) :
    ListRelN Q N N' FinalNorm.normedForms := by
  intro f' hf
  beta_reduce at hf ⊢
  simp only [FinalNorm.normedForms, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨_, by simp [FinalNorm.normedForms], H.nmLeft _⟩
  · exact ⟨_, List.mem_of_getElem? (i := 1) rfl, C.sub (H.nmEnd 0 (by omega))
      (rowAlike C _ _ fun j hj => C.addN (hN .rowAtNormed j hj) _).R⟩
  · refine ⟨_, List.mem_of_getElem? (i := 2) rfl, C.sub (H.nmEnd 1 (by omega))
      (C.sumTo _ _ _ fun i hi => C.sumTo _ _ _ fun l hl => C.smulE _ ?_)⟩
    exact hN .streamAtNormed _ (limb_lt hd hl hi)

/-- **ALL 29 FORMS.** -/
theorem alikeN_forms (hd : S2 ∣ d) (H : HeardAlike Q) : ListRelN Q N N' FinalNorm.forms := by
  intro f' hf
  beta_reduce at hf ⊢
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨f, h1, h2⟩ := alike_squares C N N' hN hd H f' hf
        exact ⟨f, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1)), h2⟩
      · obtain ⟨f, h1, h2⟩ := alike_products C N N' hN H f' hf
        exact ⟨f, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h1)),
          h2⟩
    · obtain ⟨f, h1, h2⟩ := alike_rows C N N' hN H f' hf
      exact ⟨f, List.mem_append_left _ (List.mem_append_right _ h1), h2⟩
  · obtain ⟨f, h1, h2⟩ := alike_normed C N N' hN hd H f' hf
    exact ⟨f, List.mem_append_right _ h1, h2⟩

include hw

/-- Two limbs of the wide matrix from limb m on, m ≤ 2. -/
theorem alike_wideAt (hd : S2 ∣ d) (k : FinalNorm.Key) (m : Nat) (hm : m ≤ 2) :
    RelN Q N N' (FinalNorm.wideAt k (m * d)) := by
  unfold RelN FinalNorm.wideAt
  refine C.sumTo _ _ _ fun i hi => C.sumTo _ _ _ fun l hl => C.smulE _ (hw _ ?_)
  rw [← Nat.add_mul]
  exact limb_lt hd (show m + l < 4 by omega) hi

/-- **THE FOUR KEYS**, with the head's 21 digits behind the norm's 99. -/
theorem alikeN_key (hd : S2 ∣ d) (H : HeardAlike Q) (k : FinalNorm.Key) :
    RelN Q N N' (FinalNorm.key 21 k) := by
  have w0 : ∀ k, RelN Q N N' (FinalNorm.wideAt k 0) := fun k => by
    have := alike_wideAt C N N' hN hw hd k 0 (by omega)
    rwa [Nat.zero_mul] at this
  have w2 : ∀ k, RelN Q N N' (FinalNorm.wideAt k (2 * d)) := fun k =>
    alike_wideAt C N N' hN hw hd k 2 (by omega)
  cases k with
  | remLow =>
    exact C.sub (C.sub (C.addE H.nmClaimed _) (C.smulN _ (w0 _))) (C.smulN _ (w2 _))
  | remHigh => exact C.smulN _ (C.Eadd _ (w2 _))
  | clamp =>
    refine C.addE (C.add (w0 _) (C.smulN _ (C.sumTo _ _ _ fun j hj => C.smulE _ ?_))) _
    exact C.add (hN .actAtKeys _ (show j < 2 * d by omega))
      (C.smulN _ (hN .actAtKeys _ (show d + j < 2 * d by omega)))
  | digits =>
    exact C.sumTo _ _ _ fun j hj => C.smulE _ (C.addN (hN .rowAtKeys _ hj) _)

end Norm

end VerifiableInference.Desc.Kinds.Head.Law
