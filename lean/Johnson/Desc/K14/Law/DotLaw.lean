-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/DotLaw.lean: the joined law of the constraint (Dot) of the linear claim's
second part, with its premises by name, and the law tried on two functions that are no verifier's.

The law's first half (DotSoundOf). The shape, the row weights g, the matrix M and the words of W are
fixed. If W is not g applied to M's rows at some column, then at no more than kCol |K| ^ (kCol - 1)
points psi can (Dot), made at a point that reads as psi, lie among constraints that hold of words.

THE NAMED PREMISES. None of them is tested where (Dot) is laid.
  WBeforePoint   the words of W are fixed before the shared point is drawn: the words that the
                 constraints hold of agree with the fixed ones on W's message. What holds it in a
                 protocol is that W's message is sent, and bound, in front of the draw. The block
                 that draws the point has a list of messages that must stand in front of it; its
                 test on the plan refuses an empty list (Johnson/Desc/K14/Blocks.lean).
  the weights    g stands outside the count: it is fixed before the point. It is a value in the
                 clear, read off the first chain's last record.
  OmegaOfTable   omega_col, as the words hold it, is M applied to the equality vector at psi. It is
                 what (fold) gives together with the pinning of the folded row: not shown.
  one shape      the shape S is one letter: the chain that draws psi and the chain that lays (Dot)
                 run under the same shape.
  well-formed    each row weight is a well-formed vector (Tensor.ok).
The second half (YesDotOf): where the point has kCol coordinates, each weight has kRow variables and
can be cut at the rows of M, the constraint can be made.
Main names: WBeforePoint, OmegaOfTable, DotSoundOf, YesDotOf, DotLawOf, dotSound, dot_yes, dotLaw,
not_dotLawOf_yes, not_dotLawOf_no.

What is not claimed. That any of the named premises holds of a run. Nothing on how psi is drawn, on
(Eval), or on soundness of a verifier. The small instance is no instance of a release.

-/
import Johnson.Desc.K14.Law.MeansDotOk
import Johnson.Desc.K14.Law.RunSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- A NAMED PREMISE: the words of W's message are fixed before the shared point is drawn. m: the
fixed words; m': the words that the constraints hold of. -/
def WBeforePoint (w : Nat) (m m' : Words K) : Prop := AgreeOn w m m'

/-- A NAMED PREMISE: omega_col, as the words hold it, is M applied to the equality vector at psi. -/
def OmegaOfTable (S : LinShape) (M : Nat → Nat → K) (psi : List K) (omega : Nat)
    (omegaLay : VectorLay) (m' : Words K) : Prop :=
  OmegaIs S.matrixRows S.kCol M psi fun y => m' omega .main (omegaLay.index y)

/-- The type of a function in the place of the maker of (Dot). -/
abbrev DotMaker : Type :=
  LinShape → List Tensor → List E → Nat → VectorLay → Nat → VectorLay → Option Row

open Classical in
/-- The law's first half, of any function in the place of the maker of (Dot). -/
def DotSoundOf [Fintype K] (mk : DotMaker) : Prop :=
  ∀ (S : LinShape) (weights : List Tensor) (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay)
    (m : Words K) (M : Nat → Nat → K), (∀ g ∈ weights, g.ok = true) →
    (∃ c < 2 ^ S.kCol, m w .main (wLay.index c) ≠
      ∑ y ∈ Finset.range S.matrixRows, (weights.map fun g => ρ.val (g.entry y)).sum * M y c) →
    (Finset.univ.filter fun psi : Fin S.kCol → K =>
      ∃ (psiE : List E) (omega : Nat) (row : Row) (rows : List Row) (T : Statement)
        (m' : Words K),
        psiE.map ρ.val = List.ofFn psi ∧ mk S weights psiE omega omegaLay w wLay = some row ∧
        row ∈ rows ∧ Means.AllSay ρ T rows m' ∧ PlacedDot T S omega omegaLay w wLay ∧
        WBeforePoint w m m' ∧ OmegaOfTable S M (List.ofFn psi) omega omegaLay m').card ≤
      S.kCol * Fintype.card K ^ (S.kCol - 1)

/-- The law's second half: the constraint can be made wherever its parts fit. -/
def YesDotOf (mk : DotMaker) : Prop :=
  ∀ (S : LinShape) (weights : List Tensor) (psi : List E) (omega : Nat) (omegaLay : VectorLay)
    (w : Nat) (wLay : VectorLay), psi.length = S.kCol → (∀ g ∈ weights, g.vars = S.kRow) →
    (∀ g ∈ weights, (tensorBelow g 0 S.kRow S.matrixRows).isSome = true) →
    (mk S weights psi omega omegaLay w wLay).isSome = true

/-- The joined law of (Dot), of any function in the place of its maker. -/
def DotLawOf [Fintype K] (mk : DotMaker) : Prop := DotSoundOf ρ mk ∧ YesDotOf mk

/-- **The law's first half**: MEANS and the count joined, under the named premises. -/
theorem dotSound [Fintype K] : DotSoundOf ρ linDotRow := by
  classical
  intro S weights omegaLay w wLay m M hok hgap
  refine le_trans (Finset.card_le_card ?_)
    (dotCatches S.matrixRows S.kCol M (fun y => (weights.map fun g => ρ.val (g.entry y)).sum)
      (fun c => m w .main (wLay.index c)) hgap)
  intro psi hpsi
  rw [Finset.mem_filter] at hpsi
  obtain ⟨_, psiE, omega, row, rows, T, m', hp, hrow, hmem, hs, hP, hW, hO⟩ := hpsi
  have hD := (dotMeansOk ρ T S weights psiE omega omegaLay w wLay row hrow hok hP m').1
    (hs row hmem)
  rw [hp] at hD
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, _, hO, ?_⟩
  unfold DotEq at hD ⊢
  rw [hD]
  exact Finset.sum_congr rfl fun c _ => congrArg (eqK (List.ofFn psi) c * ·) (hW (wLay.index c))

/-- A list can be made item by item where each item can. -/
theorem mapM_isSome {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ a ∈ l, (f a).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1
      (mapM_isSome f l fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [List.mapM_cons, hb, hbs]

/-- (Dot) can be made wherever its parts fit. -/
theorem dot_yes : YesDotOf linDotRow := by
  intro S weights psi omega omegaLay w wLay hp hv hc
  obtain ⟨cut, hcut⟩ := Option.isSome_iff_exists.1 (mapM_isSome _ weights hc)
  have hg : (psi.length == S.kCol && weights.all (·.vars == S.kRow)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨hp, hv⟩
  unfold linDotRow
  simp [guard, hg, hcut]

/-- **The joined law of (Dot).** -/
theorem dotLaw [Fintype K] : DotLawOf ρ linDotRow := ⟨dotSound ρ, dot_yes⟩

/-! ## The two tries -/

/-- The constraint without a coefficient and with the target 0 holds of all words. -/
theorem says_empty (T : Statement) (m : Words K) : Means.Says ρ T {} m := by
  unfold Means.Says Means.value Means.onTable
  simp only [coefficient_empty, zero_mul, Finset.sum_const_zero, add_zero]
  exact ρ.zero.symm

/-- The small shape has no column variable. -/
theorem tiny_kCol : tinyS.kCol = 0 := by decide

/-- At the small instance the two messages have their tables. -/
theorem tiny_placedDot : PlacedDot tinyT tinyS 0 {} 1 {} :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A function that hands out the constraint without a coefficient does not meet the first half. -/
theorem not_dotSoundOf_yes [Fintype K] :
    ¬ DotSoundOf ρ fun _ _ _ _ _ _ _ => some {} := by
  classical
  intro h
  have h3 := h tinyS [] {} 1 {} (fun o _ _ => if o = 1 then (1 : K) else 0) (fun _ _ => 0)
    (fun g hg => absurd hg List.not_mem_nil) ⟨0, by simp, by simp⟩
  have hb : tinyS.kCol * Fintype.card K ^ (tinyS.kCol - 1) = 0 := by rw [tiny_kCol]; simp
  rw [hb, Nat.le_zero, Finset.card_eq_zero] at h3
  refine Finset.filter_eq_empty_iff.1 h3 (Finset.mem_univ fun _ => 0)
    ⟨[], 0, {}, [{}], tinyT, fun o _ _ => if o = 1 then (1 : K) else 0, ?_, rfl,
      List.mem_singleton.2 rfl, ?_, tiny_placedDot, fun _ => rfl, ?_⟩
  · exact (List.ofFn_eq_nil_iff.2 tiny_kCol).symm
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact says_empty ρ _ _
  · intro y _
    simp

/-- A function that makes nothing does not meet the second half. -/
theorem not_yesDotOf_no : ¬ YesDotOf fun _ _ _ _ _ _ _ => none := by
  intro h
  have := h tinyS [] [] 0 {} 1 {} tiny_kCol.symm (fun g hg => absurd hg List.not_mem_nil)
    (fun g hg => absurd hg List.not_mem_nil)
  cases this

/-- Neither function meets the joined law. -/
theorem not_dotLawOf_yes [Fintype K] : ¬ DotLawOf ρ fun _ _ _ _ _ _ _ => some {} :=
  fun h => not_dotSoundOf_yes ρ h.1

@[inherit_doc not_dotLawOf_yes]
theorem not_dotLawOf_no [Fintype K] : ¬ DotLawOf ρ fun _ _ _ _ _ _ _ => none :=
  fun h => not_yesDotOf_no h.2

end Desc.K14.Law
