-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartCellsProofs.lean: the proofs of Cb/Part/LdPartCells.lean: the one reading of cells;
the claims on cell atoms as the read stage's claims.

Two helper lemmas: `ldPartCells_laid`, used in the proofs of `ldPartCells_item` and
`ldPartCells_claims`, and `ldPartCells_get`, used in that of `ldPartCells_claims`. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Limits: what the head of Cb/Part/LdPartCells.lean lists as not said is not said here either.
-/
import Cb.Part.LdPartCells
import Cb.Ld.LdRngAlgProofs

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

section
variable {E : Type} [Field E]

/-- A sum against coefficients a i that are laid at the places f i is the sum over the names i,
whatever procedure d decides the equations f i = x. -/
theorem ldPartCells_laid {ι X : Type} [Fintype X] (s : Finset ι) (f : ι → X)
    (d : ∀ i x, Decidable (f i = x)) (a : ι → E) (g : X → E) :
    ∑ x, (∑ i ∈ s, @ite E (f i = x) (d i x) (a i) 0) * g x = ∑ i ∈ s, a i * g (f i) := by
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single (f i)]
  · rw [if_pos rfl]
  · intro x _ hx
    rw [if_neg (Ne.symm hx), zero_mul]
  · intro h
    exact absurd (mem_univ _) h

theorem ldPartCells_get {α : Type} (l : List α) (f : α → E) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    exact Fin.sum_univ_succ fun i : Fin (l.length + 1) => f ((a :: l).get i)

end

theorem ldPartCells_item : Spec.ldPartCells_item := by
  intro p E _ nm t γ Y
  have h1 : ∀ κ, ∑ ρ, nm.rowW t γ ρ * ((Y ρ κ : ℤ) : E) =
      ∑ r ∈ range (nm.R t.seg), t.row γ r * ((Y (nm.rowAt t.seg r) κ : ℤ) : E) := fun κ =>
    ldPartCells_laid (range (nm.R t.seg)) (nm.rowAt t.seg) _ (t.row γ) fun ρ => ((Y ρ κ : ℤ) : E)
  simp only [h1]
  have h2 := ldPartCells_laid (range (nm.C t.seg)) (nm.colAt t.seg) (fun _ _ => inferInstance)
    (t.col γ) fun κ => ∑ r ∈ range (nm.R t.seg), t.row γ r * ((Y (nm.rowAt t.seg r) κ : ℤ) : E)
  refine Eq.trans h2 ?_
  unfold LdPartItem.val
  rw [sum_comm]
  refine sum_congr rfl fun c hc => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have e : nm.matsE E Y t.seg r c = ((Y (nm.rowAt t.seg r) (nm.colAt t.seg c) : ℤ) : E) := by
    unfold LdPartNm.matsE LdPartNm.mats
    rw [if_pos ⟨mem_range.1 hr, mem_range.1 hc⟩]
  rw [e]
  ring

theorem ldPartCells_claims : Spec.ldPartCells_claims := by
  intro p E St J _ _ nm K W hOf hT st Y e
  have key : ∀ j : K.Jc, (K.toCl nm).k0 st j +
        ∑ k, ∑ c, (K.toCl nm).cw st j k c * readsOf (W st) Y k c +
        ∑ n, (K.toCl nm).ms st j n * e n =
      ext (K.v j) (fun b => (K.f j b).val (nm.matsE E Y)) (K.pt st j) + e (K.cAt j) * K.β st j := by
    intro j
    have h1 : ∑ k, ∑ c, (K.toCl nm).cw st j k c * readsOf (W st) Y k c =
        ((K.rg j).items.map fun t => t.val nm.R nm.C (K.pt st j) (nm.matsE E Y)).sum := by
      rw [sum_comm, ← ldPartCells_get]
      have h2 : ∀ c, ∑ k, (K.toCl nm).cw st j k c * readsOf (W st) Y k c =
          ∑ i : Fin (K.rg j).items.length, nm.colW ((K.rg j).items.get i) (K.pt st j) c *
            readsOf (W st) Y (K.rdAt j i) c := fun c =>
        ldPartCells_laid univ (K.rdAt j) _
          (fun i => nm.colW ((K.rg j).items.get i) (K.pt st j) c) fun k => readsOf (W st) Y k c
      simp only [h2]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [← ldPartCells_item p E nm ((K.rg j).items.get i) (K.pt st j) Y]
      refine sum_congr rfl fun c _ => ?_
      unfold readsOf
      rw [hT st j i]
    have h3 : ∑ n, (K.toCl nm).ms st j n * e n = e (K.cAt j) * K.β st j := by
      have hm : ∀ n,
          (K.toCl nm).ms st j n = @ite E (n = K.cAt j) (Classical.propDecidable _) (K.β st j) 0 :=
        fun _ => rfl
      rw [sum_eq_single (K.cAt j)]
      · rw [hm, if_pos rfl, mul_comm]
      · intro n _ hn
        rw [hm, if_neg hn, zero_mul]
      · intro h
        exact absurd (mem_univ _) h
    rw [h1, h3, hOf j (nm.matsE E Y) (K.pt st j)]
    rfl
  constructor
  · intro h j
    rw [← key j]
    exact h j
  · intro h j
    exact (key j).trans (h j)

theorem ldPartCells_stdW : Spec.ldPartCells_stdW := fun _ _ _ _ _ nm K _ h st j i =>
  congrArg (fun x : Σ j,
    Fin (K.rg j).items.length => nm.rowW ((K.rg x.1).items.get x.2) (K.pt st x.1)) (h j i)

theorem ldPartCells_lay : Spec.ldPartCells_lay := by
  intro p nm Z hOK
  refine ⟨fun s r c hr hc => ?_, fun b hb hZ ρ κ => ?_⟩
  · have hex : ∃ x : ℕ × ℕ × ℕ, x.2.1 < nm.R x.1 ∧ x.2.2 < nm.C x.1 ∧
        nm.rowAt x.1 x.2.1 = nm.rowAt s r ∧ nm.colAt x.1 x.2.2 = nm.colAt s c :=
      ⟨(s, r, c), hr, hc, rfl, rfl⟩
    unfold LdPartNm.mats LdPartNm.lay
    rw [if_pos ⟨hr, hc⟩, dif_pos hex]
    have hs := hex.choose_spec
    generalize hex.choose = x at hs
    obtain ⟨x1, x2, x3⟩ := x
    obtain ⟨g1, g2, g3, g4⟩ := hs
    obtain ⟨e1, e2⟩ := hOK.row x1 x2 s r g1 hr g3
    subst e1
    subst e2
    rw [hOK.col x1 x3 c g2 hc g4]
  · unfold LdPartNm.lay
    split
    · exact hZ _ _ _
    · rw [abs_zero]
      exact hb

theorem ldPartCells_honest : Spec.ldPartCells_honest := by
  intro p E J _ pp _ nm pkJ m Z b' hOK hU hb hP s r c hr hc
  have h :=
    rngPk_cells E pp p.Rp p.C p.P (2 * p.D) b' p.rdx (nm.lay Z) (fun i κ => m (pkJ i κ)) hU hb hP
  unfold LdPartNm.A LdPartNm.matsE
  rw [h, (ldPartCells_lay p nm Z hOK).1 s r c hr hc]

end Cb
