-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLineProofs.lean: proofs for Cb/Ld/LdLine.lean.

The line: two claims "F_a(γ) + β c_a = v_a" at one point γ become one claim, by a random combination
with the coefficients (1 - ρ, ρ).

Main names (statements and hypotheses: Cb/Ld/LdLine.lean):
  `ldLine_cnt`: under `L.Virt` and `L.Form`, for each fixed tuple of entries of which one of the two
    claims fails: at most one bad ρ.
  `ldLine_piece`: the line over a signature.
  `ldLineC_piece`: the line on the two halves of a table, over a signature.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLine
import Cb.Ld.LdZeroProofs
import Cb.Ld.LdBatProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-- The extension of t at the point x read through σ⁻¹ is the extension, at x, of the table t read
through σ⁻¹. -/
theorem mle_perm {K : Type} [CommRing K] {k : ℕ} (σ : Equiv.Perm (Fin k)) (t : (Fin k → Bool) → K)
    (x : Fin k → K) :
    Alg.mle t (fun i => x (σ.symm i)) =
      Alg.mle (fun b : Fin k → Bool => t fun v => b (σ.symm v)) x := by
  have h := Alg.mle_equiv σ t (fun i => x (σ.symm i))
  simp only [Equiv.symm_apply_apply] at h
  exact h.symm

section Cube
variable {E : Type} [Field E]

/-- a corner of the cube of k + 1 variables: its last coordinate and the others -/
def lnSnocB (k : ℕ) : Bool × (Fin k → Bool) ≃ (Fin (k + 1) → Bool) where
  toFun p := Fin.snoc p.2 p.1
  invFun b := (b (Fin.last k), fun i => b i.castSucc)
  left_inv p := Prod.ext (Fin.snoc_last (α := fun _ => Bool) p.1 p.2)
    (funext fun i => Fin.snoc_castSucc (α := fun _ => Bool) p.1 p.2 i)
  right_inv b := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact Fin.snoc_last (α := fun _ => Bool) _ _
    · exact Fin.snoc_castSucc (α := fun _ => Bool) _ _ i

theorem ln_sum_cube {N : Type} [AddCommMonoid N] {k : ℕ} (f : (Fin (k + 1) → Bool) → N) :
    ∑ b, f b = ∑ x : Fin k → Bool, (f (Fin.snoc x false) + f (Fin.snoc x true)) := by
  rw [← (lnSnocB k).sum_comp f, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib, add_comm]
  rfl

theorem ln_eqk_snoc {k : ℕ} (γ : Fin k → E) (ρ : E) (x : Fin k → Bool) (β : Bool) :
    Alg.eqk (Fin.snoc γ ρ : Fin (k + 1) → E) (Fin.snoc x β) =
      Alg.eqk γ x * if β then ρ else 1 - ρ := by
  simp [Alg.eqk, Fin.prod_univ_castSucc]

end Cube

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLine_all : Spec.ldLine_all E := fun _ _ _ => Iff.rfl

theorem ldLine_link : Spec.ldLine_link E := by
  intro L hV hF o (ρ : E) m
  show hSumAll (L.N.vars (L.nx o ρ)) (L.N.sum (L.nx o ρ) m) + ∑ j, L.N.slS (L.nx o ρ) j * m j =
    ∑ b : Bool, (if b then ρ else 1 - ρ) * (L.fv o m b + L.cv m b * L.be o)
  rw [hV, hF, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem ldLine_tg : Spec.ldLine_tg E := by
  intro L o ρ
  show ∑ b : Bool, (if b then ρ else 1 - ρ) * o.vals (L.a b) = _
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem ldLine_ok : Spec.ldLine_ok E := fun _ => ldBat_ok_line E

theorem ldLine_err : Spec.ldLine_err E := fun _ => rfl

theorem ldLine_cnt : Spec.ldLine_cnt E := fun L hV hF o m hn =>
  pscIn_cnt E L.toIn (ldLine_link E L hV hF) (ldLine_ok E L) o m hn

theorem ldLine_piece : Spec.ldLine_piece E := fun L S E₀ Wp Kc R0 msg q hV hF hB =>
  pscIn_piece E L.toIn S E₀ Wp Kc R0 msg q (ldLine_link E L hV hF) hB (ldLine_ok E L)

omit [Fintype E] in
theorem ldLine_mle_snoc : Spec.ldLine_mle_snoc E := by
  intro k u γ ρ
  unfold Alg.mle
  rw [ln_sum_cube, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ln_eqk_snoc, ln_eqk_snoc]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem ldLineC_virt : Spec.ldLineC_virt E := by
  intro C hH o ρ m
  show hSumAll
      (pVars (List.replicate (C.k + 1) (pfCube E C.n)) (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ))))
      (C.next.sum (o, ρ) m) =
    (1 - ρ) * C.P.F o.st (fun j => m (C.jm j)) (C.a false) (C.P.ini o.st (C.P.par.hp o.st o.pt)) +
      ρ * C.P.F o.st (fun j => m (C.jm j)) (C.a true) (C.P.ini o.st (C.P.par.hp o.st o.pt))
  rw [psv_eqs_sum E, hH, hH, ← ldLine_mle_snoc E C.k (fun b => C.G o m (Alg.corner b)) (C.gam o) ρ,
    ← Alg.mle_equiv C.sg (fun b => C.G o m (Alg.corner b)) (Fin.snoc (C.gam o) ρ)]
  unfold Alg.mle
  refine Finset.sum_congr rfl fun b _ => ?_
  have hx : C.fn (o, ρ)
        (pH _ (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ)))
          (ppOf (pfCube E C.n) (C.k + 1) (Alg.corner b))) =
      Alg.corner fun v => b (C.sg.symm v) := by
    funext i
    show hFnOf (pfCube E C.n) (C.k + 1) (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ)))
        (pH _ (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ)))
          (ppOf (pfCube E C.n) (C.k + 1) (Alg.corner b))) (C.sg.symm i) = _
    rw [psv_fn_pt E (pfCube E C.n) (C.k + 1) (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ))) (Alg.corner b)]
    rfl
  have hs : C.next.sum (o, ρ) m
        (pH _ (pdEqs E C.n (C.k + 1) (C.ptS (o, ρ)))
          (ppOf (pfCube E C.n) (C.k + 1) (Alg.corner b))) =
      C.G o m (Alg.corner fun v => b (C.sg.symm v)) := by
    show C.S0 o (C.fn (o, ρ) _) (fun a => C.F o m a (C.fn (o, ρ) _)) +
        ∑ b', C.S1 o (C.fn (o, ρ) _) (fun a => C.F o m a (C.fn (o, ρ) _)) b' *
          C.Fb o m b' (C.fn (o, ρ) _) = _
    rw [hx]
    rfl
  exact congrArg (fun s => Alg.eqk (C.ptS (o, ρ)) b * s) hs

theorem ldLineC_form : Spec.ldLineC_form E := by
  intro C o ρ m
  classical
  show ∑ j, C.P.lst o.st (C.P.par.hp o.st o.pt) *
      ((if j = C.jm (C.P.cAt (C.a false)) then 1 - ρ else 0) +
        if j = C.jm (C.P.cAt (C.a true)) then ρ else 0) * m j =
    C.P.lst o.st (C.P.par.hp o.st o.pt) *
      ((1 - ρ) * m (C.jm (C.P.cAt (C.a false))) + ρ * m (C.jm (C.P.cAt (C.a true))))
  have e : ∀ j, C.P.lst o.st (C.P.par.hp o.st o.pt) *
        ((if j = C.jm (C.P.cAt (C.a false)) then 1 - ρ else 0) +
          if j = C.jm (C.P.cAt (C.a true)) then ρ else 0) * m j =
      C.P.lst o.st (C.P.par.hp o.st o.pt) *
        ((if j = C.jm (C.P.cAt (C.a false)) then (1 - ρ) * m j else 0) +
          if j = C.jm (C.P.cAt (C.a true)) then ρ * m j else 0) := by
    intro j
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem ldLineC_back : Spec.ldLineC_back E := fun _ _ _ => rfl

theorem ldLineC_vars : Spec.ldLineC_vars E := fun C =>
  ⟨fun s => psv_eqs_ok E C.n (C.k + 1) (C.ptS s),
    fun f hf => by rw [List.eq_of_mem_replicate hf]; exact (psv_val E).1 C.n⟩

theorem ldLineC_piece : Spec.ldLineC_piece E := fun C S E₀ Wp Kc R0 msg q hH =>
  ldLine_piece E C.toLine S E₀ Wp Kc R0 msg q (ldLineC_virt E C hH)
    (ldLineC_form E C) (ldLineC_back E C)

end
end Cb
