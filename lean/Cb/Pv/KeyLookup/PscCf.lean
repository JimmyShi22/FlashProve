-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/PscCf.lean: the first row of a sumcheck, coefficient by coefficient, for every
sumcheck all of whose public polynomials ψ have the value 1 everywhere (equality weights; the
further variable).

It imports the library alone.

The library's `PscPar.slU` (Cb/Ld/LdPsc.lean:350-355) is a sum over the names `HIdx` of the hiding
polynomial's coefficients, which hang on the variables' data. Here the same sum runs over the names
`PIdx fmt`, by recursion on the list of formats, so that at a closed list it unfolds.
Main names:
  `Cf.nSum l f`    the sum of f over all names: for each variable, in the order of the rounds, its
                   degrees 1, 2, …, n; the constant's name last.
  `Cf.nH l γ i`    the weight of the coefficient named i at the point γ: γ_l^(t + 1) at (variable l,
                   degree t + 1), and 1 at the constant.
  `Cf.PsiOne l d`  every ψ has the value 1 everywhere. `psiOne_eqs`, `psiOne_snoc`, `psiOne_dummy`,
                   `psiOne_our`: equality weights have it, and so has the further variable.
  `Cf.slU_cf`      under `PsiOne`: slU rowB o j = nSum (fun i => if wAt i = j then nH o.pt i else 0)
                   + ε · slS j + ε · Σ_b S1_b · rowB_b j.
Limits: nothing on a protocol.

-/
import Cb.Ld.LdPscProofsIor
import Cb.Ld.LdPscVarsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Cf
open Iop Hiop Prob Cb Finset

variable {E : Type} [Field E]

/-- The sum over all names of a hiding polynomial's coefficients. -/
def nSum : (l : List (PFmt E)) → (PIdx l → E) → E
  | [], f => f ()
  | g :: l, f => (∑ t : Fin g.n, f (.inl t)) + nSum l fun i => f (.inr i)

/-- The weight of a coefficient at a point. -/
def nH : (l : List (PFmt E)) → PPt l → PIdx l → E
  | [], _, _ => 1
  | _ :: _, γ, .inl t => γ.1 ^ ((t : ℕ) + 1)
  | _ :: l, γ, .inr i => nH l γ.2 i

/-- Every public polynomial has the value 1 everywhere. -/
def PsiOne : (l : List (PFmt E)) → PDats l → Prop
  | [], _ => True
  | _ :: l, d => (∀ x : E, hev d.1.psi x = 1) ∧ PsiOne l d.2

theorem hPsi_one : ∀ (l : List (PFmt E)) (d : PDats l), PsiOne l d →
    ∀ X : HPt (pVars l d), hPsi (pVars l d) X = 1
  | [], _, _, _ => rfl
  | _ :: l, d, h, X => by
    show hev d.1.psi X.1 * hPsi (pVars l d.2) X.2 = 1
    rw [h.1, hPsi_one l d.2 h.2, mul_one]

theorem hSl_nH : ∀ (l : List (PFmt E)) (d : PDats l), PsiOne l d →
    ∀ (γ : PPt l) (i : HIdx (pVars l d)), hSl (pVars l d) (pH l d γ) i = nH l γ (pIx l d i)
  | [], _, _, _, _ => rfl
  | _ :: l, d, h, γ, .inl t => by
    show hPsi (pVars l d.2) (pH l d.2 γ.2) * γ.1 ^ ((t : ℕ) + 1) = γ.1 ^ ((t : ℕ) + 1)
    rw [hPsi_one l d.2 h.2, one_mul]
  | _ :: l, d, h, γ, .inr i => hSl_nH l d.2 h.2 γ.2 i

theorem sum_names : ∀ (l : List (PFmt E)) (d : PDats l) (f : PIdx l → E),
    ∑ i : HIdx (pVars l d), f (pIx l d i) = nSum l f
  | [], _, f => by
    show ∑ i : Unit, f i = f ()
    simp
  | g :: l, d, f => by
    show ∑ i : Fin g.n ⊕ HIdx (pVars l d.2),
      f (Equiv.sumCongr (Equiv.refl _) (pIx l d.2) i) = _
    rw [Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) rfl (sum_names l d.2 fun i => f (.inr i))

/-- The first row, coefficient by coefficient. -/
theorem slU_cf (Y : PscPar E) [DecidableEq Y.J]
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) (j : Y.J)
    (h : PsiOne Y.fmt (Y.dat o.st)) :
    Y.slU rowB o j =
      nSum Y.fmt (fun i => if Y.wAt i = j then nH Y.fmt o.pt i else 0) + o.eps * Y.slS o.st j +
        o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j := by
  unfold PscPar.slU
  rw [hPsi_one _ _ h, mul_one, ← sum_names Y.fmt (Y.dat o.st)]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hSl_nH _ _ h]
  by_cases e : Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e]

theorem psiOne_snoc : ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f),
    PsiOne l d → (∀ x : E, hev e.psi x = 1) → PsiOne (l ++ [f]) (PDats.snoc l d f e)
  | [], _, _, _, _, he => ⟨he, trivial⟩
  | _ :: l, d, f, e, h, he => ⟨h.1, psiOne_snoc l d.2 f e h.2 he⟩

variable [Fintype E]

theorem psiOne_eqs (n : ℕ) : ∀ (k : ℕ) (z : Fin k → E),
    PsiOne (List.replicate k (pfCube E n)) (pdEqs E n k z)
  | 0, _ => trivial
  | k + 1, z => ⟨fun x => hev_pvConst E n 1 x, psiOne_eqs n k fun i => z i.succ⟩

theorem psiOne_dummy (D : ℕ) (x : E) : hev (pDummyD E D).psi x = 1 := by
  unfold hev pDummyD
  rw [Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

/-- The instance with the further variable Y. -/
theorem psiOne_our (T : PscOur E) (st : T.St) (h : PsiOne T.fmt (T.dat st)) :
    PsiOne T.par.fmt (T.par.dat st) :=
  psiOne_snoc T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY) h (psiOne_dummy T.DY)

end Lk6.Cf

#print axioms Lk6.Cf.slU_cf
#print axioms Lk6.Cf.psiOne_our
