-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/CloseCf.lean: the three rows of the closing and of the test of the bits, coefficient
by coefficient.

It imports PscCf.lean and ClosePoint.lean; no file of the port.

Below, k := mu + d; γ: the places of the sumcheck's point (`gamE`, `gamB`); π: the end point by
variable, π t = γ (k − 1 − t) (`ptE`, `ptB`); ε: the sumcheck's first challenge.
Main names:
  `A.cellW π j`   the sum of eq(π, c) over the corners c whose cell is j. No corner of a dead plane
                  has a cell (Idle.lean).
  `rowE_cf`       rowE.cf j = Σ_{names i, wE i = j} nH γ i + ε · x.top.mf j + ε · (facE · cellW ptE
                  j).
                  Its target (`rowE_tg`, ClosePoint.lean): the last value less ε.
  `rowU_cf`       rowU.cf j = Σ_{names i, wB i = j} nH γ i. `rowU_tg`: the last value less
                  ε · v (v − 1), v the shown value.
  `rowV_cf`       rowV.cf j = cellW ptB j + (if j = cB then β else 0). `rowV_tg`: v.
The sums over names are `Cf.nSum` and `Cf.nH` (PscCf.lean). No condition is asked.
Limits: not shown that these are the port's numbers, nor that places are apart (that depends on the
values of the places).

-/
import Cb.Pv.KeyLookup.PscCf
import Cb.Pv.KeyLookup.ClosePoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Finset

noncomputable section

namespace Clo
variable {E : Type} [Field E] [Fintype E]

theorem psiOne_mix : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    Cf.PsiOne (pfMix E k dg) (pdMix E k dg z)
  | 0, _, _ => trivial
  | k + 1, dg, z => ⟨fun x => hev_pvConst E (dg 0) 1 x, psiOne_mix k _ _⟩

end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-- The weight of the entry j in the extension of the bits at π. -/
def cellW (π : Fin (A.mu + A.d) → E) (j : A.J) : E :=
  Alg.mle (fun c => if A.cell c = some j then (1 : E) else 0) π

theorem cellW_eq (π : Fin (A.mu + A.d) → E) (j : A.J) :
    A.cellW π j = ∑ c, if A.cell c = some j then Alg.eqk π c else 0 := by
  unfold cellW Alg.mle
  refine Finset.sum_congr rfl fun c _ => ?_
  show Alg.eqk π c * (if A.cell c = some j then 1 else 0) = _
  by_cases e : A.cell c = some j
  · rw [if_pos e, if_pos e, mul_one]
  · rw [if_neg e, if_neg e, mul_zero]

theorem rowE_cf (zz : (A.En P).par.Mid) (j : A.J) :
    (A.rowE P zz).cf j =
      Cf.nSum (A.En P).par.fmt (fun i => if P.wE i = j then Cf.nH (A.En P).par.fmt zz.pt i else 0) +
        zz.eps * (show A.XS from zz.st).top.mf j +
        zz.eps * (A.facE P zz * A.cellW (A.ptE P zz) j) := by
  haveI : DecidableEq (A.En P).par.J := inferInstanceAs (DecidableEq (Option A.J))
  have h := Cf.slU_cf (A.En P).par (A.En P).rowB ((A.En P).outOf zz) (some j)
    (Clo.psiOne_mix _ _ _)
  refine h.trans ?_
  have h1 : (fun i => if (A.En P).par.wAt i = some j then
        Cf.nH (A.En P).par.fmt ((A.En P).outOf zz).pt i else 0) =
      fun i => if P.wE i = j then Cf.nH (A.En P).par.fmt zz.pt i else 0 := by
    funext i
    by_cases e : P.wE i = j
    · rw [if_pos e]
      exact if_pos (congrArg some e)
    · rw [if_neg e]
      exact if_neg fun e' => e (Option.some.inj e')
  have h2 : (A.En P).rowB zz.st () ((A.En P).par.hp zz.st zz.pt) (some j) =
      A.cellW (A.ptE P zz) j := by
    have hm := Alg.mle_equiv (ordC (A.mu + A.d))
      (fun c => if A.cell c = some j then (1 : E) else 0) (A.ptE P zz)
    have hz : (fun v => A.ptE P zz (ordC (A.mu + A.d) v)) = A.gamE P zz := by
      funext v
      show A.gamE P zz (Fin.rev (Fin.rev v)) = _
      rw [Fin.rev_rev]
    rw [hz] at hm
    unfold cellW
    rw [← hm]
    unfold LkEndM.rowB Alg.mle
    rw [A.en_point P zz]
    refine Finset.sum_congr rfl fun b _ => ?_
    show (if (A.En P).tAt b = some j then Alg.eqk (A.gamE P zz) b else 0) =
      Alg.eqk (A.gamE P zz) b *
        (if (A.cell fun v => b ((ordC (A.mu + A.d)).symm v)) = some j then 1 else 0)
    by_cases e : (A.cell fun v => b ((ordC (A.mu + A.d)).symm v)) = some j
    · rw [if_pos e, mul_one]
      exact if_pos e
    · rw [if_neg e, mul_zero]
      exact if_neg e
  have h3 : ∑ b : Unit, (A.En P).par.S1 zz.st ((A.En P).par.hp zz.st zz.pt)
        ((A.En P).outOf zz).vals b * (A.En P).rowB zz.st b ((A.En P).par.hp zz.st zz.pt) (some j) =
      A.facE P zz * A.cellW (A.ptE P zz) j := by
    rw [Fintype.sum_unique]
    exact congrArg₂ (· * ·) (A.en_fac P zz _) h2
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg (Cf.nSum (A.En P).par.fmt) h1) rfl) (congrArg (zz.eps * ·) h3)

theorem rowU_cf (o : (A.BT P).par.Out) (j : A.J) :
    (A.rowU P o).cf j =
      Cf.nSum (A.BT P).par.fmt fun i =>
        if P.wB i = j then Cf.nH (A.BT P).par.fmt o.pt i else 0 := by
  haveI : DecidableEq (A.BT P).par.J := inferInstanceAs (DecidableEq (Option A.J))
  have h := Cf.slU_cf (A.BT P).par (fun _ b => b.elim) o (some j)
    (Cf.psiOne_our (A.BT P) o.st (Cf.psiOne_eqs 2 _ _))
  refine h.trans ?_
  have h1 : (fun i => if (A.BT P).par.wAt i = some j then Cf.nH (A.BT P).par.fmt o.pt i else 0) =
      fun i => if P.wB i = j then Cf.nH (A.BT P).par.fmt o.pt i else 0 := by
    funext i
    by_cases e : P.wB i = j
    · rw [if_pos e]
      exact if_pos (congrArg some e)
    · rw [if_neg e]
      exact if_neg fun e' => e (Option.some.inj e')
  have h2 : o.eps * (A.BT P).par.slS o.st (some j) = 0 := mul_zero _
  have h3 : o.eps * ∑ b : (A.BT P).par.B,
      (A.BT P).par.S1 o.st ((A.BT P).par.hp o.st o.pt) o.vals b * (b.elim : E) = 0 := by
    rw [Finset.sum_eq_zero fun b _ => b.elim, mul_zero]
  exact (congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (congrArg (Cf.nSum (A.BT P).par.fmt) h1) h2) h3).trans
      ((add_zero _).trans (add_zero _))

theorem rowU_tg (o : (A.BT P).par.Out) :
    (A.rowU P o).tg = o.fin - o.eps * (o.vals () * (o.vals () - 1)) := by
  show o.fin - o.eps * (∑ _t : Unit, (1 : E) * (o.vals () * (o.vals () - 1))) = _
  simp

theorem rowV_cf (o : (A.BT P).par.Out) (j : A.J) :
    (A.rowV P o).cf j = A.cellW (A.ptB P o) j + if j = P.cB then A.betaB P o else 0 := by
  show (A.Bt P).rowA o.st () ((A.BT P).par.hp o.st o.pt) (some j) = _
  unfold LkBit.rowA
  rw [A.bt_point P o, A.cellW_eq]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_) ?_
  · by_cases e : A.cell c = some j
    · rw [if_pos e]
      exact if_pos e
    · rw [if_neg e]
      exact if_neg e
  · by_cases e : j = P.cB
    · rw [if_pos e]
      exact if_pos (congrArg some e)
    · rw [if_neg e]
      exact if_neg fun e' => e (Option.some.inj e')

theorem rowV_tg (o : (A.BT P).par.Out) : (A.rowV P o).tg = o.vals () := rfl

end Dat
end
end Lk6

#print axioms Lk6.Dat.rowE_cf
#print axioms Lk6.Dat.rowU_cf
#print axioms Lk6.Dat.rowU_tg
#print axioms Lk6.Dat.rowV_cf
