-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/SumFits.lean: the port's weights fit the variables of the layers' sumchecks,
under the two picks of the coefficient that is left out.

OnBytes/Tie/Pv/Lay/SumTie.lean has as a premise that the port's list of weights fits the variables'
data under the pick (`Fits`, OnBytes/Tie/Pv/Psc/PscTie.lean): the port's completion of a round's
message, read, is the library's. Here that is proved for the two forms that occur in the layers'
sub-proof.

Main names:
  `fits_eq0`, `sum_fits_eq`: all k variables in the equality form, at the readings of the port's
    coordinates z: the port's weights Weight.equality (z i) (n i + 1), then Weight.atZero (DY + 1),
    fit under the pick `F₀` (Cb/G6/Pick.lean): the constant coefficient is left out everywhere.
  `fits_pick`, `sum_fits_plain`: all k variables in the plain form, each of degree at least 1: the
    port's weights Weight.plain (n i + 1), then Weight.atZero (DY + 1), fit under `pick`
    (Cb/Pv/Lay/Merge.lean): the linear coefficient is left out at the k variables, the constant one
    at the further variable.

Limits: sumchecks with variables of both forms are not treated.
-/
import OnBytes.Tie.Pv.Lay.SumTie
import Cb.Pv.Lay.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att
open OnBytes.Psc (Weight)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem fit_eq1 (n : ℕ) (z : E) (o : Option K) (ho : o = some (ρ.val z)) :
    Fit1 ρ (Weight.equality z (n + 1)) ((pfCube K n).var (ldPartDat1 K n o))
      ((0 : Fin (n + 1)), (1 : K)) := by
  subst ho
  exact fit_eq ρ z n

theorem fits_eq0 (DY : ℕ) : ∀ (k : ℕ) (n : Fin k → ℕ) (z : Fin k → E) (w : Fin k → Option K),
    (∀ i, w i = some (ρ.val (z i))) →
    Fits ρ ((List.ofFn fun i => Weight.equality (z i) (n i + 1)) ++ [Weight.atZero (DY + 1)])
      (ldPartFmt K k n ++ [pDummy K DY])
      (PDats.snoc (ldPartFmt K k n) (ldPartDat K k n w) (pDummy K DY) (pDummyD K DY))
      (fix0 (pVars (ldPartFmt K k n ++ [pDummy K DY])
        (PDats.snoc (ldPartFmt K k n) (ldPartDat K k n w) (pDummy K DY) (pDummyD K DY))))
  | 0, _, _, _, _ => by
    rw [List.ofFn_zero]
    exact ⟨fit_y ρ DY, trivial⟩
  | k + 1, n, z, w, h => by
    rw [List.ofFn_succ]
    exact ⟨fit_eq1 ρ (n 0) (z 0) (w 0) (h 0),
      fits_eq0 DY k (fun i => n i.succ) (fun i => z i.succ) (fun i => w i.succ) fun i => h i.succ⟩

theorem sum_fits_eq (L : SumL K) (st : L.St) (z : Fin L.S.k → E)
    (hw : ∀ i, L.S.w st i = some (ρ.val (z i))) :
    Fits ρ ((List.ofFn fun i => Weight.equality (z i) (L.M.n i + 1)) ++
        [Weight.atZero (L.M.DY + 1)]) L.T.par.fmt (L.T.par.dat st) (F₀ L.T.par st) :=
  fits_eq0 ρ L.M.DY L.S.k L.M.n z (L.S.w st) hw

/-! ## The plain form -/

theorem mon0_plain (n : ℕ) : ((pfCube K n).var (pdPlain K n)).mon 0 = 2 := by
  show ∑ b : Bool, (1 : K) * (if b then (1 : K) else 0) ^ (((0 : Fin (n + 1)) : ℕ)) = 2
  rw [Fintype.sum_bool]
  norm_num

theorem pick_plain (n : ℕ) (h : 1 ≤ n) (o : Option K) (ho : o = none) (l : List (HVar K)) :
    (pick (((pfCube K n).var (ldPartDat1 K n o)) :: l)).1 = ((1 : Fin (n + 1)), (1 : K)) := by
  classical
  subst ho
  have h2 : ((pfCube K n).var (pdPlain K n)).mon 0 ≠ 1 := by
    rw [mon0_plain]
    intro h3
    have h4 : (1 : K) = 0 := by linear_combination h3
    exact one_ne_zero h4
  have hn : 1 ≤ ((pfCube K n).var (pdPlain K n)).n := h
  show ((if ((pfCube K n).var (pdPlain K n)).mon 0 = 1 then 0
    else if h : 1 ≤ ((pfCube K n).var (pdPlain K n)).n then ⟨1, Nat.lt_succ_of_le h⟩ else 0,
      (1 : K)) : Fin (n + 1) × K) = _
  rw [if_neg h2, dif_pos hn]
  refine Prod.ext (Fin.ext ?_) rfl
  show 1 = 1 % (n + 1)
  rw [Nat.mod_eq_of_lt (by omega)]

theorem pick_dummy (DY : ℕ) :
    (pick [(pDummy K DY).var (pDummyD K DY)]).1 = ((0 : Fin (DY + 1)), (1 : K)) := by
  classical
  show ((if ((pDummy K DY).var (pDummyD K DY)).mon 0 = 1 then 0
    else if h : 1 ≤ ((pDummy K DY).var (pDummyD K DY)).n then ⟨1, Nat.lt_succ_of_le h⟩ else 0,
      (1 : K)) : Fin (DY + 1) × K) = _
  rw [if_pos (mon0_dummy DY)]

theorem fit_plain1 (n : ℕ) (h : 1 ≤ n) (o : Option K) (ho : o = none) :
    Fit1 ρ (Weight.plain (n + 1)) ((pfCube K n).var (ldPartDat1 K n o))
      ((1 : Fin (n + 1)), (1 : K)) := by
  subst ho
  exact fit_plain_at ρ n h

theorem fits_pick (DY : ℕ) : ∀ (k : ℕ) (n : Fin k → ℕ) (w : Fin k → Option K),
    (∀ i, w i = none) → (∀ i, 1 ≤ n i) →
    Fits ρ (plainWs (List.ofFn n) DY) (ldPartFmt K k n ++ [pDummy K DY])
      (PDats.snoc (ldPartFmt K k n) (ldPartDat K k n w) (pDummy K DY) (pDummyD K DY))
      (pick (pVars (ldPartFmt K k n ++ [pDummy K DY])
        (PDats.snoc (ldPartFmt K k n) (ldPartDat K k n w) (pDummy K DY) (pDummyD K DY))))
  | 0, _, _, _, _ => by
    unfold plainWs
    rw [List.ofFn_zero]
    refine ⟨?_, trivial⟩
    have e := pick_dummy (K := K) DY
    exact e ▸ fit_y ρ DY
  | k + 1, n, w, hw, h => by
    have ih := fits_pick DY k (fun i => n i.succ) (fun i => w i.succ) (fun i => hw i.succ)
      fun i => h i.succ
    unfold plainWs at ih ⊢
    rw [List.ofFn_succ, List.map_cons]
    refine ⟨?_, ih⟩
    have e := pick_plain (K := K) (n 0) (h 0) (w 0) (hw 0)
      (pVars (ldPartFmt K k (fun i => n i.succ) ++ [pDummy K DY])
        (PDats.snoc (ldPartFmt K k fun i => n i.succ) (ldPartDat K k (fun i => n i.succ)
          fun i => w i.succ) (pDummy K DY) (pDummyD K DY)))
    exact e ▸ fit_plain1 ρ (n 0) (h 0) (w 0) (hw 0)

theorem sum_fits_plain (L : SumL K) (st : L.St) (hw : ∀ i, L.S.w st i = none)
    (h1 : ∀ i, 1 ≤ L.M.n i) :
    Fits ρ (plainWs (List.ofFn L.M.n) L.M.DY) L.T.par.fmt (L.T.par.dat st)
      (pick (L.T.par.vars st)) :=
  fits_pick ρ L.M.DY L.S.k L.M.n (L.S.w st) hw h1

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_fits_eq
#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_fits_plain
