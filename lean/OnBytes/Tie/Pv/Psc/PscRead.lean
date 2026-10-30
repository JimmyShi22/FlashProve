-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscRead.lean: the pure functions of one round of the verifier's masked sumcheck,
read in a field, are the library's.

The functions are those of OnBytes/Iop/Psc.lean: polyAt, Weight with its three makers, and
Weight.complete. They are read by a reading rho (OnBytes/Model/HideLaws.lean). The library's side is
Cb/Ld/LdHide.lean and Cb/Ld/LdHideShort.lean: hev, HVar, hFill.

Main definitions: rd (a list of elements read as a function on Fin n, 0 beyond its end), Fit1 (what
ties a weight to a variable of the library with the power that is left out). Main theorems:
polyAt_hev, complete_sumK, cmp_of, phi_plain, phi_eq, phi_y.

What is not claimed. The statements hold under lengths: polyAt_hev asks length at most n + 1, and
Fit1 asks that as many scalars were sent as the variable's degree. Nothing is said on another weight
than the three makers', or on a run.

-/
import OnBytes.Model.HideLaws
import Cb.Ld.LdHideShort
import Cb.Ld.LdPscVars
import Cb.Ld.LdPsc

set_option autoImplicit false

namespace Johnson.L5.Layers
open OnBytes OnBytes.Model Cb Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-- a list of the port's elements, read; 0 beyond its end -/
def rd (n : ℕ) (l : List E) : Fin n → K := fun t => ρ.val (l.getD t zeroE)

theorem polyAt_sum : ∀ (g : List E) (k : ℕ), g.length ≤ k → ∀ x : E,
    ρ.val (OnBytes.Psc.polyAt g x) = ∑ t : Fin k, ρ.val x ^ (t : ℕ) * rd ρ k g t
  | [], k, _, x => by simp [rd, OnBytes.Psc.polyAt, ρ.zero]
  | c :: g, 0, h, _ => by simp at h
  | c :: g, k + 1, h, x => by
    have hp : OnBytes.Psc.polyAt (c :: g) x = addE (mulE (OnBytes.Psc.polyAt g x) x) c := rfl
    rw [hp, ρ.add, ρ.mul, polyAt_sum g k (by simpa using h) x, Fin.sum_univ_succ]
    simp only [rd, Fin.val_zero, pow_zero, one_mul, List.getD_cons_zero, Fin.val_succ,
      List.getD_cons_succ]
    rw [Finset.sum_mul, add_comm]
    congr 1
    exact sum_congr rfl fun t _ => by ring

/-- (P1) -/
theorem polyAt_hev (g : List E) (n : ℕ) (h : g.length ≤ n + 1) (x : E) :
    ρ.val (OnBytes.Psc.polyAt g x) = hev (rd ρ (n + 1) g) (ρ.val x) := by
  rw [polyAt_sum ρ g (n + 1) h x]
  unfold hev
  simp only [smul_eq_mul]

/-- The port's complete_sum, with the inverse's law read in K. -/
theorem complete_sumK (w : OnBytes.Psc.Weight) (sent : List E) (claim : E)
    (hfix : w.fixed ≤ sent.length)
    (h1 : ρ.val (w.moment.getD w.fixed zeroE) * ρ.val w.fixedInv = 1) :
    dotValue ρ w.moment (w.complete sent claim) = ρ.val claim := by
  have hlen : (sent.take w.fixed).length = w.fixed := by simp [hfix]
  unfold OnBytes.Psc.Weight.complete
  simp only []
  rw [dotValue_at, hlen, ρ.mul, ρ.sub, ρ.dot]
  linear_combination (ρ.val claim -
    dotValue ρ w.moment (List.take w.fixed sent ++ zeroE :: List.drop w.fixed sent)) * h1

/-- What ties a weight of the port to a variable of the library. -/
structure Fit1 (w : OnBytes.Psc.Weight) (v : HVar K) (fx : Fin (v.n + 1) × K) : Prop where
  len : w.d = v.n + 1
  inv : fx.2 * v.mon fx.1 = 1
  clen : ∀ (sent : List E) (claim : E), sent.length = v.n →
    (w.complete sent claim).length = v.n + 1
  cmp : ∀ (sent : List E) (claim : E), sent.length = v.n →
    rd ρ (v.n + 1) (w.complete sent claim) = hFill v fx (ρ.val claim) (rd ρ v.n sent)
  plen : w.psi.length ≤ w.d
  psi : rd ρ (v.n + 1) w.psi = v.psi

/-- (P2), from four facts on a weight. -/
theorem cmp_of (w : OnBytes.Psc.Weight) (v : HVar K) (fx : Fin (v.n + 1) × K)
    (hinv : fx.2 * v.mon fx.1 = 1)
    (h1 : ρ.val (w.moment.getD w.fixed zeroE) * ρ.val w.fixedInv = 1)
    (hfix : w.fixed ≤ v.n)
    (hphi : ∀ q : List E, q.length = v.n + 1 → v.phi (rd ρ (v.n + 1) q) = dotValue ρ w.moment q)
    (hlen : ∀ (sent : List E) (claim : E), sent.length = v.n →
      (w.complete sent claim).length = v.n + 1)
    (hoff : ∀ (sent : List E) (claim : E), sent.length = v.n → ∀ i : Fin v.n,
      rd ρ (v.n + 1) (w.complete sent claim) (fx.1.succAbove i) = rd ρ v.n sent i)
    (sent : List E) (claim : E) (hs : sent.length = v.n) :
    rd ρ (v.n + 1) (w.complete sent claim) = hFill v fx (ρ.val claim) (rd ρ v.n sent) := by
  have e := fill_drop v fx hinv (rd ρ (v.n + 1) (w.complete sent claim))
  rw [hphi _ (hlen sent claim hs), complete_sumK ρ w sent claim (by omega) h1] at e
  rw [← e]
  congr 1
  funext i
  exact hoff sent claim hs i

variable [Fintype K]

theorem phi_plain (n : ℕ) (c : Fin (n + 1) → K) :
    ((pfCube K n).var (pdPlain K n)).phi c = hev c (0 : K) + hev c (1 : K) := by
  show ∑ b : Bool, (1 : K) • hev c (if b then (1 : K) else 0) = _
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, smul_eq_mul]
  ring

theorem phi_eq (n : ℕ) (z : K) (c : Fin (n + 1) → K) :
    ((pfCube K n).var (pdEq K n z)).phi c = (1 - z) * hev c (0 : K) + z * hev c (1 : K) := by
  show ∑ b : Bool, (if b then z else 1 - z) • hev c (if b then (1 : K) else 0) = _
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, smul_eq_mul]
  ring

theorem phi_y (n : ℕ) (c : Fin (n + 1) → K) :
    ((pDummy K n).var (pDummyD K n)).phi c = hev c (0 : K) := by
  show ∑ _u : Unit, (1 : K) • hev c (0 : K) = _
  simp

end Johnson.L5.Layers

#print axioms Johnson.L5.Layers.polyAt_hev
#print axioms Johnson.L5.Layers.cmp_of
#print axioms Johnson.L5.Layers.phi_eq
