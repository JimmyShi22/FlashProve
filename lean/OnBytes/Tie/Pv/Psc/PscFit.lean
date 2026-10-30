-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscFit.lean: the verifier's three makers of a weight fit the library's three
kinds of variable.

fit_eq: Weight.equality z (n + 1) fits the cube variable under the equality form at the reading of
z, with the constant coefficient left out. fit_y: Weight.atZero (n + 1) fits the dummy variable,
with the constant coefficient left out. fit_plain: Weight.plain (m + 2) fits the cube variable under
the plain form, with the linear coefficient left out.

What is not claimed. Nothing on another weight; nothing on a run.

-/
import OnBytes.Tie.Pv.Psc.PscRead

set_option autoImplicit false

namespace Johnson.L5.Layers
open OnBytes OnBytes.Model Cb Finset

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

omit [Fintype K] in
theorem rd_one (n : ℕ) : rd ρ (n + 1) [oneE] = pvConst K n 1 := by
  funext t
  refine Fin.cases ?_ (fun j => ?_) t
  · simp [rd, pvConst, ρ.one]
  · simp [rd, pvConst, ρ.zero]

theorem fit_eq (z : E) (n : ℕ) :
    Fit1 ρ (OnBytes.Psc.Weight.equality z (n + 1)) ((pfCube K n).var (pdEq K n (ρ.val z)))
      ((0 : Fin (n + 1)), (1 : K)) where
  len := rfl
  inv := by
    show (1 : K) * ∑ b : Bool, (if b then ρ.val z else 1 - ρ.val z) *
      (if b then (1 : K) else 0) ^ (((0 : Fin (n + 1)) : ℕ)) = 1
    simp
  clen := fun sent claim hs => by
    have hs' : sent.length = n := hs
    simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.equality, hs']
  cmp := cmp_of ρ _ _ _
    (by
      show (1 : K) * ∑ b : Bool, (if b then ρ.val z else 1 - ρ.val z) *
        (if b then (1 : K) else 0) ^ (((0 : Fin (n + 1)) : ℕ)) = 1
      simp)
    (by simp [OnBytes.Psc.Weight.equality, ρ.one])
    (Nat.zero_le _)
    (fun q hq => by
      have hq' : q.length = n + 1 := hq
      rw [phi_eq, equality_moment ρ z (n + 1) q (le_of_eq hq'),
        polyAt_hev ρ q n (le_of_eq hq') zeroE, polyAt_hev ρ q n (le_of_eq hq') oneE, ρ.zero, ρ.one])
    (fun sent claim hs => by
      have hs' : sent.length = n := hs
      simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.equality, hs'])
    (fun sent claim _ i => by
      simp [rd, OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.equality])
  plen := by simp [OnBytes.Psc.Weight.equality]
  psi := rd_one ρ n

omit [Fintype K] in
theorem rd_oneY (n : ℕ) :
    rd ρ (n + 1) [oneE] = fun t : Fin (n + 1) => if t = 0 then (1 : K) else 0 := by
  funext t
  refine Fin.cases ?_ (fun j => ?_) t
  · simp [rd, ρ.one]
  · simp [rd, ρ.zero, Fin.succ_ne_zero]

theorem fit_y (n : ℕ) :
    Fit1 ρ (OnBytes.Psc.Weight.atZero (n + 1)) ((pDummy K n).var (pDummyD K n))
      ((0 : Fin (n + 1)), (1 : K)) where
  len := rfl
  inv := by
    show (1 : K) * ∑ _u : Unit, (1 : K) * (0 : K) ^ (((0 : Fin (n + 1)) : ℕ)) = 1
    simp
  clen := fun sent claim hs => by
    have hs' : sent.length = n := hs
    show ((OnBytes.Psc.Weight.atZero (n + 1)).complete sent claim).length = n + 1
    simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.atZero, OnBytes.Psc.Weight.equality, hs']
  cmp := cmp_of ρ _ _ _
    (by
      show (1 : K) * ∑ _u : Unit, (1 : K) * (0 : K) ^ (((0 : Fin (n + 1)) : ℕ)) = 1
      simp)
    (by simp [OnBytes.Psc.Weight.atZero, OnBytes.Psc.Weight.equality, ρ.one])
    (Nat.zero_le _)
    (fun q hq => by
      have hq' : q.length = n + 1 := hq
      show ((pDummy K n).var (pDummyD K n)).phi (rd ρ (n + 1) q) =
        dotValue ρ (OnBytes.Psc.Weight.equality zeroE (n + 1)).moment q
      rw [phi_y, equality_moment ρ zeroE (n + 1) q (le_of_eq hq'),
        polyAt_hev ρ q n (le_of_eq hq') zeroE, ρ.zero]
      ring)
    (fun sent claim hs => by
      have hs' : sent.length = n := hs
      show ((OnBytes.Psc.Weight.atZero (n + 1)).complete sent claim).length = n + 1
      simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.atZero, OnBytes.Psc.Weight.equality,
        hs'])
    (fun sent claim _ i => by
      show rd ρ (n + 1) ((OnBytes.Psc.Weight.atZero (n + 1)).complete sent claim)
        ((0 : Fin (n + 1)).succAbove (show Fin n from i)) = rd ρ n sent (show Fin n from i)
      simp [rd, OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.atZero,
        OnBytes.Psc.Weight.equality])
  plen := by simp [OnBytes.Psc.Weight.atZero, OnBytes.Psc.Weight.equality]
  psi := rd_oneY ρ n

omit [Fintype K] in
theorem rd_X (m : ℕ) : rd ρ (m + 2) [zeroE, oneE] = pvX K (m + 1) := by
  funext t
  refine Fin.cases ?_ (fun j => ?_) t
  · simp [rd, pvX, ρ.zero]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp [rd, pvX, ρ.one]
    · simp [rd, pvX, ρ.zero]

theorem fit_plain (m : ℕ) :
    Fit1 ρ (OnBytes.Psc.Weight.plain (m + 2)) ((pfCube K (m + 1)).var (pdPlain K (m + 1)))
      ((1 : Fin (m + 2)), (1 : K)) where
  len := rfl
  inv := by
    show (1 : K) * ∑ b : Bool, (1 : K) * (if b then (1 : K) else 0) ^ (((1 : Fin (m + 2)) : ℕ)) = 1
    simp
  clen := fun sent claim hs => by
    have hs' : sent.length = m + 1 := hs
    simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.plain, hs']
    omega
  cmp := cmp_of ρ _ _ _
    (by
      show (1 : K) * ∑ b : Bool,
        (1 : K) * (if b then (1 : K) else 0) ^ (((1 : Fin (m + 2)) : ℕ)) = 1
      simp)
    (by simp [OnBytes.Psc.Weight.plain, ρ.one])
    (by show 1 ≤ m + 1; omega)
    (fun q hq => by
      have hq' : q.length = m + 2 := hq
      rw [phi_plain, plain_moment ρ (m + 2) q (le_of_eq hq'),
        polyAt_hev ρ q (m + 1) (le_of_eq hq') zeroE, polyAt_hev ρ q (m + 1) (le_of_eq hq') oneE,
        ρ.zero, ρ.one])
    (fun sent claim hs => by
      have hs' : sent.length = m + 1 := hs
      simp [OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.plain, hs']
      omega)
    (fun sent claim hs i => by
      have hs' : sent.length = m + 1 := hs
      obtain ⟨s0, rest, rfl⟩ : ∃ s0 rest, sent = s0 :: rest := by
        cases sent with
        | nil => simp at hs'
        | cons a l => exact ⟨a, l, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [rd, OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.plain, Fin.succAbove]
      · have e : (1 : Fin (m + 2)).succAbove j.succ = j.succ.succ := by
          simp
        rw [e]
        simp [rd, OnBytes.Psc.Weight.complete, OnBytes.Psc.Weight.plain])
  plen := by simp [OnBytes.Psc.Weight.plain]
  psi := rd_X ρ m

end Johnson.L5.Layers

#print axioms Johnson.L5.Layers.fit_eq
#print axioms Johnson.L5.Layers.fit_y
#print axioms Johnson.L5.Layers.fit_plain
