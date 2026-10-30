-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevRunA.lean: the short sumcheck on k equality-weighted cube variables of degree 2
and the dummy variable Y of degree 2, written out: what its verifier reads off a
transcript, as plain functions of the flat view of that transcript.

States, for the list of formats `lk k` (k cube variables, then Y) with the data `dk k z` (equality
weights at z, then Y's):
  `psi_one`    the product of the public polynomials is 1 at every point.
  `row_form`   the linear form hSl (the value of the library's polynomial hU in its coefficients),
                  pushed to the entries by a map w of names: `rowF`: c_j at the name of X_j, c_j² at
                  that of X_j²,
               1 at the name of the constant.
  `fin_view`   the last value of the running claim: `finC`: under the weight at z the constant is σ
                  − z (q₁ + q₂); in Y it is σ.
  `ch_view`    the challenge of round j. `tail_view`: what stands behind the k + 1 rounds.
Names of coefficients: `nmV k j t` (round j, power t + 1), `nmC k` (the constant). Readers: `fuK k`.
Under: nothing, but that `ch_view` speaks of the rounds j ≤ k. It names no honest side and imports
no file of the port.

-/
import Cb.Pv.KeyLookup.ShortPt
import Cb.Pv.KeyLookup.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Lev
open Cb Cb.LdLkp Iop IOR Hiop Prob Johnson.L5.Layers Flat

/-- c at the entry i, 0 elsewhere -/
def one {E J : Type} [Zero E] [DecidableEq J] (i : J) (c : E) : J → E := fun j => if j = i then c
    else 0

theorem ite_one {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E) (inst : Decidable (i = j)) :
    @ite E (i = j) inst c 0 = one i c j := by
  unfold one
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun e => h e.symm]

theorem ite_one' {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E) (inst : Decidable (j = i))
    :
    @ite E (j = i) inst c 0 = one i c j := by
  unfold one
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

section
variable (E : Type) [Field E] [Fintype E]

/-- k cube variables of degree 2, then Y of degree 2 -/
noncomputable abbrev lk (k : ℕ) : List (PFmt E) := List.replicate k (pfCube E 2) ++ [pDummy E 2]

/-- equality weights at z, then Y's data -/
noncomputable abbrev dk (k : ℕ) (z : Fin k → E) : PDats (lk E k) :=
  PDats.snoc (List.replicate k (pfCube E 2)) (pdEqs E 2 k z) (pDummy E 2) (pDummyD E 2)

/-- the name of the coefficient of the power t + 1 in round j (from round k on: Y's); of the
constant -/
def nmV : (k : ℕ) → ℕ → Fin 2 → PIdx (lk E k)
  | 0, _, t => (Sum.inl t : Fin 2 ⊕ Unit)
  | _ + 1, 0, t => Sum.inl t
  | k + 1, j + 1, t => Sum.inr (nmV k j t)
def nmC : (k : ℕ) → PIdx (lk E k)
  | 0 => (Sum.inr () : Fin 2 ⊕ Unit)
  | k + 1 => Sum.inr (nmC k)

end

section
variable {E : Type} [Field E] [Fintype E]

/-- the form hSl on the entries -/
def rowF {J : Type} [DecidableEq J] : (k : ℕ) → (ℕ → Fin 2 → J) → J → (ℕ → E) → J → E
  | 0, wv, wc, c, i => one (wv 0 0) (c 0) i + one (wv 0 1) (c 0 ^ 2) i + one wc 1 i
  | k + 1, wv, wc, c, i =>
    one (wv 0 0) (c 0) i + one (wv 0 1) (c 0 ^ 2) i + rowF k (fun j => wv (j + 1)) wc (fun j => c
        (j + 1)) i

theorem hev_const (x : E) : hev (pvConst E 2 1) x = 1 := by
  show ∑ t : Fin 3, x ^ (t : ℕ) • (if (t : ℕ) = 0 then (1 : E) else 0) = 1
  simp [Fin.sum_univ_succ]

theorem hev_dummy (x : E) : hev (pDummyD E 2).psi x = 1 := by
  show ∑ t : Fin 3, x ^ (t : ℕ) • (if t = 0 then (1 : E) else 0) = 1
  simp [Fin.sum_univ_succ]

theorem psi_one : ∀ (k : ℕ) (z : Fin k → E) (X : HPt (pVars (lk E k) (dk E k z))),
    hPsi (pVars (lk E k) (dk E k z)) X = 1
  | 0, _, X => by
    show hev (pDummyD E 2).psi X.1 * 1 = 1
    rw [hev_dummy, one_mul]
  | k + 1, z, X => by
    show hev (pvConst E 2 1) X.1 * hPsi (pVars (lk E k) (dk E k fun i => z i.succ)) X.2 = 1
    rw [hev_const, psi_one k (fun i => z i.succ) X.2, one_mul]

omit [Fintype E] in
theorem sum_hidx_cons (v : HVar E) (l : List (HVar E)) (g : HIdx (v :: l) → E) :
    ∑ i, g i = ∑ t : Fin v.n, g (.inl t) + ∑ i : HIdx l, g (.inr i) := by
  show ∑ i : Fin v.n ⊕ HIdx l, g i = _
  exact Fintype.sum_sum_type g

omit [Fintype E] in
theorem sum_hidx_nil (g : HIdx ([] : List (HVar E)) → E) : ∑ i, g i = g () := by
  exact Fintype.sum_unique (fun a : Unit => g a)

theorem row_form {J : Type} [DecidableEq J] : ∀ (k : ℕ) (z : Fin k → E) (w : PIdx (lk E k) → J)
    (γ : PPt (lk E k)) (j : J),
    (∑ i, @ite E (w (pIx (lk E k) (dk E k z) i) = j) (Classical.propDecidable _)
      (hSl (pVars (lk E k) (dk E k z)) (pH (lk E k) (dk E k z) γ) i) 0) =
      rowF k (fun r t => w (nmV E k r t)) (w (nmC E k)) (ppGet (lk E k) γ) j
  | 0, z, w, γ, j => by
    refine (sum_hidx_cons ((pDummy E 2).var (pDummyD E 2)) [] _).trans ?_
    rw [sum_hidx_nil]
    show (∑ t : Fin 2, @ite E (w (Sum.inl t) = j) (Classical.propDecidable _) (1 * γ.1 ^ ((t : ℕ) +
        1)) 0) +
      @ite E (w (Sum.inr ()) = j) (Classical.propDecidable _) 1 0 = _
    rw [Fin.sum_univ_two, ite_one, ite_one, ite_one]
    show one _ (1 * γ.1 ^ (0 + 1)) j + one _ (1 * γ.1 ^ (1 + 1)) j + one _ 1 j =
      one _ γ.1 j + one _ (γ.1 ^ 2) j + one _ 1 j
    rw [one_mul, one_mul, zero_add, pow_one]
    rfl
  | k + 1, z, w, γ, j => by
    refine (sum_hidx_cons ((pfCube E 2).var (pdEq E 2 (z 0)))
      (pVars (lk E k) (dk E k fun i => z i.succ)) _).trans ?_
    have ih := row_form k (fun i => z i.succ) (fun n => w (Sum.inr n)) γ.2 j
    show (∑ t : Fin 2, @ite E (w (Sum.inl t) = j) (Classical.propDecidable _)
        (hPsi (pVars (lk E k) (dk E k fun i => z i.succ)) (pH (lk E k) (dk E k fun i => z i.succ)
            γ.2) *
          γ.1 ^ ((t : ℕ) + 1)) 0) +
      (∑ i, @ite E (w (Sum.inr (pIx (lk E k) (dk E k fun i => z i.succ) i)) = j)
          (Classical.propDecidable _)
        (hSl (pVars (lk E k) (dk E k fun i => z i.succ)) (pH (lk E k) (dk E k fun i => z i.succ)
            γ.2) i) 0) = _
    rw [ih, psi_one, Fin.sum_univ_two, ite_one, ite_one]
    show one _ (1 * γ.1 ^ (0 + 1)) j + one _ (1 * γ.1 ^ (1 + 1)) j + _ = one _ γ.1 j + one _ (γ.1 ^
        2) j + _
    rw [one_mul, one_mul, zero_add, pow_one]
    rfl

/-- a polynomial completed at its constant, at the draw: under an equality weight; in Y -/
theorem fill_eq (z σ γ : E) (q : Fin 2 → E) :
    hev (hFill ((pfCube E 2).var (pdEq E 2 z)) ((0 : Fin 3), (1 : E)) σ q) γ =
      σ - z * (q 0 + q 1) + q 0 * γ + q 1 * γ ^ 2 := by
  have h0 : ((pfCube E 2).var (pdEq E 2 z)).phi ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) =
      z * (q 0 + q 1) := by
    show ∑ b : Bool, (if b then z else 1 - z) • ∑ t : Fin 3, (if b then (1 : E) else 0) ^ (t : ℕ) •
      ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) t = _
    rw [Fintype.sum_bool]
    simp [Fin.sum_univ_succ]
  show hev ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ -
    ((pfCube E 2).var (pdEq E 2 z)).phi ((0 : Fin 3).insertNth (α := fun _ => E) 0 q))) q) γ = _
  rw [h0]
  show ∑ t : Fin 3, γ ^ (t : ℕ) •
    ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ - z * (q 0 + q 1))) q) t = _
  simp [Fin.sum_univ_succ]
  ring

theorem fill_dummy (σ β : E) (q : Fin 2 → E) :
    hev (hFill ((pDummy E 2).var (pDummyD E 2)) ((0 : Fin 3), (1 : E)) σ q) β =
      σ + q 0 * β + q 1 * β ^ 2 := by
  have h0 : ((pDummy E 2).var (pDummyD E 2)).phi
      ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) = 0 := by
    show ∑ _s : Unit, (1 : E) • ∑ t : Fin 3, (0 : E) ^ (t : ℕ) •
      ((0 : Fin 3).insertNth (α := fun _ => E) 0 q) t = 0
    simp [Fin.sum_univ_succ]
  show hev ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ -
    ((pDummy E 2).var (pDummyD E 2)).phi ((0 : Fin 3).insertNth (α := fun _ => E) 0 q))) q) β = _
  rw [h0]
  show ∑ t : Fin 3, β ^ (t : ℕ) •
    ((0 : Fin 3).insertNth (α := fun _ => E) ((1 : E) • (σ - 0)) q) t = _
  simp [Fin.sum_univ_succ]
  ring

end

/-! ### the flat side -/
section
variable {E : Type} [Field E]

/-- scalar number t sent in round j; the element drawn in round j -/
def snt (f : List (RV E)) (j t : ℕ) : E := (f.getD j ([], [])).1.getD t 0
def chC (f : List (RV E)) (j : ℕ) : E := (f.getD j ([], [])).2.headD 0

/-- the running claim behind k rounds under equality weights at z and Y's round -/
def finC : (k : ℕ) → (Fin k → E) → E → List (RV E) → E
  | 0, _, σ, f => σ + snt f 0 0 * chC f 0 + snt f 0 1 * chC f 0 ^ 2
  | k + 1, z, σ, f =>
    finC k (fun i => z i.succ)
      (σ - z 0 * (snt f 0 0 + snt f 0 1) + snt f 0 0 * chC f 0 + snt f 0 1 * chC f 0 ^ 2) f.tail

theorem snt_cons (v : RV E) (f : List (RV E)) (j t : ℕ) : snt (v :: f) (j + 1) t = snt f j t := rfl
theorem chC_cons (v : RV E) (f : List (RV E)) (j : ℕ) : chC (v :: f) (j + 1) = chC f j := rfl

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- how the draws of the k + 1 rounds are written -/
def fuK : (k : ℕ) → FUs (lk E k)
  | 0 => (fuDummy 2, ())
  | k + 1 => (fuCube 2, fuK k)

variable {t : Shape} (B : RdS E t)

theorem fin_view : ∀ (k : ℕ) (z : Fin k → E) (σ : E) (τ : Tr (sRounds (lk E k) ++ t)),
    (TWhole.vFinT (lk E k) (dk E k z) (TWhole.fix0 (pVars (lk E k) (dk E k z))) σ t τ).1.1 =
      finC k z σ (((rdVars (lk E k) (fuK k)).app B).view τ)
  | 0, _, σ, (m, c, τ) => by
    show hev (hFill ((pDummy E 2).var (pDummyD E 2)) ((0 : Fin 3), (1 : E)) σ m.2) c.1 = _
    rw [fill_dummy]
    have e0 : (List.ofFn m.2).getD 0 0 = m.2 (0 : Fin 2) := getD_ofFn (n := 2) m.2 (0 : Fin 2)
    have e1 : (List.ofFn m.2).getD 1 0 = m.2 (1 : Fin 2) := getD_ofFn (n := 2) m.2 (1 : Fin 2)
    show _ = σ + (List.ofFn m.2).getD 0 0 * c.1 + (List.ofFn m.2).getD 1 0 * c.1 ^ 2
    rw [e0, e1]
  | k + 1, z, σ, (m, c, τ) => by
    have ih := fin_view k (fun i => z i.succ)
      (hev (hFill ((pfCube E 2).var (pdEq E 2 (z 0))) ((0 : Fin 3), (1 : E)) σ m.2) c) τ
    refine ih.trans ?_
    rw [fill_eq]
    show _ = finC k (fun i => z i.succ)
      (σ - z 0 * ((List.ofFn m.2).getD 0 0 + (List.ofFn m.2).getD 1 0) + (List.ofFn m.2).getD 0 0 *
          c +
        (List.ofFn m.2).getD 1 0 * c ^ 2) (((rdVars (lk E k) (fuK k)).app B).view τ)
    have e0 : (List.ofFn m.2).getD 0 0 = m.2 0 := getD_ofFn m.2 (0 : Fin 2)
    have e1 : (List.ofFn m.2).getD 1 0 = m.2 1 := getD_ofFn m.2 (1 : Fin 2)
    rw [e0, e1]

theorem ch_view : ∀ (k : ℕ) (τ : Tr (sRounds (lk E k) ++ t)) (j : ℕ), j ≤ k →
    chS (lk E k) t τ j = chC (((rdVars (lk E k) (fuK k)).app B).view τ) j
  | 0, (_, _, _), 0, _ => rfl
  | 0, _, j + 1, h => absurd h (Nat.not_succ_le_zero j)
  | _ + 1, (_, _, _), 0, _ => rfl
  | k + 1, (_, _, τ), j + 1, h => ch_view k τ j (Nat.le_of_succ_le_succ h)

theorem tail_view : ∀ (k : ℕ) (z : Fin k → E) (σ : E) (τ : Tr (sRounds (lk E k) ++ t)) (i : ℕ),
    (((rdVars (lk E k) (fuK k)).app B).view τ).getD (k + 1 + i) ([], []) =
      (B.view (TWhole.vFinT (lk E k) (dk E k z) (TWhole.fix0 (pVars (lk E k) (dk E k z))) σ t
          τ).2).getD i ([], [])
  | 0, _, _, (_, _, _), i => by
    rw [Nat.zero_add, Nat.add_comm]
    rfl
  | k + 1, z, σ, (m, c, τ), i => by
    have ih := tail_view k (fun i => z i.succ)
      (hev (hFill ((pfCube E 2).var (pdEq E 2 (z 0))) ((0 : Fin 3), (1 : E)) σ m.2) c) τ i
    refine Eq.trans ?_ ih
    have e : k + 1 + 1 + i = (k + 1 + i) + 1 := by omega
    rw [e]
    rfl

end
end Lev
end Lk6
