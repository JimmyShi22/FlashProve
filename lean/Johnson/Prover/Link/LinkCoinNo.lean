-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkCoinNo.lean: THE NUMBER OF A COEFFICIENT's NAME IN A HIDING POLYNOMIAL's OWN
ORDER. A definition with code, statements and proofs. Names and numbers alone.

The names: the library's HIdx (sVars GE 2 k) (Cb/Ld/LdHide.lean, Cb/Ld/LdSumPack.lean): hIx l p: the
coefficient of variable l's degree p + 1 (l and p from 0); hCst: the constant. The order: by
variable; in a variable by rising degree; degrees 1, 2 for every variable but the last; 0, 1, 2 for
the last.

  wNo           the number of a name
  wNo_hIx       hIx l p bears 2 l + p where l is not the last variable, and 2 (k - 1) + 1 + p where
                it is
  wNo_hCst      hCst bears 2 (k - 1): in front of the last variable's two
  wNo_lt        every name's number lies below 2 k + 1
  wNo_inj       two names bear two numbers
  wNo_onto      every number below 2 k + 1 is a name's

Limits. Nothing on what a coefficient is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumPack
import OnBytes.Slice.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- **The number of a coefficient's name in the hiding polynomial's own order**: by variable; in a
variable by rising degree; degrees 1, 2 for every variable but the last; 0, 1, 2 for the last. (The
name "inl p" at the head: the first variable's degree p + 1; the name at the end: the constant.) -/
def wNo : (k : ℕ) → HIdx (sVars GE 2 k) → ℕ
  | 0, _ => 0
  | 1, x => Sum.elim (fun p : Fin 2 => 1 + p.val) (fun _ => 0) (x : Fin 2 ⊕ HIdx (sVars GE 2 0))
  | k + 2, x =>
    Sum.elim (fun p : Fin 2 => p.val) (fun y => 2 + wNo (k + 1) y)
      (x : Fin 2 ⊕ HIdx (sVars GE 2 (k + 1)))

theorem wNo_hCst : ∀ k : ℕ, wNo k (hCst GE 2 k) = 2 * (k - 1)
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show 2 + wNo (k + 1) (hCst GE 2 (k + 1)) = 2 * (k + 2 - 1)
    rw [wNo_hCst (k + 1)]
    omega

theorem wNo_hIx : ∀ (k : ℕ) (l : Fin k) (p : Fin 2),
    wNo k (hIx GE 2 k l p) =
      if l.val + 1 < k then 2 * l.val + p.val else 2 * (k - 1) + 1 + p.val
  | 0, l, _ => l.elim0
  | 1, l, p => by
    obtain rfl : l = 0 := Subsingleton.elim _ _
    show 1 + p.val = _
    simp
  | k + 2, l, p => by
    refine Fin.cases ?_ (fun l' => ?_) l
    · show p.val = _
      simp
    · show 2 + wNo (k + 1) (hIx GE 2 (k + 1) l' p) = _
      rw [wNo_hIx (k + 1) l' p]
      simp only [Fin.val_succ]
      split_ifs <;> omega

theorem wNo_lt : ∀ (k : ℕ) (x : HIdx (sVars GE 2 k)), wNo k x < 2 * k + 1
  | 0, _ => Nat.zero_lt_one
  | 1, x => by
    cases x with
    | inl p =>
      show 1 + p.val < 3
      have : p.val < 2 := p.isLt
      omega
    | inr _ => exact Nat.zero_lt_succ _
  | k + 2, x => by
    cases x with
    | inl p =>
      show p.val < 2 * (k + 2) + 1
      have : p.val < 2 := p.isLt
      omega
    | inr y =>
      show 2 + wNo (k + 1) y < 2 * (k + 2) + 1
      have := wNo_lt (k + 1) y
      omega

theorem wNo_inj : ∀ (k : ℕ) (x y : HIdx (sVars GE 2 k)), wNo k x = wNo k y → x = y
  | 0, x, y, _ => by
    cases x
    cases y
    rfl
  | 1, x, y, h => by
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        have h' : 1 + p.val = 1 + q.val := h
        exact congrArg Sum.inl (Fin.ext (by omega))
      | inr _ =>
        have h' : 1 + p.val = 0 := h
        omega
    | inr u =>
      cases y with
      | inl q =>
        have h' : 0 = 1 + q.val := h
        omega
      | inr v =>
        cases u
        cases v
        rfl
  | k + 2, x, y, h => by
    cases x with
    | inl p =>
      cases y with
      | inl q =>
        have h' : p.val = q.val := h
        exact congrArg Sum.inl (Fin.ext h')
      | inr v =>
        have h' : p.val = 2 + wNo (k + 1) v := h
        have : p.val < 2 := p.isLt
        omega
    | inr u =>
      cases y with
      | inl q =>
        have h' : 2 + wNo (k + 1) u = q.val := h
        have : q.val < 2 := q.isLt
        omega
      | inr v =>
        have h' : 2 + wNo (k + 1) u = 2 + wNo (k + 1) v := h
        exact congrArg Sum.inr (wNo_inj (k + 1) u v (by omega))

theorem wNo_onto : ∀ (k n : ℕ), n < 2 * k + 1 → ∃ x : HIdx (sVars GE 2 k), wNo k x = n
  | 0, n, h => ⟨(), by show 0 = n; omega⟩
  | 1, n, h => by
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with e | e | e
    · exact ⟨(Sum.inr () : Fin 2 ⊕ HIdx (sVars GE 2 0)), e.symm⟩
    · exact ⟨(Sum.inl 0 : Fin 2 ⊕ HIdx (sVars GE 2 0)), e.symm⟩
    · exact ⟨(Sum.inl 1 : Fin 2 ⊕ HIdx (sVars GE 2 0)), e.symm⟩
  | k + 2, n, h => by
    by_cases h2 : n < 2
    · exact ⟨(Sum.inl ⟨n, h2⟩ : Fin 2 ⊕ HIdx (sVars GE 2 (k + 1))), rfl⟩
    · obtain ⟨y, hy⟩ := wNo_onto (k + 1) (n - 2) (by omega)
      refine ⟨(Sum.inr y : Fin 2 ⊕ HIdx (sVars GE 2 (k + 1))), ?_⟩
      show 2 + wNo (k + 1) y = n
      omega

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.wNo_hCst
#print axioms Johnson.Prover.Link.wNo_hIx
#print axioms Johnson.Prover.Link.wNo_lt
#print axioms Johnson.Prover.Link.wNo_inj
#print axioms Johnson.Prover.Link.wNo_onto
