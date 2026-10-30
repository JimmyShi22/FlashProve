-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/FoldTriTie.lean: the sum and the rounds' pairs of Johnson/LinkSim/FoldTri.lean are
the library's: the sum of a hiding polynomial (hMu) and the coefficients 0 and 2 of its round
polynomials (hTr), at k plain variables of degree 2 (sVars E 2 k). Statements and proofs. Pure
algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  hMu_list      hMu (sVars E 2 k) W = mu of listW k W.
  hTr_list      pairsOf k (hTr (sVars E 2 k) A W g) = shownW of listW k W, for every carried value
                A and every sampled point g. The reason: the public polynomial of a plain variable
                is X, which has no coefficient 0 or 2. So neither A nor the point enters these two
                coefficients.
Here listW k W is the list of the coefficients W, as the library names them: one pair (linear,
quadratic) for each variable, and the constant. pairsOf k q takes, of the entries q of k round
polynomials, the coefficients 0 and 2 of each round. The carried value A is the coefficient of the
product of the variables' public polynomials, which is added to the hiding polynomial (Lambda in the
docstring of hTr). From round to round it becomes the value that the earlier terms take at the
challenges so far. The honest prover's rounds start with A = 0 (SumPar.honQ, Cb/Ld/LdSum.lean).

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/FoldShift.lean and Johnson/LinkSim/FoldInj.lean use hMu_list and hTr_list;
Johnson/LinkSim/AtText/Fold.lean and Johnson/LinkSim/AtText/FoldInjAt.lean state their lemmas with
pairsOf.

The proof unfolds the definitions hMu, hRc, hTr, HVar.plain (Cb/Ld/LdHide.lean) and sVars
(Cb/Ld/LdSum.lean).

Limits. The linear coefficient of a round polynomial, which does depend on A and on the point, is
not among the pairs. Nothing on the other summand of an honest round polynomial, a sampled
coefficient times the claim polynomial's (sTr; SumPar.honQ, Cb/Ld/LdSum.lean): see
Johnson/LinkSim/SumAdd.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.FoldTri
import Cb.Ld.LdSum

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

variable {E : Type} [Field E]

/-- The coefficients as a list of pairs and the constant. -/
def listW : (k : ℕ) → (HIdx (sVars E 2 k) → E) → List (E × E) × E
  | 0, W => ([], W ())
  | k + 1, W =>
    ((W (.inl (0 : Fin 2)), W (.inl (1 : Fin 2))) :: (listW k fun i => W (.inr i)).1,
      (listW k fun i => W (.inr i)).2)

/-- For each round the coefficients 0 and 2. -/
def pairsOf : (k : ℕ) → (RIdx (sVars E 2 k) → E) → List (E × E)
  | 0, _ => []
  | k + 1, q => (q (.inl (0 : Fin 3)), q (.inl (2 : Fin 3))) :: pairsOf k fun i => q (.inr i)

/-- The sum over a plain variable of a polynomial of degree 2: its values at 0 and at 1. -/
theorem phi_plain (c : Fin 3 → E) : (HVar.plain E 2).phi c = c 0 + (c 0 + c 1 + c 2) := by
  show ∑ s : Bool, (1 : E) • ∑ t : Fin 3, (if s then (1 : E) else 0) ^ (t : ℕ) • c t = _
  rw [Fintype.sum_bool]
  simp [Fin.sum_univ_three]
  ring

/-- A plain variable has total weight 2: nodes 0 and 1, each of weight 1. -/
theorem tot_plain : (HVar.plain E 2).tot = 2 := by
  show ∑ _s : Bool, (1 : E) = 2
  rw [Fintype.sum_bool]
  exact one_add_one_eq_two

/-- The library's sum hMu is mu of listW. -/
theorem hMu_list : ∀ (k : ℕ) (W : HIdx (sVars E 2 k) → E),
    hMu (sVars E 2 k) W = mu (listW k W).1 (listW k W).2
  | 0, _ => rfl
  | k + 1, W => by
      show (HVar.plain E 2).phi (Fin.cons 0 fun t : Fin 2 => W (.inl t) : Fin 3 → E) +
        (HVar.plain E 2).tot • hMu (sVars E 2 k) (fun i => W (.inr i)) =
        (W (.inl (0 : Fin 2)) + W (.inl (1 : Fin 2))) + 2 * mu (listW k fun i => W (.inr i)).1
          (listW k fun i => W (.inr i)).2
      rw [hMu_list k fun i => W (.inr i), phi_plain, tot_plain, smul_eq_mul]
      show (0 : E) + (0 + W (.inl (0 : Fin 2)) + W (.inl (1 : Fin 2))) + _ = _
      ring

/-- The coefficients 0 and 2 of the library's round polynomials are shownW of listW, for every A and
every point. -/
theorem hTr_list : ∀ (k : ℕ) (A : E) (W : HIdx (sVars E 2 k) → E) (g : HPt (sVars E 2 k)),
    pairsOf k (hTr (sVars E 2 k) A W g) = shownW (listW k W).1 (listW k W).2
  | 0, _, _, _ => rfl
  | k + 1, A, W, g => by
      show (hRc (HVar.plain E 2) A (fun t : Fin 2 => W (.inl t))
            (hMu (sVars E 2 k) fun i => W (.inr i)) (0 : Fin 3),
          hRc (HVar.plain E 2) A (fun t : Fin 2 => W (.inl t))
            (hMu (sVars E 2 k) fun i => W (.inr i)) (2 : Fin 3)) ::
          pairsOf k (hTr (sVars E 2 k) _ (fun i => W (.inr i)) g.2) =
        (mu (listW k fun i => W (.inr i)).1 (listW k fun i => W (.inr i)).2,
            W (.inl (1 : Fin 2))) ::
          shownW (listW k fun i => W (.inr i)).1 (listW k fun i => W (.inr i)).2
      rw [hTr_list k _ (fun i => W (.inr i)) g.2, hMu_list k fun i => W (.inr i)]
      have e0 : hRc (HVar.plain E 2) A (fun t : Fin 2 => W (.inl t))
          (mu (listW k fun i => W (.inr i)).1 (listW k fun i => W (.inr i)).2) (0 : Fin 3) =
          mu (listW k fun i => W (.inr i)).1 (listW k fun i => W (.inr i)).2 := by
        show (0 : E) • A + (0 : E) + (if (0 : Fin 3) = 0 then _ else 0) = _
        rw [if_pos rfl, zero_smul, add_zero, zero_add]
      have e2 : hRc (HVar.plain E 2) A (fun t : Fin 2 => W (.inl t))
          (mu (listW k fun i => W (.inr i)).1 (listW k fun i => W (.inr i)).2) (2 : Fin 3) =
          W (.inl (1 : Fin 2)) := by
        show (0 : E) • A + W (.inl (1 : Fin 2)) + (0 : E) = _
        rw [zero_smul, zero_add, add_zero]
      rw [e0, e2]

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.hMu_list
#print axioms OnBytes.LinkSim.hTr_list
