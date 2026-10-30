-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Fold.lean: two messages of a proximity test's prover in a form for which
Lean compiles code that runs: the round polynomials of a fold, and the answer to the out-of-domain
(OOD) sample of the oracle message that a code switch sends. Definitions with code, and theorems
that tie them to the forms of Johnson/Prover/Link/ (FoldHolds.lean: `foldQ`; FoldSay.lean: `foldRV`;
SwitchMsg.lean: `gAns`; BodyAll.lean: `ansAt`), of which that folder's laws speak. It hangs on no
frame for an honest side.

Why. A test that plays a prover's part at small synthetic sizes needs code that runs. Evaluations of
terms that call `foldQ` have broken off; `foldPoly` below runs. We take this for the cause, and have
not isolated it: `foldQ` is the library's `SumPar.honQ` at the structure `Sg.par`, which holds an
enumeration of the whole extension field (its challenge set's `Fintype`). `gAns` goes through a
structure with `Classical.decEq`, and Lean compiles no code for it. The forms here name neither
structure.

  `leftTab`, `rightTab`   the claim's coefficients and the stage's message, each as one table with
                 rows on the cube of all row variables: `SumPar.tabL`, `SumPar.tabM`
                 (Cb/Ld/LdSum.lean) at the stage, written out
  `foldPoly`     the round polynomials: the hiding polynomial's part and the sampled coefficient
                 times the claim polynomial's part
  **`foldQ_eq`**   `foldQ s v μ W ε γ = foldPoly s v μ W ε γ`: by unfolding
  `foldShown`    a fold's rounds as a view shows them; **`foldRV_eq`**: they are `foldRV`'s
  `isPad`, `orOne`, `sampleAt`   the last entry of a stage's mask table; an element, or 1 in the
                 place of 0; THE ANSWER: the sum, over the entries of a stage's two tables, of the
                 entry times its weight: the equality weight of the OOD seed's point at the
                 entry's vertex; at the pad: the OOD seed's factor
  `isPad_iff`, `val_unitOf`   the pad is the library's `csPad`; `orOne` is the library's `unitOf`
  **`sampleAt_eq`**   where two stages fit (`CsFit`, OnBytes/Slice/CsData.lean), `ansAt` is
                 `sampleAt` at the next stage's message

Limits.
- `foldQ_eq` and `foldRV_eq` hold at every stage and at all letters, also at a stage without a row
  variable: there both sides of `foldQ_eq` are the function on the empty type, and the two lists of
  `foldRV_eq` hold the one round "FOLD epsilon".
- Where the two stages do not fit, `ansAt` is 0 and `sampleAt` need not be: `sampleAt_eq` asks the
  fit.
- AT A SAMPLED FACTOR 0 THE ANSWER IS MADE WITH 1 IN ITS PLACE (`orOne`), while the verifier's
  switch rejects such a factor: what the term shows there is of no use.
- One answer and one pad: a place whose switches count more answers is not served.
- Equations between two texts. Nothing on a verifier's decision. No honest prover is defined.
  Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Prover.Link.BodyAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

/-! ## 1 The fold's round polynomials -/

/-- The claim's coefficients as one table: row b holds the main table's row b and, beside it, the
mask table's row at b's first h bits, which counts only where all later bits of b are 1. -/
def leftTab (s : Sg) (v : s.cIn.J → GE) : (Fin (s.h + s.g) → Bool) → s.cM.J ⊕ s.cZ.J → GE :=
  fun b =>
  Sum.elim (fun c => v (.inl (b, c))) fun c =>
    v (.inr (fun i => b (Fin.castAdd s.g i), c)) *
      ∏ t : Fin s.g, if b (Fin.natAdd s.h t) then 1 else 0

/-- The stage's message as one table: row b holds the main table's row b and the mask table's row at
b's first h bits. -/
def rightTab (s : Sg) (μ : s.cIn.J → GE) : (Fin (s.h + s.g) → Bool) → s.cM.J ⊕ s.cZ.J → GE :=
  fun b =>
  Sum.elim (fun c => μ (.inl (b, c))) fun c => μ (.inr (fun i => b (Fin.castAdd s.g i), c))

/-- **The round polynomials of a fold**, all three coefficients of each. v: the claim's
coefficients. μ: the stage's message: the main table beside the carried mask table. W: the hiding
polynomial's coefficients. ε: the element that "FOLD epsilon" sampled. γ: the elements that the
rounds "FOLD round" sampled. -/
def foldPoly (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) : RIdx (sVars GE 2 (s.h + s.g)) → GE := fun i =>
  hTr (sVars GE 2 (s.h + s.g)) 0 W γ i + ε * sTr 2 (s.h + s.g) (leftTab s v) (rightTab s μ) γ i

/-- It is `foldQ`. -/
theorem foldQ_eq (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) : foldQ s v μ W ε γ = foldPoly s v μ W ε γ := rfl

/-- **A fold's rounds as a view shows them**: "FOLD epsilon" shows the hiding polynomial's sum; each
"FOLD round" the coefficients 0 and 2 of its polynomial. D: the sampled challenges, by the round's
number. -/
def foldShown (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : List Fmt.RoundView :=
  ⟨[.e (ofE (hMu (sVars GE 2 (s.h + s.g)) W))], D 0⟩ ::
    showRV (s.h + s.g)
      (foldPoly s v μ W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))))
      fun n => D (n + 1)

/-- They are `foldRV`'s. -/
theorem foldRV_eq (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : foldRV s v μ W D = foldShown s v μ W D := rfl

/-! ## 2 The answer to a new oracle message's sample -/

/-- The entry is the last of the stage's mask table: the place of the sample's pad. -/
def isPad (s : Sg) : s.cIn.J → Bool
  | .inl _ => false
  | .inr x => idxOf x + 1 == 2 ^ s.h * s.Z.l

/-- An element; 1 in the place of 0. -/
def orOne (x : GE) : GE := if x = 0 then 1 else x

/-- **The answer**: z: the OOD seed's point. β: the OOD seed's factor. μ: the stage's message. -/
def sampleAt (s : Sg) (z : Fin s.st.na → GE) (β : GE) (μ : s.cIn.J → GE) : GE :=
  ∑ j, (if isPad s j then β else Alg.eqk z fun t => (cubeAt s j).testBit t.val) * μ j

/-- An entry is the last of the mask table just if it is the library's pad. -/
theorem isPad_iff {s s' : Sg} (hf : CsFit s s') (j : s'.cIn.J) :
    isPad s' j = true ↔ j = csPad hf := by
  have hpos : 1 ≤ 2 ^ s'.h * s'.Z.l := by have := hf.mask; omega
  rcases j with x | x
  · constructor
    · intro h; exact absurd h (by simp [isPad])
    · intro h; exact absurd h (by simp [csPad])
  · show (idxOf x + 1 == 2 ^ s'.h * s'.Z.l) = true ↔ _
    rw [beq_iff_eq]
    constructor
    · intro h
      refine congrArg Sum.inr (idxOf_inj ?_)
      rw [idxOf_cell]
      omega
    · intro h
      have h' : x = cell _ _ (2 ^ s'.h * s'.Z.l - 1) (by omega) := Sum.inr.inj h
      rw [h', idxOf_cell]
      omega

/-- The library's "an element as a unit, 1 in the place of 0", as an element. -/
theorem val_unitOf (x : GE) : (unitOf x).val = orOne x := by
  unfold unitOf orOne
  by_cases h : x = 0
  · rw [dif_neg (not_not.2 h), if_pos h]; rfl
  · rw [dif_pos h, if_neg h]; rfl

/-- **Where two stages fit, the answer of Johnson/Prover/Link/BodyAll.lean is this sum at the next
stage's message.** -/
theorem sampleAt_eq (s s' : Sg) (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE)
    (fr : ℕ → GE) (els : List E) (bits : ℕ) :
    ansAt s s' μ' tl fr els bits =
      sampleAt s' (readP _ (els.take bits)) (orOne (readE (els.getD bits zeroE)))
        (gMsg hf μ' tl fr) := by
  unfold ansAt
  rw [dif_pos hf]
  simp only [gAns, Cb.Ood.Sample.val]
  unfold sampleAt
  refine Finset.sum_equiv (csPlace hf) (fun _ => by simp) fun n _ => ?_
  rw [gMsg_place]
  refine congrArg (· * ldNew (Sum.elim μ' tl) (freeOf hf fr) n) ?_
  show Sum.elim _ _ (splitAt (csPad hf) (csPlace hf n)) = _
  by_cases h : csPlace hf n = csPad hf
  · rw [if_pos ((isPad_iff hf _).2 h), h, splitAt_self]
    show (unitOf _).val * 1 = _
    rw [mul_one, val_unitOf]
  · rw [if_neg (fun c => h ((isPad_iff hf _).1 c)), splitAt_ne h]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.foldQ_eq
#print axioms ProofFile.Honest.K12.foldRV_eq
#print axioms ProofFile.Honest.K12.isPad_iff
#print axioms ProofFile.Honest.K12.val_unitOf
#print axioms ProofFile.Honest.K12.sampleAt_eq
