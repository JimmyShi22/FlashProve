-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Fold/FoldClaim.lean: the running claim of the program's fold, read in the field, is
the running claim of the library's fold with short rounds, on a typed transcript that reads the
program's scalars and elements.

The program's k rounds of a fold keep a running claim (`foldClaimRound`, OnBytes/Iop/Fold.lean;
round by round:
`claimAfter`, OnBytes/Tie/Pv/Fold/FoldView.lean). The library's fold with short rounds keeps one too
(`sClaim`, Cb/Ent/FoldShort.lean): in each round n coefficients are sent, the coefficient of one
power is completed from the running claim, and the polynomial is evaluated at the challenge.
OnBytes/Slice/BlkFold.lean has one round of the program's in the field (`readE_foldClaimRound`). It
is the library's step at n = 2, with the LINEAR coefficient left out and completed by the factor 1;
the first scalar sent is the constant coefficient, the second the quadratic one. Here this is
carried through the k rounds. Statements and proofs.

Main names (val: the value of a challenge; n, fx: the number of scalars of a short round, and the
power that is left out with its factor; rd2: how the program's two scalars of a round are read as a
short message):
  `StepOK val n fx rd2`: one step of the library's running claim, at the reading of the program's
    claim, scalars and element, is the reading of the program's step.
  `two c0 c2`, `stepOK_two`: at n = 2, fx = (1, 1) and the reading "constant coefficient, quadratic
    coefficient" it holds.
  `firstN n c0 c2`, `firstN_two`, `stepOK_firstN`: the reading "the first n of the two scalars, 0
  beyond"; at n = 2 it is
    `two`.
  `Reads val n rd2 k τ qs gs`: the typed transcript τ of k short rounds reads the program's pairs qs
    of scalars and its drawn elements gs, round by round.
  `sClaim_reads`: under `StepOK`: the library's running claim from `readE claim` on is `readE` of
  the program's.
  `first_claim`: the claim with which the rounds begin: the sum, and the target times the
coefficient.
Limits: the field is the program's extension field, read by `readE`. `StepOK` is shown
at n = 2, fx = (1, 1), `two` alone. Nothing on forms or words. Nothing on soundness.

-/
import OnBytes.Tie.Pv.Fold.FoldView
import OnBytes.Slice.BlkFold
import Cb.Ent.FoldShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Fold
open OnBytes OnBytes.Slice Iop Cb

variable {Ch : Type} [Fintype Ch] [Nonempty Ch] (val : Ch → GE) (n : ℕ) (fx : Fin (n + 1) × GE)
  (rd2 : E → E → Fin n → GE)

/-- One step of the library's running claim reads one step of the program's. -/
def StepOK : Prop :=
  ∀ (claim c0 c2 g : E) (ch : Ch), val ch = readE g →
    hev (sFill n fx (readE claim) (rd2 c0 c2)) (val ch) = readE (foldClaimRound claim c0 c2 g)

/-- The two scalars of a round, read in the field: the constant and the quadratic coefficient. -/
def two (c0 c2 : E) : Fin 2 → GE := fun t => if t.val = 0 then readE c0 else readE c2

omit [Fintype Ch] [Nonempty Ch] in
theorem stepOK_two : StepOK val 2 ((1 : Fin 3), (1 : GE)) two := fun claim c0 c2 g ch h => by
  rw [readE_foldClaimRound, h]
  rfl

/-- The program's two scalars of a round as a short message of n scalars: the first n of them, 0
beyond. -/
def firstN (n : ℕ) (c0 c2 : E) : Fin n → GE := fun i => (([c0, c2][i.1]?).map readE).getD 0

theorem firstN_two : firstN 2 = two := by
  funext c0 c2 i
  fin_cases i <;> rfl

omit [Fintype Ch] [Nonempty Ch] in
theorem stepOK_firstN : StepOK val 2 ((1 : Fin 3), (1 : GE)) (firstN 2) := by
  rw [firstN_two]
  exact stepOK_two val

/-- The typed transcript reads the program's scalars and elements, round by round. -/
def Reads : ∀ k : ℕ, Tr (List.replicate k (sRoundS GE Ch n)) → List (E × E) → List E → Prop
  | 0, _, [], [] => True
  | k + 1, τ, q :: qs, g :: gs =>
      τ.1.2 = rd2 q.1 q.2 ∧ val τ.2.1 = readE g ∧ Reads k τ.2.2 qs gs
  | _, _, _, _ => False

variable {val n fx rd2}

/-- **The two running claims are one.** -/
theorem sClaim_reads (hs : StepOK val n fx rd2) :
    ∀ (k : ℕ) (τ : Tr (List.replicate k (sRoundS GE Ch n))) (qs : List (E × E)) (gs : List E)
      (claim : E), Reads val n rd2 k τ qs gs →
      sClaim val n fx k (readE claim) τ = readE (claimAfter claim qs gs)
  | 0, _, [], [], _, _ => rfl
  | k + 1, τ, q :: qs, g :: gs, claim, h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [claimAfter_cons, ← sClaim_reads hs k τ.2.2 qs gs _ h3, ← hs claim q.1 q.2 g τ.2.1 h2, ← h1]
    rfl
  | 0, _, [], _ :: _, _, h => h.elim
  | 0, _, _ :: _, _, _, h => h.elim
  | _ + 1, _, [], _, _, h => h.elim
  | _ + 1, _, _ :: _, [], _, h => h.elim

/-- The claim with which the rounds begin. -/
theorem first_claim (sum eps target : E) :
    readE (maddE sum eps target) = readE sum + readE target * readE eps := by
  rw [readE_maddE, mul_comm]

end OnBytes.Tie.Pv.Fold

#print axioms OnBytes.Tie.Pv.Fold.stepOK_firstN
#print axioms OnBytes.Tie.Pv.Fold.sClaim_reads
