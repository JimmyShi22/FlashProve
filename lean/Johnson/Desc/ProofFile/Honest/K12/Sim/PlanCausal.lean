-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlanCausal.lean: two of the four hypotheses of
`accepts_of_plan` (Johnson/Desc/ProofFile/Honest/K12/PlanB.lean) depend on a proximity test's
sampled challenges only through those of the round "BAT" and of the first fold's rounds. The two are
the structure `ShapeAsks`, on the shape of the state of type `T12` (the type of the verifier's state
inside a test) on entry, after the batching and after the first fold, and the structure `DataAsks`,
on the prover's data. Where the test has two stages or more and h is at most k at the first stage,
these rounds are the first part's, and none is the second part's; that is not stated here (see the
limits). So a condition that is laid in front of the second part, and is not handed that part's
challenges, can hold the two. Three theorems with their proofs, at every job J (`TestJob`,
Johnson/Desc/ProofFile/Honest/K12/Test.lean: what a caller supplies for its test), input w, front fr
(`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test) and coins C (`TestCoins`,
Test.lean).

In this head: D and D' give the sampled challenges by the round's number in the test; "BAT" is round
0. The three theorems have one hypothesis in common: D and D' agree at every number below
1 + (1 + (h + g)), where h and g are those of `sgOf (stA J.p)`: the first stage's sizes, with
g = k - h (`sgOf`, Johnson/Desc/K12/Law/ChainOf.lean; `stA`, PlanB.lean). That is round 0 and the
1 + (h + g) rounds of a fold (`length_aFold`, Johnson/Desc/K12/Honest/Causal.lean). The term is
`testAll` (Test.lean) with the definitions of which it is made, among them `aFold`
(Johnson/Desc/K12/Honest/Stages.lean), a fold's rounds. The rows are `J.first w fr C` (Test.lean);
the first fold's coefficients are `C.hide`. The parts are the two into which Parts.lean, next to
Test.lean, cuts the test's rounds: `firstPart`, "BAT" and the first fold, and `restPart`, all the
rest. The carried coins are the fields of C that `restCoins` (Parts.lean) fills from the stretches
that the second part carries: `hide`, `tails` and `mem`.

  `shapeAsks_congr`: `ShapeAsks` at D gives `ShapeAsks` at D', at the same table of codes K and
    plain data Dp
  `dataAsks_congr`: `DataAsks` at D gives `DataAsks` at D', at the same Dp, cc and R
  `tFold_congr`: `tFold` (PlanB.lean) is the same at D and at D'. `tFold` is the state after the
    first fold: the state after the batching (`TestJob.recB`, Test.lean, at `D 0`), advanced by the
    `decide` function of `guardedProximityTestParts.fold` on the rounds of `aFold`; where that function rejects, the
    state before it is kept (`aRec1`, Stages.lean)

By what. `tFold_congr` rewrites `D 0` to `D' 0` and calls `aFold_congr` (Causal.lean). The two other
theorems copy the clauses that do not mention D and rewrite the rest: `plain` and `allSay` by
`D 0 = D' 0`, `codes₁` and `pub` by `tFold_congr`. Of the hypothesis, the proof of `dataAsks_congr`
uses only `D 0 = D' 0`.

Limits.
- It says which challenges are read; not that the two structures are public: `ShapeAsks`' clauses
  behind the first fold hang, by type, on the first fold's rounds as the term shows them, and so on
  the rows and the first fold's coefficients; `DataAsks` reads the input and the carried coins.
- That the numbers below 1 + (1 + (h + g)) are those of the first part's rounds is not stated here.
  `firstLen` (Parts.lean) counts 2 + k rounds of the first part where the test has two stages or
  more; that is the same number where, besides, h is at most k at the first stage. `exact_plan`
  (Sim/ExactPlan.lean), which calls the two theorems, derives both conditions from its own
  hypotheses. In every other case the hypothesis also requires that D and D' agree at rounds after
  the first part's.
- The state on entry is a function of the input and the front that the job supplies (a field of
  `TestJob`); it is compared with nothing here. No statement that this state is the verifier's.
- J, w, fr and C are the same at D and at D'.
- `FormAsks`, the third structure of PlanB.lean, also reads challenges of later rounds; no theorem
  here is about it.
- Whether any values meet `ShapeAsks` or `DataAsks` is not shown here. Neither has a value that
  meets it in the library yet.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.K12.Honest.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

section
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D D' : ℕ → Fmt.Drawn)
  (h : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) → D n = D' n)
include h

/-- `tFold` (PlanB.lean), the state of type `T12` after the first fold as computed from the term's
rounds, is the same at D and at D'. No statement that this state is the verifier's. -/
theorem tFold_congr : tFold J w fr C D = tFold J w fr C D' := by
  have e0 : D 0 = D' 0 := h 0 (by omega)
  show aRec1 J.p 0 (stA J.p) (laidS J.p) (J.recB w fr (D 0))
      (aFold _ 0 (stA J.p) 1 (J.first w fr C) (rowOf (J.recB w fr (D 0))) D) =
    aRec1 J.p 0 (stA J.p) (laidS J.p) (J.recB w fr (D' 0))
      (aFold _ 0 (stA J.p) 1 (J.first w fr C) (rowOf (J.recB w fr (D' 0))) D')
  rw [e0, aFold_congr _ _ _ _ _ _ D D' h]

/-- **`ShapeAsks` at D gives `ShapeAsks` at D'.** Six of its nine clauses do not mention D; `plain`
reads `D 0`, what "BAT" sampled; `codes₁` and `pub` read `tFold`. -/
theorem shapeAsks_congr {K : Codes} {Dp : Plain} (S : ShapeAsks J w fr C D K Dp) :
    ShapeAsks J w fr C D' K Dp := by
  have e0 : D 0 = D' 0 := h 0 (by omega)
  have eT := tFold_congr J w fr C D D' h
  exact ⟨S.codes, S.door, S.came, S.tidy, S.plainRows, S.claims, by rw [← e0]; exact S.plain,
    by rw [← eT]; exact S.codes₁, by rw [← eT]; exact S.pub⟩

/-- **`DataAsks` at D gives `DataAsks` at D'.** Of D its clauses read only `D 0`, what "BAT"
sampled, and that only in `allSay`. -/
theorem dataAsks_congr {Dp : Plain} {cc : ℕ → ℕ → List UInt64} {R : PlainRows}
    (Dt : DataAsks J w fr C D Dp cc R) : DataAsks J w fr C D' Dp cc R := by
  have e0 : D 0 = D' 0 := h 0 (by omega)
  exact ⟨Dt.cols, Dt.state, Dt.trees, by rw [← e0]; exact Dt.allSay⟩

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.tFold_congr
#print axioms ProofFile.Honest.K12.shapeAsks_congr
#print axioms ProofFile.Honest.K12.dataAsks_congr
