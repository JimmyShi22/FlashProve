-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/PieceLiveOfStatement.lean: THE KIND K8 (the sub-protocol that tests that
values are small): `PieceLive`, "the weights that its second computation multiplies do not read as
0" (Johnson/Desc/K8/Honest/SecondNz.lean) FROM "NEITHER 0 NOR 1": STATEMENTS ALONE: four definitions
of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are
lemmas' statements. On field words, arrays and numbers: no state of the verifier, no ledger, no
sub-protocol, no prover.

WHAT IT IS NOT. THAT THE FIRST COORDINATE OF zy AND THE COORDINATES OF zk's POINTS ARE NEITHER 0 NOR
1 AT ANY STATE IS NOT SAID: these are premises here.

  `EqPlainFNe`         a point z whose every coordinate reads as neither 0 nor 1: the plain product
                       `eqPlainF z idx` (OnBytes/Model/FormF.lean) does not read as 0, at every idx
  `EqAtNe`             the same of the run's value `eqAt z first i`
                       (Johnson/Desc/First/TailClaims/AgainMeans.lean)
  `CallWeightAgainNe`  where the first coordinate of g.zy reads as neither 0 nor 1, the call's
                       weight by the second computation (`callWeightAgain`,
                       OnBytes/Model/Tail.lean) does not read as 0, at every call
  `PieceLiveOfFine`    so: `PieceLive tl g W`, where that holds of g.zy's first coordinate and of
                       every coordinate of g.zk's point at each wanted piece's call

THE PREMISES' FORM. The two inequalities are written out. They are the text of `P1K8.Fine`
(Johnson/P1K8R/DigitsOfSilence.lean, a file that is not in this library), which is not imported. A
premise on fewer coordinates does not serve: the product runs over all of them. At one fixed index
half of each pair would do (not 0 where the index's bit is 1, not 1 where it is 0); a piece's
indices are many, so both halves are asked.

NEAR. `P1K8.weight_fold`, `P1K8.callWeight_ne` (DigitsOfSilence.lean, the same file): the like
product at another text of the bit test (`Forest.callWeight`). The library's `eq_zero_ne` over
`wt_zero_ne` (Johnson/Desc/Kinds/Law/K06ToyDraws.lean): the like at the index 0 alone, at another
text of the weight.

Limits. By values. Nothing on any property.
-/
import Johnson.Desc.K8.Honest.SecondNz

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims (eqAt)

/-- The statement on the plain product. Not proved here; a lemma's statement, none of the library's
goals. -/
def EqPlainFNe : Prop :=
  ∀ (z : Array E) (idx : Nat),
    (∀ v, v < z.size →
      Reading.gl.val (z.getD v zeroE) ≠ 0 ∧ Reading.gl.val (z.getD v zeroE) ≠ 1) →
    Reading.gl.val (eqPlainF z idx) ≠ 0

/-- The statement on the run's value. Not proved here; a lemma's statement, none of the library's
goals. -/
def EqAtNe : Prop :=
  ∀ (z : Array E) (first i : Nat),
    (∀ v, v < z.size →
      Reading.gl.val (z.getD v zeroE) ≠ 0 ∧ Reading.gl.val (z.getD v zeroE) ≠ 1) →
    Reading.gl.val (eqAt z first i) ≠ 0

/-- The statement on the call's weight. Not proved here; a lemma's statement, none of the library's
goals. -/
def CallWeightAgainNe : Prop :=
  ∀ (g : Forest.Heard) (q : Nat),
    (Reading.gl.val (g.zy.getD 0 zeroE) ≠ 0 ∧ Reading.gl.val (g.zy.getD 0 zeroE) ≠ 1) →
    Reading.gl.val (callWeightAgain g q) ≠ 0

/-- The statement of the title. Not proved here; a lemma's statement, none of the library's goals.
-/
def PieceLiveOfFine : Prop :=
  ∀ (tl : HTailF2) (g : Forest.Heard) (W : List Want),
    (Reading.gl.val (g.zy.getD 0 zeroE) ≠ 0 ∧ Reading.gl.val (g.zy.getD 0 zeroE) ≠ 1) →
    (∀ w ∈ W, ∀ v, v < (g.zk.getD w.call #[]).size →
      Reading.gl.val ((g.zk.getD w.call #[]).getD v zeroE) ≠ 0 ∧
        Reading.gl.val ((g.zk.getD w.call #[]).getD v zeroE) ≠ 1) →
    PieceLive tl g W

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.EqPlainFNe
#print axioms VerifiableInference.Desc.First.K8.Honest.EqAtNe
#print axioms VerifiableInference.Desc.First.K8.Honest.CallWeightAgainNe
#print axioms VerifiableInference.Desc.First.K8.Honest.PieceLiveOfFine
