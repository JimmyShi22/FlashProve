-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkPlan.lean.

What is here. Law/Mark.lean's `k4MarkRounds_rows` holds the mark's listed rounds against the
verifier's table of K4's rounds under one hypothesis on the plan's numbers: la ≤ muV (the first
product layer has at least la variables). HERE THAT HYPOTHESIS IS SHOWN OF EVERY PLAN WHOSE LAYOUT
THE PROGRAM's FUNCTION `layout` RETURNS, for a shape with routed experts, AND WHOSE NUMBERS OF READS
`readsOf` RETURNS AT THAT LAYOUT (`la_le_muV`): la = ls + lt; 2 ^ ls divides the model's width,
which is not 0, so ls is at most the width's bits lPd; and muV = lNI + lPd + lt. So the listed
rounds are rows of a masked sumcheck's variable at every such plan (`k4MarkRounds_rows_plan`).
Statements and proofs: calls of the library's `admitted_of_layout`
(Johnson/Road/FormsKeysLaid.lean), `laySizes_of_layout` (Johnson/Road/K4/PlanSizes.lean),
`layMore_of_layout`, `le_clog_of_dvd` (Johnson/Road/K4/PlanClauses.lean), and the text of `readsOf`.

Not shown here. THAT THE PUBLIC DATA's LAYOUT AND NUMBERS OF READS ARE SUCH RETURNS: hy and hrd are
hypotheses on public numbers. Nothing is counted here. What the mark's silence gives at any state of
the verifier is not shown. No property is claimed.

  `reads_muV`   the number of variables of the first product layer, off `readsOf`'s text.
  `la_le_muV`   **la ≤ muV.**
  `k4MarkRounds_rows_plan`   **each listed number's row of the verifier's table, at such a plan.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Mark
import Johnson.Road.K4.PlanClauses
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Road (ok_of_refuse admitted_of_layout)
open OnBytes.Road.K4 (laySizes_of_layout layMore_of_layout le_clog_of_dvd)
open OnBytes.Desc.First.K4.Honest

/-- The number of variables of the first product layer. CONDITIONAL: on the return. -/
theorem reads_muV {y : Layer.Lay} {rd : Layer.Reads} (e : Layer.readsOf y = .ok rd) :
    rd.muV = ceilLog2 y.NI + y.lPd + y.h.lt := by
  unfold Layer.readsOf at e
  dsimp only at e
  obtain ⟨-, e⟩ := ok_of_refuse e
  cases e
  rfl

/-- CONDITIONAL on hy, hp3, hrd. **THE FIRST PRODUCT LAYER HAS AT LEAST la VARIABLES.** -/
theorem la_le_muV {hS : Layer.Shape} {pc : List (List String)} {y : Layer.Lay} {rd : Layer.Reads}
    (hy : Layer.layout hS pc = .ok y) (hp3 : hS.p3 = true) (hrd : Layer.readsOf y = .ok rd) :
    y.h.la ≤ rd.muV := by
  have A := admitted_of_layout hy hp3
  have L := laySizes_of_layout hy
  have M := layMore_of_layout hy
  have hls : y.ls ≤ y.lPd := by
    rw [L.lPd, OnBytes.Road.ceilLog2_eq_clog]
    exact le_clog_of_dvd M.bd M.d0
  have hla : y.h.la = y.ls + y.h.lt := by
    rw [A.shape]
    exact A.la
  rw [reads_muV hrd, hla]
  omega

/-- CONDITIONAL on hy, hp3, hrd. **EACH LISTED NUMBER's ROW OF THE VERIFIER's TABLE IS A ROUND OF A
MASKED SUMCHECK's VARIABLE**, at a plan whose layout and numbers of reads the program's functions
return. -/
theorem k4MarkRounds_rows_plan (Q : K4Pub) {hS : Layer.Shape} {pc : List (List String)}
    (hy : Layer.layout hS pc = .ok Q.P.y) (hp3 : hS.p3 = true)
    (hrd : Layer.readsOf Q.P.y = .ok Q.P.rd) :
    ∀ i ∈ k4MarkRounds Q, (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? =
      some { name := .pscRound, sent := 2 } :=
  k4MarkRounds_rows Q (la_le_muV hy hp3 hrd)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.reads_muV
#print axioms ProofFile.Honest.K4.la_le_muV
#print axioms ProofFile.Honest.K4.k4MarkRounds_rows_plan
