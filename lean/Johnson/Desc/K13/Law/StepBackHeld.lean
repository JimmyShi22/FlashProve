-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/StepBackHeld.lean: the step back from (Eval) at the decoded table: (Eval), "the
other vector
is the row weights applied to the matrix that the stored table decodes to" (`VIs` at `TabX2`) and
"held" give the claim on the matrix that the cells hold. A statement with its proof, in K13's files'
own terms: no table of joints, no piece, no promise stands in it.
Main names:
  `claim_of_eval_held`: **where the library's decoder with the record gives U and the cells c are
    held U: (Eval) says its claim of the words just if the claim's row on the matrix is true of the
    matrix that c holds and of the words' mask entries.** Both ways.
It joins `stepBack` (Johnson/Desc/K13/Law/StepBack.lean), `tabX2_of_dcd` and `HeldTie`
(Johnson/Desc/K13/Law/HeldTab.lean). USER: `s4a_paid` (Johnson/Desc/K13/Law/PointStepBack.lean).

What is not claimed. The premises: the three public facts on the record of (Eval) (`EvalAt.Ok`);
that g is the sum of the claim's vectors' entries; that the vector V lies in W's message under W's
layout; `VIs`; "held". Nothing on soundness.

-/
import Johnson.Desc.K13.Law.StepBack
import Johnson.Desc.K13.Law.HeldTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy matBy_congr stepBack)

/-- **The step back from (Eval) at the decoded table, and the step forth.** -/
theorem claim_of_eval_held {Cells : Type} (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (matC : Cells → Nat → Nat → GE) (hH : HeldTie p err₂ eM rank held matC)
    (cl : Nat → Option (Nat × List UInt64)) (s : St)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE)
    (hU : dcdAt p err₂ eM rank cl (recAt p err₂ eM rank s) = some U) (c : Cells)
    (hc : held U = some c) (D : EvalAt) (hD : D.Ok p.S) (m : Words GE) (g V : Nat → GE)
    (hg : ∀ y < p.S.matrixRows,
      g y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hvec : ∀ e < 2 ^ p.S.kCol, m D.w .main (D.lay.index e) = V e)
    (hV : VIs p.S g (TabX2 p err₂ eM rank (colsOf cl) s.loc.key) V) :
    OnBytes.Means.Says OnBytes.Model.Reading.gl D.st D.r m ↔
      VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
        (witOf (matBy (nR := p.S.matrixRows) p.S.kCol (matC c)) m) D.row := by
  rw [tabX2_of_dcd p err₂ eM rank cl s U hU] at hV
  rw [matBy_congr (hH U c hc)]
  exact stepBack p.S D hD m (matOf p.S.kLo (tabU p err₂ eM rank U)) g V hg hvec hV

end Desc.K14.Law
