-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Inf/Spec.lean: the relation `R` of the model, at the reference scales, under the policy
  of exact match (words of this library: lean/GLOSSARY.md).

  `R i x` holds if the integer program with the weights i, at the reference parameters and tables,
  runs on the tokens of the request x and the clauses of the policy `AcceptancePolicy.exact` hold of its logits
  (`RinfR0`, Inst/Model/ProgramRPol.lean; on requests: Inst/Model/ProgramR.lean). Equivalently, the
  program runs and every covered token is the least token of largest logit at its position
  (`RinfS0_iff_exact`, Inst/Model/ProgramRExact.lean). On the request "the next token" this is
  Model_i(prompt) = y (`infR_next`, Inst/Model/RequestGuards.lean).
  Notation:
    runs: `RunsK` (Inst/Model/Program.lean): `Runs` with the scales and tables of each layer;
      `Runs`: a `Prop`: no range condition fails.
    `ppref.scale` (`Params.scale`, Inst/Model/Program.lean): a `LayerScale`: the scales that P has
      for all layers; `tbRef` (Inst/Model/TablesRef.lean): `Tables`: the table functions at `ppref`.
    covered: r ≤ t < e, of a position t of the request x (`Instance`, Inst/Model/Program.lean;
      Inst/Model/ProgramR.lean).

  Limits: `R` does not include the request's form (`Head3`: r < e ≤ T, and y = 0 if e < T).
-/
import Blocks.StageSide
import Blocks.AlignedPlaces
import Inst.Model.IndexM
import Blocks.RngFront
import Blocks.RngNums
import Blocks.RngSmall
import Blocks.RngArr
import Mathlib.Algebra.CharP.Algebra
import Inst.Model.TablesRef
import Inst.Model.Inf.Data
import Inst.Model.ProgramR
import Inst.Model.ProgramRPol
import Blocks.Numbering
import Blocks.SerS
import Compile.Spec
import Blocks.ClosingPlaces
import Blocks.LookupPlaces
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Inst.Model.Inf

open Iop Blocks Code Inst.Model.Params
open scoped ENNReal

/-- The relation of the model, without the request's form (`Head3`). This file has no test of that
form. -/
def R (i : Index ppref) (x : Instance ppref) : Prop :=
  RinfR0 ppref (fun _ => ppref.scale) ppref.nf (fun _ => tbRef) AcceptancePolicy.exact i x

end Inst.Model.Inf
