-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/NzOk.lean: a test on the plan: no declared round of the proximity test (the
kind K12) asks more elements other than 0 than elements (drawNZ ≤ drawE).

This is the one premise on the entries of roundsFit_behind (Johnson/Desc/K12/Law/FitWritten.lean).
Definitions with code alone and no theorem, so that the test can be compiled and run.
Main names:
  `nzOn`, `nzOk`: one clause for each declared round, under its number and name; the test, which is
    false where the numbers give no rounds.
  `nzLines`: the lines that a run prints, with one control, due false: the last round asks one
    element other than 0 more than elements.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.
nzOk was evaluated at the four proximity tests of both stored proofs and at the proximity test of
the product test's stored tiny proof: true at each, the control false [the prints are not in this
library].

-/
import Johnson.Desc.K12.Law.FirstOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

def nzOn (ds : List Fmt.DeclaredRound) : Clauses :=
  ds.zipIdx.map fun x => (toString x.2 ++ ":" ++ x.1.entry.name,
      decide (x.1.entry.drawNZ ≤ x.1.entry.drawE))

/-- The test: the numbers give rounds, and every clause says yes. -/
def nzOk (p : P12) : Bool := (H2U.roundsOfNums p.nums).any fun ds => ok (nzOn ds)

def spoilLast (ds : List Fmt.DeclaredRound) : List Fmt.DeclaredRound :=
  match ds.reverse with
  | d :: r => ({ d with entry := { d.entry with drawNZ := d.entry.drawE + 1 } } :: r).reverse
  | [] => []

def nzLines (tagS : String) (p : P12) : List String :=
  let ds := (H2U.roundsOfNums p.nums).getD []
  [s!"{tagS}.NZ\tnzOk {nzOk p}\tclauses {(nzOn ds).length}\trefusing: {((nzOn ds).filter (!·.2)).map
      (·.1)}\t(name, drawE, drawNZ) where drawNZ > 0: {(ds.filter fun d =>
      decide (0 < d.entry.drawNZ)).map fun d => (d.entry.name, d.entry.drawE, d.entry.drawNZ)}",
   s!"{tagS}.NZ.control\tthe last round asks one element other than 0 more than elements\t{ok (nzOn
       (spoilLast ds))}\trefusing: {((nzOn (spoilLast ds)).filter (!·.2)).map (·.1)}"]

end H2K.First
