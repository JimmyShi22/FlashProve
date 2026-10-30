-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/Coefficients.lean: the smallness test's step "the weights of every
virtual row on the rows of its array" as a plain function on data.

It is typed after `HTailF2.coefficientsF` (OnBytes/Model/Tail.lean:1192-1223), line for line, and calls
the program's pure routines by name (`onRow`, `formOnes`, `formPoint`, `formPowers`, `eqTab`, `powE`).
It closes no round and reads no view.

Main names:
  `coefBody tl g F`: the state with the weights set. g: what the lookup on the digits returned.
  `coefficientsP tl F`: the step. It refuses at one place alone: the lookup has returned nothing.

Refusals: a guard without a name in the program has the name "routine:line" of the program's text.

Kin: `OnBytes.K.Kc.still tl.coefficients` (OnBytes/K/Kc/Quiet.lean, TailQuiet.lean): the
program's routine itself, run from an empty context, without a name of refusal.
Not claimed: no law is stated here.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Tail

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-- Sets the weights of every virtual row on the rows of its array, written out and as a product
form. -/
def coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Fork := Id.run do
  let theta := F.theta
  let mut F := F
  for n in List.range 4 do
    if let some t := tl.ix.U.getD n none then
      if (F.trees.getD t {}).kind == .table then
        F := onRow F t 0 fun row => formOnes { row with coef := #[oneE] }
  for q in [0, 1] do
    let c := tl.zOf q
    let zk := g.zk.getD q #[]
    for p in c.pieces do
      let zr := zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a)
      let e := eqTab zr
      let R := (F.trees.getD p.tree {}).R
      let w := (Array.range R).map fun r =>
        if p.r0 ≤ r ∧ r < p.r0 + p.Rp then e.getD (r - p.r0) zeroE else zeroE
      F := onRow F p.tree p.row fun row => formPoint { row with coef := w } zr p.r0
  F := onRow F tl.ix.ZZ tl.zzRowReads fun row =>
    formPowers { row with coef := tl.vt } theta tl.tau
  F := onRow F tl.ix.ZZ tl.zzRowTies fun row =>
    formPowers { row with coef := tl.vp } theta tl.tau
  for e in [0, 1] do
    let z := (g.zb e).extract 0 5
    F := onRow F tl.ix.BZ e fun row => formPoint { row with coef := eqTab z } z 0
  F := onRow F tl.ix.BZ 2 fun row => formOnes { row with coef := Array.replicate 32 oneE }
  for mu in List.range tl.NM do
    F := onRow F (tl.gtTree.getD mu 0) 0 fun row =>
      formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
        (tl.shp.getD mu {}).mS
  return F

/-- **The step.** -/
def coefficientsP (tl : HTailF2) (F : Fork) : Except String Fork :=
  match tl.heard with
  | none => .error "coefficientsF:1193"
  | some g => .ok (coefBody tl g F)

end VerifiableInference.Desc.First.TailClaims
