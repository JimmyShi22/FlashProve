-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysIdnLRun.lean: the two theorems of Johnson/Road/FormsKeysIdnL.lean on claims
that read long tables, evaluated on made-up numbers.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof, and it speaks of these numbers alone. This file holds no theorem.

What is evaluated. The shape, the sizes, the points and the made-up world of
Johnson/Road/FormsKeysIdnWRun.lean: hR8 with pcR8, both groups of layers, dimP hR8; every entry of
the reads holds what a true table holds of made-up cells; a slot is valued 0. On the verifier's
side: its own tabAt, T_, hiTab, and normsSum and embSum, which are the sums in the text of
claimsNorms and claimEmbedding (claimsNorms_eq, claimEmbedding_eq). The weights e are those that
claimsNorms makes from the challenges of the product layer of the squares; the powers gp are five
made-up elements. On the library's side: its own bS, xS, eqN and ext, over the integers modulo the
verifier's prime.

The marks, for each group.
 1. The tables of the stream that comes in and of af at Z_V are found, the tensor xs, the weights,
    and normsSum returns.
 2. (T-end): the equation of Fits.normsEnd, with 0 under the slot.
 3. In the first group: the table at Z_E is found, embSum returns, and the equation of
    Fits.embedding holds, with 0 under the slot. In the other group: no table is found at Z_E.
 4. A control: with other powers gp on the library's side, mark 2 fails.
 5. The right side of mark 2 is not 0.

What is not run: a slot with a value other than 0; any other shape. The program does not import this
file.
-/
import Johnson.Road.FormsKeysIdnL
import Johnson.Road.FormsKeysIdnWRun

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Aff lastOf hiTab eqTab)
open Inst.Model.FFSeg (bS xS)

/-- The marks, in one group. -/
def idnLB (r : RunP) : List Bool :=
  let y := r.v.y
  let D := dimP hR8
  let t := cellsP D
  let ZV := (lastOf r.H.wpl.r y.h.la).toOption.getD #[]
  let gp := elemsR 4100 5
  let blocks := y.h.d / y.S2
  let ends (e g : Array E) : KP :=
    ∑ x ∈ range (y.NI * blocks * y.xb.nl),
      valF (e.getD (x / y.xb.nl / blocks * y.Pd / y.S2 + x / y.xb.nl % blocks) zeroE) *
        valF (g.getD (x % y.xb.nl) zeroE) *
        ∑ q ∈ range (2 ^ y.ls), Blocks.eqN y.ls 0 (ptIW ZV) q *
          Blocks.ext D.lT (fun p => bS D t (x / y.xb.nl / blocks) (x % y.xb.nl)
            (x / y.xb.nl % blocks * 2 ^ y.ls + q) p) (fun j => ptIW ZV (y.ls + j))
  match r.v.tabAt "xbI@Z_V", r.v.tabAt "af@Z_V", y.T_ "xs",
    (hiTab r.H.wpl.r y.h.la (ceilLog2 y.NI + y.lPd - y.ls)).toOption with
  | some tI, some tA, some txs, some e =>
    match normsSum y r.v tI tA txs e gp with
    | some sum =>
      [true, isP r (Aff.slot 0 + sum) (0 - ends e gp),
       if r.v.g == 0 then
         match r.v.tabAt "xbI@Z_E" with
         | some tb =>
           match embSum r.v tb r.H.tkh with
           | some s => isP r ((Aff.slot 0).scale (negE oneE) + s)
               (∑ kh ∈ range blocks, valF ((eqTab r.H.tkh).getD kh zeroE) *
                 ∑ q ∈ range (2 ^ y.ls), Blocks.eqN y.ls 0 (ptIW r.H.ZE) q *
                   Blocks.ext D.lT (fun p => xS D t 0 (kh * 2 ^ y.ls + q) p)
                     (fun j => ptIW r.H.ZE (y.ls + j)) - 0)
           | none => false
         | none => false
       else (r.v.tabAt "xbI@Z_E").isNone,
       !isP r (Aff.slot 0 + sum) (0 - ends e (elemsR 4200 5)), ends e gp != 0]
    | none => []
  | _, _, _, _ => []

/- all marks, in both groups of layers -/
#guard withP false hR8 pcR8 idnLB == List.replicate 2 (List.replicate 5 true)

end OnBytes.Road
