-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/U3RowsLaws.lean

Where "layersAt" and "headAt" of Johnson/HonestTrace/U3Rows.lean return a vector, it is the vector
of which the laws of the reads speak.

Main theorems:
* "layersAt_eq": if layersAt mats y fo pt laid n = .ok v: v cell i = u3Layers mats y fo pt laid cell
  i (Johnson/HonestTrace/ReadsLayers.lean), for all cell and i.
* "headAt_eq": if headAt h L hp cov x = .ok v: v cell i = u3Head h L hp cov x cell i
  (Johnson/HonestTrace/ReadsHead.lean), for all cell and i.

Limits. Two unfoldings. Nothing on attention's vector. Nothing on the letters fo, pt, x: that the
makers of U3Rows.lean lay there what a run of the verifier hears is not shown here. Nothing on rows,
places or addresses. Nothing on any property of the protocol.

-/
import Johnson.HonestTrace.U3Rows
import Johnson.HonestTrace.ReadsLayers
import Johnson.HonestTrace.ReadsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay TableAsk)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)

/-- Where "layersAt" returns a vector, its entries are "u3Layers". -/
theorem layersAt_eq {mats : Array TMat} {y : Lay} {fo : Forest.Heard}
    {pt : List (String × Array E)} {laid : List (TableAsk × List (Nat × Nat))} {n : Nat}
    {v : CellsAt → Nat → E} (h : layersAt mats y fo pt laid n = .ok v) (cell : CellsAt)
    (i : Nat) : v cell i = u3Layers mats y fo pt laid cell i := by
  unfold layersAt at h
  split at h
  · cases h
  · rename_i funs hf
    split at h
    · cases h
    · cases h
      unfold u3Layers
      rw [layerParts_some hf]

/-- Where "headAt" returns a vector, its entries are "u3Head". -/
theorem headAt_eq {h : Head.Shape} {L : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {x : Head.Heard} {v : CellsAt → Nat → E} (e : headAt h L hp cov x = .ok v) (cell : CellsAt)
    (i : Nat) : v cell i = u3Head h L hp cov x cell i := by
  unfold headAt at e
  split at e
  · cases e
  · rename_i t ht
    split at e
    · cases e
    · cases e
      unfold u3Head
      rw [headParts_ok ht]

end OnBytes.HonestTrace.U3

#print axioms OnBytes.HonestTrace.U3.layersAt_eq
#print axioms OnBytes.HonestTrace.U3.headAt_eq
