-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/LaidAtFull.lean: at the full size the host's count of padding places at a layers'
link is the written list of sixteen numbers. A joining, and one small closed fact by Lean's kernel.

  `fitB y fo`: with code: the trees of each call lie among the lookup's trees.
  `fit_W`: [Lean's kernel] the test accepts at the layers' layout at the full size. It reads the
    number of calls and, of the lookup's shape, two short lists (first, iota) and the number of
    trees. `fit_no`: a negative test: the makers return, and with one tree fewer in the lookup the
    test rejects.
  **`laid_of_y`**: for every value P of the layers' public data (Layer.Pub) whose layout is the
    full-size layout yFull (Johnson/AtFull/Public/Values.lean): laidLayers P = some (pubW 0 false).
How. The host's count is the layout's own (laidLayers_eq_pub, Johnson/AtFull/K3X/LaidLayers.lean: a
general law); the layout's own count is the written list (counts_yFull,
Johnson/AtFull/K3X/CountsAtFull.lean: the library's closed form). No column is walked by the kernel.

Limits. The full size, at the stored free numbers alone. Both counts are made next to the key forms,
from the lists of columns: a fault inside a form or in a list is not seen by either. Nothing on
soundness.

-/
import Johnson.AtFull.K3X.LaidLayers
import Johnson.AtFull.K3X.CountsAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model
open Johnson.AtFull.Lots.K3 (pubW)
open OnBytes.Road.K4.Trial.Values (yBase foW yFull hW layout_W withFo withFo_eq)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- The trees of each call lie among the lookup's trees. -/
def fitB (y : Layer.Lay) (fo : Forest.Shape) : Bool :=
  (List.range y.calls.size).all fun q =>
    decide (fo.first.getD q 0 + 2 ^ fo.iota.getD q 0 ≤ fo.NT)

/-- **By the kernel.** -/
theorem fit_W : withFo fitB = true := by decide +kernel

/-- A negative test: both makers return, and with one tree fewer the test rejects. -/
theorem fit_no : withFo (fun y fo => !fitB y { fo with NT := fo.NT - 1 }) = true := by
  decide +kernel

/-- **The host's count at a layers' link, at the full size.** -/
theorem laid_of_y {P : Layer.Pub} (hy : P.y = yFull) : laidLayers P = some (pubW 0 false) := by
  have S : OnBytes.Road.Switches hW := OnBytes.Road.Alg.switches_of_B switches_W
  have F : fitB yBase foW = true := (withFo_eq fitB).symm.trans fit_W
  rw [laidLayers_eq_pub (h := hW) (pc := VerifierAndGoals.Lines.callsRef) (by rw [hy]; exact layout_W) S
    (fun q hq => by
      rw [hy] at hq ⊢
      exact of_decide_eq_true (List.all_eq_true.1 F q (List.mem_range.2 hq))),
    hy, counts_yFull]

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.fit_W
#print axioms Johnson.AtFull.K3X.fit_no
#print axioms Johnson.AtFull.K3X.laid_of_y
