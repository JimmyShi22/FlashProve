-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pend/WeightsB.lean: A TEST WITH CODE ON THE FIRST CHAIN'S RECORD: every weight
vector of every row on the table passes `Tensor.ok`. One definition, five small statements. It
imports Johnson/Desc/First/State.lean alone.

Why. The law on the row (Dot) of the last chain spends `Tensor.ok` of the one pending row's weights;
no block asks it. It is to ride along the first chain as an invariant (the named item
"K13.weightsOk": Johnson/Desc/First/FillWeights.lean). The test stands here by itself
so that it can be run at a chain's borders without any law's cone.

Main names (namespace `VerifiableInference.Desc.First`).
  **`weightsB s`** := `s.rows.all fun r => r.g.all (·.ok)`. `S.rows` (State.lean): the pile in front
    of the batching; behind it the one row, read off the claim.
  `weightsB_same`: a step that leaves `S.rows` leaves the test. `weightsB_firstRecord`,
    **`weightsB_start`**, `weightsB_blank`: the first record, the bare start at every state of the
    calls with a request's words laid, and the marked blank pass: their piles are empty.
    `weightsB_can_fail`: a record that fails it (its one vector fails two of `Tensor.ok`'s four
    conjuncts at once: it shows that the test bites, not which conjunct).

Limits. TRUE FOR NOTHING WHERE NO ROW LIES: at every border in front of the first pending row the
yes is idle. `S.rows` reads two fields, the pile and `here` (the claim): "leaves the rows" is a word
on both. Who keeps it: Johnson/Desc/Last/ShapeWeights.lean, as far as that goes. Nothing on what the
weights' entries are. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

/-- **Every weight vector of every row on the table passes `Tensor.ok`.** -/
def weightsB (s : S) : Bool := s.rows.all fun r => r.g.all (·.ok)

/-- A step that leaves the rows on the table leaves the test. -/
theorem weightsB_same {s s' : S} (h : s'.rows = s.rows) : weightsB s' = weightsB s := by
  unfold weightsB
  rw [h]

/-- The first record passes: no row lies on its pile. -/
theorem weightsB_firstRecord (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) : weightsB (S.firstRecord codes shape layout) = true := rfl

/-- **The bare start passes, at every state of the calls and all words of a request**: the term at
which the first table's start asks a public item (`IsStart`,
Johnson/Desc/First/BordersStart.lean). -/
theorem weightsB_start (codes : Codes) (c : ChainCheck) (req : Array UInt32) :
    weightsB ((S.start codes c).withReq req) = true := rfl

/-- So does the marked blank. -/
theorem weightsB_blank : weightsB S.blank = true := rfl

/-- **It can fail**: the first record with one row on its pile whose one vector names a written-out
variable that it does not have. -/
theorem weightsB_can_fail (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    weightsB { S.firstRecord codes shape layout with
      out := { indexMasks := noId, reply := none
               pending := [{ g := [{ denseVars := [0] }], psi := [], masks := [],
                             target := zeroE }] } } = false := rfl

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.weightsB_same
#print axioms VerifiableInference.Desc.First.weightsB_firstRecord
#print axioms VerifiableInference.Desc.First.weightsB_start
#print axioms VerifiableInference.Desc.First.weightsB_blank
#print axioms VerifiableInference.Desc.First.weightsB_can_fail
