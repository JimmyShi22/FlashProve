-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/TableRows.lean: from a lookup's claims on its parts' keys to rows on the committed
matrix. One definition, computable; nothing is proved here.

It serves the block without a round that stands in front of the batching of these rows
(`layPile`, Johnson/Desc/Key/One.lean). It is written after the verifier program's `Wf.pendingOf`
(OnBytes/Iop/Wf.lean), without that routine's monad; the program's pure functions are called as
they stand: `Wf.eqPlaces`, `Wf.sumOfForm`, `Wf.coveredSum`, `Wf.pendingRow`, `zipT`.

Limits. That it returns what `Wf.pendingOf` returns is not proved here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Key.OneTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes
open OnBytes.Params (WfLookup)

/-- The rows on the table of one lookup, from the claims on its parts' keys, with the four
conditions that the program asks: there is a claim for each part; a claim's point has one coordinate
for each bit of a key's number; its weights have no written-out factor; its weights add up to the
sum of the equality vector over the places that the part's runs cover. -/
def tableRowsOf (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys) : Option (List TensorRow) :=
  if l.parts.length == keys.length then
    (zipT l.parts keys).mapM fun x =>
      let e := Wf.eqPlaces m x.2.point
      if x.2.point.length == m.kCol + x.1.logPlaces &&
          x.2.weights.tensors.all (·.denseVars.isEmpty) &&
          Wf.sumOfForm x.2.weights == Wf.coveredSum x.1 e then
        some (Wf.pendingRow m l x.1 x.2 e)
      else none
  else none

end VerifiableInference.Desc.Key
