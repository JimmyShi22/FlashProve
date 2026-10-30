-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/LayoutOkPub.lean: WHERE THE PLAIN ROAD's PUBLIC PART IS MADE, THE REQUEST's LAYOUT
HAS PASSED THE PROGRAMS' OWN TEST reqLayoutOk: at every o; no scope. The first state is made by
S.startP, which asks S.startOk, whose last clause is that test (Johnson/Desc/First/State.lean).

OBJECT: ProofFile.pureRoad.pub's value. USER: whoever holds a law under
reqLayoutOk codes shape layout = true at the description's own letters (Meaning.laidAt_of_layout,
Meaning.laidThere_of_named: Johnson/Goal/Meaning/LaidCovered.lean). LETTERS: o and the three files:
free. No soundness.
-/
import Johnson.IMR.RecRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open ProofFile (Pub)

theorem pub_layoutOk {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) :
    reqLayoutOk Z.first.codes Z.first.shape Z.first.layout = true := by
  have hs := pub_start h
  unfold S.startP at hs
  split at hs
  · rename_i hk
    unfold S.startOk at hk
    simp only [Bool.and_eq_true] at hk
    exact hk.2.2
  · cases hs

#print axioms pub_layoutOk

end Meaning.K2
