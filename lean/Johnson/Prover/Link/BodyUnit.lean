-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyUnit.lean: A DRAWN FACTOR THAT IS NOT (0, 0, 0) AS RAW WORDS, AND WHOSE
WORDS ARE BELOW THE PRIME, IS A UNIT OF THE FIELD. One statement and its proof, by laws of the
library: K1.okE_ofTriple (Johnson/Desc/K1/Law/OkView.lean) · Slice.isZeroE_iff
(OnBytes/Slice/ProgField.lean) · unitOf_val (OnBytes/Slice/CorePeel.lean). It pays the premise β.val
= readE D.beta of the switch's laws at β := unitOf (readE ...), as ans_at
(Johnson/Prover/Link/BodyStepAt.lean) writes it.

Not shown here. That a draw is such. Nothing on a decision, on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ViewWords
import Johnson.Desc.K1.Law.OkView
import Johnson.Desc.Own.Rows
import OnBytes.Slice.CorePeel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice
open VerifiableInference.Desc

theorem readE_ne_zero_of (x : Fmt.Ext) (h1 : ltE x = true)
    (h2 : Own.allZero (E.ofTriple x) = false) : readE (E.ofTriple x) ≠ 0 := fun h => by
  have hz : isZeroE (E.ofTriple x) = true := (isZeroE_iff _ (K1.okE_ofTriple x h1)).2 h
  have hz' : Own.allZero (E.ofTriple x) = true := hz
  rw [h2] at hz'
  cases hz'

theorem unit_of_factor (x : Fmt.Ext) (h1 : ltE x = true)
    (h2 : Own.allZero (E.ofTriple x) = false) :
    (unitOf (readE (E.ofTriple x))).val = readE (E.ofTriple x) :=
  unitOf_val (readE_ne_zero_of x h1 h2)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.readE_ne_zero_of
#print axioms Johnson.Prover.Link.unit_of_factor
