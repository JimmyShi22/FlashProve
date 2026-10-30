-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GenStop.lean: one lemma on lists.

  `length_zip_slots`   The instances of a batch b, zipped with a list that has one proof for each
                       pair of b (`Slots Pf b`), are a list of the length of b.

Notation: `X`, `W`, `Pf` : Type: the types of the instances, the witnesses and the proofs (`Batch`,
`Arg`, ZKCP/Gen.lean).

Limits: this file does not define a prover that withholds a proof or a verifier that rejects when a
public check fails, and proves nothing on such schemes.
-/
import Compile.Spec
import Compile.Batch.SpecGlue
import Compile.Step1_defc_Gen

noncomputable section

namespace Compile.GenStop
open ZKCP.Gen Rom Prob Compile.GlueB
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}


theorem length_zip_slots {b : List (X × W)} (πs : Slots Pf b) :
    ((b.map Prod.fst).zip πs.val).length = b.length := by
  rw [List.length_zip, List.length_map, πs.property, Nat.min_self]

end Compile.GenStop
