-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/ClaimTrue.lean: one definition, in a file of its own so that a file which
wants it need import no law of this folder.

  `ClaimTrue`    whatever claim the verifier's state inside a proximity test passes is true at the
                 prover's state's message, read with the layout that is passed with it

Limits. A definition alone. Where the verifier's state passes no claim it holds for nothing. Of the
claim's row it reads the form on the main table, the vector on the mask table and the target: NOT
the separate forms on kept members; at a row that has such forms it says less than the row does.
Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Join
import Johnson.Prover.Link.BodyState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS μOf)

/-- **Whatever claim the verifier's state passes is true at the prover's state.** -/
def ClaimTrue (s : Sg) (t : T12) (P : PS) : Prop :=
  ∀ (row : GroupRow) (L : GroupLayout), t.pass = .claim row L →
    (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmGk s L.k L.h row) (μOf s P)

end ProofFile.Honest.K12
