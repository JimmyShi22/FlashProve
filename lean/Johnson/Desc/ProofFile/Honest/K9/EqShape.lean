-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqShape.lean: ALL THAT IS LEFT OF WHAT THE NAMED TEST `oneV` OF THE SUB-PROTOCOL "THE ONE EQUATION"
(Johnson/AtFull/Shape/ValsBool.lean) ASKS OF THE PUBLIC DATA, AS ONE Bool ON THE SHAPE OF THE FIRST CHAIN's STATE; and which components of the shape it
reads.

  **`oneShape a`**      `oneSizes a` (Honest/K9/EqSizes.lean: the four tests on sizes, but for one clause) and `oneFirsts a`
                      (Honest/K9/EqFormFits.lean: what the shape holds of that clause) and `padsS a` (Honest/K9/PadShape.lean: no block of an
                      array covers a place of a pad; the mask message's pad lies behind the mask entries in use)
  **`oneShape_reads`**  it reads three components of the shape alone: the link's context, the ledger, and the core (statement, book, count of
                      roots): two shapes that agree in these get the same answer

It reads no field element: the shape holds none. Limits. That it accepts at any shape is not proved here. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqFormFits
import Johnson.Desc.ProofFile.Honest.K9.PadShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc.First.Shape (ChainSh)

/-- **The one Bool on the chain's shape.** -/
def oneShape (a : ChainSh) : Bool := oneSizes a && oneFirsts a && padsS a

/-- **It reads the link's context, the ledger and the core alone.** -/
theorem oneShape_reads {a a' : ChainSh} (h1 : a.link = a'.link) (h2 : a.led = a'.led) (h3 : a.core = a'.core) :
    oneShape a = oneShape a' := by
  unfold oneShape oneSizes oneFirsts padsS
  rw [h1, h2, h3]

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.oneShape_reads
