-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SerS.lean: the serialisers, as data, of a round `wordsRound`.

The compiled scheme's typed queries are encoded as strings (Compile/Batch/Ser.lean; the tools:
Iop/Ser.lean). For that it needs, for every round of a protocol, a serialiser of (position, symbol)
and one of the plain part (`SerR`, Iop/SerS.lean). `wordsSer` gives the two for a round `wordsRound`
(Blocks/Basic.lean): a round whose prover message consists of the oracles `w a : Fin (n a) → Sy a`,
a : A, and of a plain part. Every element is written as its number in Mathlib's FinEnum, in fixed
width. No serialiser is obtained from a statement of existence (Lean's list of axioms does not show
this: the head of Iop/Ser.lean; it is seen by reading the bodies of `wordsSer` and of
`Ser.ofFinEnum`).
-/
import Blocks.Numbering
import Iop.SerS

set_option autoImplicit false

namespace Blocks
open Iop

/-! ## Rounds -/

/-- a round `wordsRound` -/
def wordsSer (A : Type) [FinEnum A] (n : A → ℕ) (Sy : A → Type) [∀ a, FinEnum (Sy a)]
    (Plain Chal : Type) [FinEnum Plain] [Fintype Chal] [Nonempty Chal]
    (dSy : ∀ a, Sy a) (dPlain : Plain) :
    SerR (wordsRound A n Sy Plain Chal dSy dPlain) :=
  (Ser.ofFinEnum (Σ p : (Σ a, Fin (n a)), Sy p.1), Ser.ofFinEnum Plain)

end Blocks
