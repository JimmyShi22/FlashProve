-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/TabOf.lean: TWO SMALL PIECES FOR THE SIX TABLES ON WORDS
(Johnson/Prover/Link/CarriedTabs.lean [not in this library]). Definitions alone, with code; no
theorem.

  tabOfFn   a table out of a finite function of a row's number and a place: an array, the row's
            number in the low bits of the index. General in the entries' type. Every entry is the
            function's value at indices that are in range by their types: no default
  pointW    the point of a stage's fold, on words: the first element of what each of the k rounds
            behind round o sampled

Limits. pointW reads "the first element, or three words 0 where a round sampled none", as the
verifier's own reading does (drawnOf, Johnson/Prover/Link/FormFold.lean). Nothing here tests that
each of these k rounds sampled one element. (Of a run's rounds FitFrom,
Johnson/Prover/Link/BodyFit.lean, says that each sampled as many elements as its declared round's
entry says; what that number is, is the plan's.) No law on a random value is stated over pointW
here. Such a law is to take "each of these k rounds sampled one element" as a named public premise,
or be proved at the point 0 too.
Nothing is proved. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Base
import Fmt.Rules8X

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes

/-- **A table out of a finite function**: entry r + 2 ^ n * q is f r q. -/
def tabOfFn {α : Type} (n l : Nat) (f : Fin (2 ^ n) → Fin l → α) : Array α :=
  Array.ofFn (n := l * 2 ^ n) fun i =>
    f ⟨i.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩
      ⟨i.val / 2 ^ n, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 i.isLt⟩

/-- **The fold's point on words.** D: what each round sampled, by the round's number. o: the number
of the fold's first round. k: the number of its further rounds. A coordinate whose round's list of
elements is empty is (0, 0, 0). Nothing here tests that a list is not empty. -/
def pointW (D : Nat → Fmt.Drawn) (o k : Nat) : List E :=
  (List.range k).map fun n => E.ofTriple ((D (o + 1 + n)).elems.headD (0, 0, 0))

end Johnson.Prover.Link
