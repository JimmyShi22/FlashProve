-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Door/Door.lean: DEFINITIONS WITH CODE; NO THEOREM: two tests on a batching draw's
round, for a kind that closes such a round through the plain functions
(OnBytes/K/Kc/Door.lean: flatBatch).
A round as these functions see it (FlatRound) has three words of the plan's entry: its name, its
draws other than 0, its rows. The closeAs of the program `verify-on-bytes`
(OnBytes/Model/Rounds.lean) asks more of the entry: its kind; just one element; no position; no
matrix entry: batchEntryB. And the maker of a tape is laxer than that verifier's channel at the
round itself (an item that is no field element; positions or matrix entries drawn): batchRoundB.
Kind K9's own text (Johnson/Desc/First/Batch/Text.lean: K9.draw) asks the same clauses under names
of its own and does not import this file.

What is not claimed. That a function here is `verify-on-bytes`'s routine: it has been held against
it by reading alone. Nothing on soundness, on an honest prover or on hiding.
The two functions are cut, to the token, out of a longer working file, which has been compiled and
has run under the merge's block in a harness.

-/
import OnBytes.K.Kc.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Door
open OnBytes OnBytes.Model

/-- What the program asks of the batching draw's entry beside its name, its draws other than 0 and
its rows. -/
def batchEntryB (e : Fmt.Entry) : Bool :=
  Params.kindOf e.name == some .elems &&
  e.drawE == 1 && e.trits == 0 && e.poss == 0

/-- What the program's channel asks of the batching draw's round on a view, and the maker of
a tape (OnBytes/K/Kc/Laws.lean: flatOf, tape) does not: NO ITEM OF ANY KIND is left in the round
(the tape keeps the leading field elements alone), and the round draws as many positions and matrix
entries as the entry says (the tape keeps the elements drawn alone). r: the round with the items not
yet taken. -/
def batchRoundB (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  r.vals.isEmpty &&
  r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits

end VerifiableInference.Desc.First.Door
