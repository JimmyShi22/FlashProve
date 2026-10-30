-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Plan/Eight.lean: the eight tests on the entries of a key file's three plans, each
with its name, in one list. One definition with code; public data only.

The eight: the first chain's (`okFirst`, Johnson/Desc/Key/Plan/One.lean); the second chain's two
(`okFolded`, `okOmega`, Plan/Two.lean); the third chain's four (`stepsThird`, Plan/Three.lean);
and that the rounds which a description's blocks take use the three plans up.

Main names.
  `clausesAt k n₁ n₂ n₃`: the list of names and answers at a key's chains k. n₁, n₂, n₃: how many
    rounds a description's blocks take of the three chains, the seals' rounds not counted.

Limits. The three numbers are the caller's: nothing here says that they are the numbers of rounds
of any description. What each test leaves unasked stands in its own file's head. The names are
strings for a reader of a refusal: no code reads them. No theorem. Nothing on soundness.

-/
import Johnson.Desc.Key.Plan.One
import Johnson.Desc.Key.Plan.Two
import Johnson.Desc.Key.Plan.Three

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Plan

open OnBytes OnBytes.Params

/-- The eight tests at a key's chains, each with its name. The last: the first and the second plan
have one round more than the blocks take, the seal's; the third has none. -/
def clausesAt (k : KeyChains) (n₁ n₂ n₃ : Nat) : List (String × Bool) :=
  let P := sharedPub k.shared
  [("chain 1: from the lookups' own message to the batching of the pending rows the plan's \
      entries are what the shapes ask (okFirst)", okFirst k.oneTime),
   ("chain 2: the folded row's test and the rounds before it (okFolded)", okFolded P),
   ("chain 2: Omega's test and the rounds before it (okOmega)", okOmega P)] ++
  ((stepsThird k).map fun s => ("chain 3: " ++ s.1, s.2 ())) ++
  [("the steps use up the plans' rounds: chain 1's and chain 2's with a seal's round, \
      chain 3's without",
    k.oneTime.given.rounds.length == n₁ + 1 && k.shared.given.rounds.length == n₂ + 1 &&
      k.second.given.rounds.length == n₃)]

end VerifiableInference.Desc.Key.Plan
