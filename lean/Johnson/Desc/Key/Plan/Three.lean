-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Plan/Three.lean: the four tests on the plans that belong to a key file's third
chain, the field that the program calls `second` (OnBytes/Params/Chains.lean). That chain holds the
own test: the proximity test on the own group, the group of the oracle message W
(`LinShape.testOwn`, OnBytes/Params/Items.lean). Definitions with code; Bool tests with a name each;
public data only: no view and no value of the field is read.

The four, in `stepsThird`:
  one answer to a sample (any other number is refused, though the wants are written for any);
  the own group's two codes are the first stage's (as `ioppVerify` asks, OnBytes/Iop/Prox.lean);
  the third chain's plan is just the own test's entries (Johnson/Desc/Key/Plan/Test.lean: names,
    bytes, roots, answers, elements drawn, how many of them must not be 0, the range of the
    positions at every round that draws positions, the rows at every round that batches), with no
    round behind them;
  the entries of the two sendings of the FIRST chain that the own test reads, the index-mask
    message's and W's, are a round of seeds and a round of answers of these messages.

Main names.
  `wantsSend`: the two rounds of a prover's message.
  `wantsThird`: the own test's entries.
  `sendsInFirst`: where the two sendings lie in the first chain's plan.
  `stepsThird`: the four tests, each with its name; a test is evaluated when it is called.

Limits. The sending of Omega, which the own test reads too, is asked by `okOmega`
(Johnson/Desc/Key/Plan/Two.lean), not here. `sendsInFirst` takes the first and the last round named
SEND seed and asks nothing of what lies between. `wantsThird` and the fourth test reckon at the
shared chain's codes and shape and at the third chain's number of answers, also where they judge the
first chain's entries: that the three chains have the same codes and answers is not asked here. An
entry's bits of work and its number of positions are not read. No theorem. Nothing on soundness.

-/
import Johnson.Desc.Key.Where
import Johnson.Desc.Key.Plan.Test

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Plan

open OnBytes OnBytes.Params

/-- The two rounds of a prover's message: seeds, answers. -/
def wantsSend (codes : Codes) (a : Nat) (m : Array OracleNotice) : List Want :=
  [wantSeed a (treesSent codes m) (largestCube codes (m.toList.map (·.shape))),
   wantAnswer a (m.toList.filter fun n => n.shape.answers != 0).length]

/-- The own test's entries: it batches the two open rows that OnBytes/Iop/Lin.lean names (Eval) and
(Dot), and three messages' sample rows. -/
def wantsThird (k : KeyChains) : List Want :=
  let S := k.shared.lin
  let a := k.second.given.plan.samples
  wantsTest k.shared.codes a S.testOwn (2 + 3 * a) (if S.masksAhead then 0 else 1)
    S.choice.masksRide

/-- Where the two sendings lie in the first chain's plan: the first and the last round named SEND
seed. -/
def sendsInFirst (k : KeyChains) : Option (Nat × Nat) :=
  let s := roundsNamed k.oneTime.given.rounds "SEND seed"
  match s.head?, s.getLast? with
  | some i, some j => some (i, j)
  | _, _ => none

/-- **The plan's side of the third chain**, test by test. -/
def stepsThird (k : KeyChains) : List (String × (Unit → Bool)) :=
  let S := k.shared.lin
  let c := k.shared.codes
  let a := k.second.given.plan.samples
  let e₁ := k.oneTime.given.rounds
  let e₃ := k.second.given.rounds
  [("public: the own test: one answer to a sample", fun _ => a == 1),
   ("public: the own test: the first stage has the group's codes", fun _ =>
      (S.testOwn.head?.map fun s => (s.code, s.maskCode)) == some (S.w.code, S.ownMaskCode)),
   ("public: the own test: chain 3's plan is just the test's entries", fun _ =>
      okFrom (wantsThird k) e₃ 0 && e₃.length == (wantsThird k).length),
   ("public: the own test: the index-mask message's and W's sendings in chain 1's plan", fun _ =>
      match sendsInFirst k, linMessageW S with
      | some (i, j), some mW =>
        okFrom (wantsSend c a #[k.oneTime.indexMasks]) e₁ i && okFrom (wantsSend c a mW) e₁ j
      | _, _ => false)]

end VerifiableInference.Desc.Key.Plan
