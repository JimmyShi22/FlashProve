-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/FileMade.lean: THE NAMED TEST "made" ON A KEY FILE's SOURCE (`madeAgainOk`,
Johnson/Desc/Key/Source.lean) AS A LAW: the declared rounds and the tenants as told are what is made
anew of the three chains as read. General: no written value, nothing asked of Lean's kernel.

Why it is a law. `madeAgain k` makes the sendings of k alone (`sendsOfKey`) and then calls `fileOf`
and `toldOfPlans`. The source's own declared rounds and tenants (`declKOf m`,
Johnson/G/RoundsOfPlan.lean; `toldOfMade m`) are the same two calls, at the sized shape and at
m.key. So the test accepts where the shape as read is the sized one and `sendsOfKey` returns m.key.

  `sendsOfKey_of`: `sendsOfKey k` unfolded: where W's sending and the shared chain's list are made
    and the three calls of `sendsOfChain` return, it returns the three.
  `told_self`: the test `==` finds three lists of trees equal to themselves.
  **`made_ok`**: where `sourceOf m` returns X, the shape as read is the sized one and `sendsOfKey`
    returns m.key: `madeAgainOk X.Y = true`.

WHAT IT COSTS. Nothing more than r1, and nothing less: the two returns inside `sourceOf m = .ok X`
(of `declKOf m` and of `toldOfMade m`) are used as they stand. The routines that Lean's kernel does
not evaluate (sorting, splitting a label, reading a number off it) stand inside these two calls:
whoever shows r1 meets them; this file does not.

Limits. Every return is a premise. That `sendsOfKey` returns m.key is a premise here: it is meant to
follow from what `Johnson.G.sendsFrom` returns, by another file. Nothing on what the sendings are.
Nothing on soundness.
-/
import Johnson.Desc.Key.Desc
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open Johnson.G (Listed ChainSends)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (sendsOfChain sendsOfKey madeAgain madeAgainOk sourceOf Source
  toldOfMade)

/-- **`sendsOfKey`, unfolded into its three calls.** -/
theorem sendsOfKey_of {k : KeyChains} {w : Listed} {sh : List Listed} {k0 k1 k2 : ChainSends}
    (hw : Johnson.G.wSend k.oneTime.lin = .ok w)
    (hs : Johnson.G.linSharedSends k.oneTime.lin k.oneTime.given.plan.samples = .ok sh)
    (c0 : sendsOfChain "key" 0 k.oneTime.codes
      ([⟨"the index-mask message", [k.oneTime.indexMasks]⟩, ⟨"the multiplicities",
          (Wf.messageOf k.oneTime.ranges).toList⟩] ++
        Johnson.G.ioppSends "the ranges' test" k.oneTime.given.plan.samples
          k.oneTime.ranges.choice.masksRide 1 k.oneTime.ranges.stages ++ [w])
      k.oneTime.given.plan.entries = .ok k0)
    (c1 : sendsOfChain "key" 1 k.oneTime.codes sh k.shared.given.plan.entries = .ok k1)
    (c2 : sendsOfChain "key" 2 k.oneTime.codes
      (Johnson.G.ioppSends "the own test" k.oneTime.given.plan.samples
        k.oneTime.lin.choice.masksRide 1 k.oneTime.lin.testOwn)
      k.second.given.plan.entries = .ok k2) : sendsOfKey k = .ok (k0, k1, k2) := by
  unfold sendsOfKey
  dsimp only
  rw [hw, hs]
  dsimp only [bind, Except.bind]
  rw [c0, c1, c2]
  rfl

/-- The test `==` finds three lists of trees equal to themselves. -/
theorem told_self (t : List ProofFile.Root × List ProofFile.Root × List ProofFile.Root) : (t == t) = true :=
  beq_self_eq_true t

/-- **THE CLAUSE "made".** -/
theorem made_ok {m : Made} {X : Source} (r1 : sourceOf m = .ok X)
    (i5 : m.p.chains.key.oneTime.lin = m.p.chains.made.sized.key.once.shape)
    (hs : sendsOfKey m.p.chains.key = .ok m.key) : madeAgainOk X.Y = true := by
  unfold sourceOf at r1
  obtain ⟨D, hD, r1⟩ := exc_bind r1
  dsimp only at r1
  obtain ⟨T, hT, r1⟩ := exc_bind r1
  obtain rfl := Except.ok.inj r1
  have hD' : Johnson.G.OfPlan.fileOf "key file" m.p.chains.key.oneTime.lin
      m.p.chains.key.oneTime.given.plan m.p.chains.key.shared.given.plan
      m.p.chains.key.second.given.plan m.key.1 m.key.2.1 m.key.2.2
      (fun ts _ => Johnson.G.OfPlan.onceOpens ts) (fun t => t.tag == .indexMask) = .ok D := by
    rw [i5]
    exact hD
  have hT' : VerifiableInference.Desc.Key.toldOfPlans m.p.chains.key.oneTime.lin
      m.p.chains.key.oneTime.given.plan m.p.chains.key.shared.given.plan
      m.p.chains.key.second.given.plan m.key = .ok T := by
    rw [i5]
    exact hT
  have e : madeAgain m.p.chains.key = .ok (D, T) := by
    unfold madeAgain
    rw [hs]
    dsimp only [bind, Except.bind]
    rw [hD', hT']
    rfl
  unfold madeAgainOk
  dsimp only
  rw [e]
  dsimp only
  rw [told_self, decide_eq_true rfl]
  rfl

end Johnson.KB9

#print axioms Johnson.KB9.sendsOfKey_of
#print axioms Johnson.KB9.told_self
#print axioms Johnson.KB9.made_ok
