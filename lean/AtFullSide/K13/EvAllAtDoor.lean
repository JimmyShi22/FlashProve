-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EvAllAtDoor.lean: kind K13 (the members' batching): the meaning `evAll` of the last
chain's item "ev" (Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean) in the form in which the
start of the last chain's thread asks it where that thread's meaning lays `evAll` for the item (at
`lastParts`, by unfolding: EvAtLastParts.lean of this folder): at the first thread's last border
written as the length of the description's first chain, at the thread's own input, and at the
challenges heard on the first chain, then those heard on the shared chain, then any continuation.
One statement with its proof: a corollary of `k13_evAll_at_lastWitness` (EvAllAtLastWitness.lean of
this folder); no definition.

Limits. As there: conditional on the head at the return and on the first thread's invariant at its
last border, which holds (Eval)'s sentence among its clauses; that it holds there at any run is not
shown here. h₂ is any list of challenges: nothing is asked of the shared chain.

NOT IN FRONT OF A LAW OVER COINS: the statement speaks of one run's values. Where the first chain's
last state holds no linear claim, or the request's own group is missing, `evAll` holds for nothing's
sake (EvAtLastStart.lean says where); under the invariant that arm is not met. z and y are read by
nothing.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.EvAllAtLastWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open VerifiableInference.Desc (Strs)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders firstThread lastWitness)
open ProofFile.Honest.K14 (evAll)

/-- **`evAll` at the last chain's start**: of the last chain's witness at the thread's own input w
and at the challenges heard on the first chain, then h₂, then ds. -/
theorem k13_evAll_at_door {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins A.B} {e₁ : TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    (u₁ : Thr (firstThread hd first w) hd.description.first.blocksInOrder.length k e₁ m₁ E₁)
    (h₂ ds : List Fmt.Drawn) (z : ProofFile.InstPub) (y : Strs) :
    evAll (P5J.At.arr A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, e₁) y
      (lastWitness hd first reads k w (m₁.st.heard ++ h₂ ++ ds)) := by
  have e : hd.description.first.blocksInOrder.length = 358 := len358 hd.head
  rw [e] at u₁
  have hw : m₁.st.input = w := by
    have t := u₁
    unfold Thr at t
    exact t.2.2.2.2.2.2.1
  have key := k13_evAll_at_lastWitness hd first reads w u₁ (h₂ ++ ds) z y
  rw [hw, ← List.append_assoc] at key
  exact key

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_evAll_at_door
