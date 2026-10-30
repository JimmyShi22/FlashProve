-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EvAtLastParts.lean: kind K13 (the members' batching): the item "ev" of the last
chain's start, IN THE WORDS OF THE LAST THREAD's OWN MEANING (`lastParts`,
Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean): wherever the first thread's invariant
holds at its last border, that meaning's field ev holds of the last chain's witness, at the first
chain's last state. One statement with its proof; no definition.

Main name. `ev_at_lastParts`: the field ev of `(lastParts hd first L).meaning w` is `evAll`
(Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean) by unfolding; there `k13_evAll_at_door`
(EvAllAtDoor.lean of this folder) is the statement.

Limits. At `lastParts` alone: at another value of the last thread's parts the field ev may be
another sentence. As in EvAllAtDoor.lean: conditional on the head at the return and on the first
thread's invariant at its last border, which holds (Eval)'s sentence among its clauses: the
statement moves that sentence to the last chain's witness and pays no debt on it; that the invariant
holds there at any run is not shown here.

NOT IN FRONT OF A LAW OVER COINS: the statement speaks of one run's values. Where the first chain's
last state holds no linear claim, or the request's own group is missing, `evAll` holds for nothing's
sake (EvAtLastStart.lean says where); under the invariant that arm is not met. z and y are read by
nothing.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.EvAllAtDoor
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open VerifiableInference.Desc (Strs)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastLetters firstThread
  lastWitness lastParts)
open ProofFile.Honest.K14 (evAll)

/-- **The item "ev" at the last chain's start, in the last thread's own meaning**: of the last
chain's witness at the thread's own input w and at the challenges heard on the first chain, then
h₂, then ds. -/
theorem ev_at_lastParts {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins A.B} {e₁ : TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    (u₁ : Thr (firstThread hd first w) hd.description.first.blocksInOrder.length k e₁ m₁ E₁)
    (h₂ ds : List Fmt.Drawn) (z : ProofFile.InstPub) (y : Strs) :
    ((lastParts hd first L).meaning w).ev (z, e₁) y
      (lastWitness hd first reads k w (m₁.st.heard ++ h₂ ++ ds)) := by
  show evAll (P5J.At.arr A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, e₁) y
    (lastWitness hd first reads k w (m₁.st.heard ++ h₂ ++ ds))
  exact k13_evAll_at_door hd first reads w u₁ h₂ ds z y

end AtFullSide.K13

#print axioms AtFullSide.K13.ev_at_lastParts
