-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheThreeThreads.lean: the three threads of the online part at one run, at a return
of the maker, and what is said at each.

The online part has three chains, the first, the shared and the second. A thread (Honest/Thread/
Thr.lean) is the invariant that ties the verifier's state at each border of a chain to the honest
prover's run. threadOne, threadTwo and threadThree are the values of TheFirstThread.lean at the run
that ready returned. saidOne and saidTwo say that the stand is the one walked from the run's start;
saidThree says which columns the second chain begins with. lastAtRun lays the second chain's parts
with the two earlier chains' ends as the two threads give them: what a run's ends must agree with.
-/
import Johnson.Bind.ForProver.FiveAt
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.Thread.BaseTied
import Johnson.Desc.ProofFile.Honest.Thread.DoorWalk
import Johnson.Desc.ProofFile.Honest.Thread.EndsAtHeads
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **The first chain's thread at the run.** -/
abbrev threadOne := firstThread h first R.own

/-- **The shared chain's thread at the run.** -/
abbrev threadTwo := sharedThread h reads shared R.common


/-- What is said at the first chain: the stand walked from the start that ready gives. -/
abbrev saidOne := SaidWalk (threadOne h first R) BaseNil (firstStand A.H R)

/-- What is said at the shared chain. -/
abbrev saidTwo := SaidWalk (threadTwo h reads shared R) BaseNil (sharedStand A.H R)

/-- **The second chain's parts, with the two earlier chains' ends as the two threads give them.** -/
def lastAtRun : LastThreadParts A :=
  { last with
    ends := fun k w hd =>
      ((w.x.pub, (endsBy (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length
          (threadTwo h reads shared R) (saidTwo h reads shared R) h.description.shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) k w hd).1),
        (endsBy (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length
          (threadTwo h reads shared R) (saidTwo h reads shared R) h.description.shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, A.H.key w.x⟩) k w hd).2) }

/-- **The second chain's thread at the run.** -/
abbrev threadThree := lastThread h first reads last R.own

/-- What is said at the second chain: the columns that it begins with are the two earlier chains'. -/
abbrev saidThree :=
  SaidField (threadThree h first reads last R) (BaseTied h.description (threadThree h first reads last R))

/-- **What the kinds' laws ask of the run's own input.** The threads stand at every input; these
facts hold at a run's, from the relation that ties it. -/
structure TiedAtRun {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (reads : IndexReaders W₀ IndexCommitterCoins)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (common : Common W₀ IndexCommitterCoins OnBytes.TableKey) : Prop where
  /-- the public part is a typed instance's -/
  typed : ∃ z, w.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub
  /-- where the index is in range, the key is one that the committer makes of the index and the
  coins at some seed -/
  key : A.H.inRange common.w₀ = true → Bind.ForProver.validAt (Bind.ForProver.shapeOf A.Z) A.Z
    ⟨reads.weights common.w₀, common.rc, common.key⟩

end AtFullSide.Honest
