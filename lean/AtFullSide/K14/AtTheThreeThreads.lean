-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtTheThreeThreads.lean: kind K14: three facts on where the shared and the second
chain meet, AT THE THREE CHAINS' THREADS AT A RUN as AtFullSide/Honest/TheThreeThreads.lean names
them (threadOne, threadTwo, threadThree; saidOne, saidTwo; lastAtRun). Statements: calls alone. No
definition.

  shared_door_at_threadTwo
      the five tests that the second chain's form at its first border makes on the shared chain's
      end say yes, from a stand of threadTwo at its last border, and nothing else:
      shared_door_at_term (AtFullSide/K14/SharedDoorAtTerm.lean) at the run's shared input
  shared_door_saidTwo
      the same from a stand with the sentence saidTwo beside it (ThrS): the form in which a door
      between chains hands a stand on
  door_rides_at_run
      **the field rides of lastParts at border 0, at the record that the second chain's start
      returns, from stands of threadOne and threadTwo at their last borders**, where the letters'
      riders are lastRiders: rides_zero_at_terms (AtFullSide/K14/RidesAtTheDoor.lean) at the run's
      two inputs
  ends_at_lastAtRun
      the two states that threadThree's own parameter ends returns are the two that the library's
      term endsBy (Honest/Thread/OneState.lean) returns at threadOne, saidOne, threadTwo, saidTwo,
      these chains' last borders and the two maps of the input: by unfolding. These are the letters
      at which the clause TiedToEnds (Honest/K14/TiedToEnds.lean) gives stands at endsBy's states
      (ties_at_endsBy)

By what: the two theorems of AtFullSide/K14/SharedDoorAtTerm.lean; the one of
AtFullSide/K14/RidesAtTheDoor.lean; the text of lastAtRun.

A stand of a thread at a border: its invariant Thr (Honest/Thread/Thr.lean) holds there, at some
state of the verifier, some state of the prover's run and some available tables.

Limits.
  * h : HeadAtReturn is a hypothesis (Honest/K14/WordsAtLastWitness.lean says what it holds).
  * NOTHING HERE SHOWS THAT ANY THREAD STANDS AT ANY RUN.
  * ends_at_lastAtRun says nothing of what endsBy returns: it is chosen, and need not be this run's
    own two ends (the head of Honest/K14/TiedToEnds.lean, on endsBy). The clause TiedToEnds is no
    part of saidThree as that file writes it.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.K14.SharedDoorAtTerm
import AtFullSide.K14.RidesAtTheDoor
import AtFullSide.Honest.TheThreeThreads
import Johnson.Desc.ProofFile.Honest.K14.TiedToEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.Last (sharedDoorB)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread
open AtFullSide.Honest (threadOne threadTwo threadThree saidOne saidTwo lastAtRun)
open Desc.K14 (St)

variable {W₀ Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **From a stand of the shared chain's thread at a run, at its last border: the five tests of the
second chain's form on that chain's end say yes**, of whatever Desc.K14.ended returns at that state.
-/
theorem shared_door_at_threadTwo {k : Coins A.B} {e₂ : St}
    {m₂ : Mid (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit} {E₂ : Env}
    (u : Thr (threadTwo h reads shared R) h.description.shared.blocksInOrder.length k e₂ m₂ E₂) :
    ∀ e, Desc.K14.ended e₂ = some e →
      sharedDoorB (ToldDesc.p14At A.Z) (sharedOfEnd e) = true :=
  shared_door_at_term h reads shared R.common u

/-- The same from a stand with saidTwo beside it. -/
theorem shared_door_saidTwo :
    ∀ k e₂ m₂ E₂, ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∀ e, Desc.K14.ended e₂ = some e →
        sharedDoorB (ToldDesc.p14At A.Z) (sharedOfEnd e) = true :=
  shared_door_saidS h reads shared R.common (saidTwo h reads shared R)

/-- **The field rides of lastParts at border 0, where the second chain is entered at a run.** hrid,
late: L's riders are lastRiders at clauses that begin at border 2 or later. -/
theorem door_rides_at_run (L : LastLetters A)
    {later : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) VerifiableInference.Desc.Third.S₃)}
    (hrid : L.riders = lastRiders h.places later) (late : ∀ c ∈ later, 2 ≤ c.lo) (x : ProofFile.Inst)
    (k : Coins A.B) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ → (lastParts h first L).rides 0 R.own s₃ :=
  fun _ _ _ _ _ _ s₃ u₁ u₂ hs =>
    rides_zero_at_terms h first reads shared L R.own R.common hrid late u₁.1
      (saidTwo h reads shared R) u₂ x.pub s₃ hs

variable [Inhabited P5J.TS] [Inhabited St]

/-- **The two states that the second chain's thread at a run names as the earlier chains' last
states are the library's chosen ones**, at every coins, input and list of challenges. -/
theorem ends_at_lastAtRun (k : Coins A.B) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hd : List Fmt.Drawn) :
    ((lastAtRun h first reads shared last R).ends k w hd).1.2 =
      (endsBy (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length
        (threadTwo h reads shared R) (saidTwo h reads shared R) h.description.shared.blocksInOrder.length id
        (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k w hd).1 ∧
    ((lastAtRun h first reads shared last R).ends k w hd).2 =
      (endsBy (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length
        (threadTwo h reads shared R) (saidTwo h reads shared R) h.description.shared.blocksInOrder.length id
        (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k w hd).2 :=
  ⟨rfl, rfl⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.shared_door_at_threadTwo
#print axioms AtFullSide.K14.shared_door_saidTwo
#print axioms AtFullSide.K14.door_rides_at_run
#print axioms AtFullSide.K14.ends_at_lastAtRun
