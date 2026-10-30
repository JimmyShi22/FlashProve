-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/RidesAtTheDoor.lean: WHERE A PROOF FILE's LAST CHAIN IS ENTERED: THE WHOLE FIELD
rides OF lastParts (Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean) AT BORDER 0, at the
record that the chain's start returns, where the letters' riders are the value lastRiders: FROM THE
INVARIANTS OF THE TERMS firstThread AND sharedThread (Honest/Thread/TheFirstThread.lean) AT THEIR
LAST BORDERS. One theorem. At border 0 two clauses speak, and both are the linear claim's: doorRider
(second_door_at_terms, AtFullSide/K14/DoorAtTerms.lean) and tiedAheadRider (tied_ahead_at_terms,
AtFullSide/K14/TiedAheadAtTerms.lean); tiedRider begins at border 1 and the later clauses at border
2 or later.

It stands under the library's hypothesis at the full size (P5J.AtMgA), at the format's second hash
function:
that is the field head of h. The limits of the two files named bind here.

The two premises on the letter. hrid: the letters' riders are lastRiders over a list of later
clauses. late: each of these begins at border 2 or later. Nothing here pays either. UNDER hrid THE
RIDERS HOLD tiedRider, WHICH BEGINS AT BORDER 1: so a statement that asks every rider to begin at
border 2 or later cannot be called at these letters: whoever spends this theorem takes, for the five
at member 0, five_at_lastParts_tied or five_at_lastRiders (AtFullSide/K14/AtLastTied.lean).

What is not claimed. That either invariant holds at any state, or that the start returns, or that
the premises can hold together: the two invariants are tied to each other by the states s₁ and s₂
alone. The other clauses of the last thread's invariant at border 0. Nothing on completeness,
soundness or hiding. Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a
chain with its parameters (Honest/Thread/Thr.lean).
-/
import AtFullSide.K14.DoorAtTerms
import AtFullSide.K14.TiedAheadAtTerms
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  LastLetters firstThread sharedThread lastParts lastRiders tiedRider)
open VerifiableInference.Desc.Third (S₃)
open P5J (TS)
open Desc.K14 (St)

variable {W₀ Rc Tr X₀ X : Type}

/-- **The field rides of lastParts at border 0, at the record that the last chain's start returns.**
hrid, late: L's riders are lastRiders at clauses that begin at border 2 or later. hT₁, hA: the two
earlier threads' invariants at their last borders. hs: the start's return. -/
theorem rides_zero_at_terms {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : SharedThreadParts A Wt) (L : LastLetters A) (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey)
    {later : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hrid : L.riders = lastRiders h.places later) (late : ∀ c ∈ later, 2 ≤ c.lo)
    {k₁ : Coins A.B} {s₁ : TS} {mid₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT₁ : Thr (firstThread h first w₁) h.firstChain.blocksInOrder.length k₁ s₁ mid₁ E₁)
    (Said : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins A.B} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (sharedThread h reads parts w₂) Said h.description.shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s : S₃) (hs : h.description.start₃ x s₁ s₂ = .ok s) :
    (lastParts h first L).rides 0 w₁ s := by
  show ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: L.riders) 0 w₁ s
  rw [hrid]
  intro c hc hlo hhi
  have hc' : c = doorRider _ (ToldDesc.p14At A.Z) ∨
      c = tiedAheadRider _ (LLT25.c2 h.places).rounds ∨ c = tiedRider _ h.places ∨
      c ∈ later := by
    simpa [lastRiders] using hc
  rcases hc' with rfl | rfl | rfl | hc'
  · exact second_door_at_terms h first reads parts w₁ w₂ hT₁ Said hA x s hs
  · exact tied_ahead_at_terms h first reads parts w₁ w₂ hT₁ hA.1 x s hs
  · exact absurd (show 1 ≤ 0 from hlo) (by omega)
  · exact absurd (late c hc') (by omega)

end AtFullSide.K14

#print axioms AtFullSide.K14.rides_zero_at_terms
