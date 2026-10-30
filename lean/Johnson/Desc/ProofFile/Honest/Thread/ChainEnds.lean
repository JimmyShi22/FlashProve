-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ChainEnds.lean: WHERE THE CHAINS MEET, AT THE PROOF FILE's
DESCRIPTION. `DoorYes` and `FinYes` (Honest/Thread/File.lean) ask, at every stand at the chains'
last borders, that the last chain's start returns and that the file's last test says yes. At
`ProofFile.fileDescBy` these are read off the description's own text: each comes down to what the
threads say at their last borders about the first chain's record, the shared chain's end, and the
last chain's seat.

  `doorYes_of_ends`   `DoorYes`, by `fileDescBy_start₃_iff` (Johnson/Desc/Plain/StartThree.lean)
  `finYes_of_ends`   `FinYes`, from the four clauses of that description's `fin`

What these are. Conditional lemmas on our own definitions and the library's. None is one of the
library's goals.

Limits.
  * Every premise speaks of a stand at a last border. None is shown here of any thread.
  * The key file has its own forms (`doorYes_key`, `finYes_key`, E2E/KeyThreads.lean).
  * That `P5J.F0T` is such a value of `fileDescBy` is not said here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.Plain.StartThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {σ W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy}
  {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {get : σ → VerifiableInference.Desc.First.S} {start : ProofFile.InstPub → σ} {c : Chain σ ProofFile.Cl}

local notation "𝔽" => ProofFile.fileDescBy o mk Z A B get start c

/-- **The last chain's start returns**, from what the threads say at their last borders. `hf`: the
first chain's record stands at its end. `he`: the shared chain has ended. `hs`: the last chain's
seat starts at these. -/
theorem doorYes_of_ends {T₁ : Thread Bk (𝔽).S₁ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {T₂ : Thread Bk (𝔽).S₂ (𝔽).Cl Empty (Common W₀ Rc Ky) X₀ Ky} {x : ProofFile.Inst} {k : Coins Bk}
    (hf : ∀ e m E, Thr T₁ (𝔽).first.blocksInOrder.length k e m E → (get e).fin = true)
    (he : ∀ e m E, Thr T₂ (𝔽).shared.blocksInOrder.length k e m E → ∃ d, A.ended e = some d)
    (hs : ∀ e₁ m₁ E₁ e₂ m₂ E₂ d, Thr T₁ (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ → A.ended e₂ = some d →
      ∃ s, B.start x.pub (get e₁) d = .ok s) :
    DoorYes 𝔽 T₁ T₂ x k := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  obtain ⟨d, hd⟩ := he e₂ m₂ E₂ u₂
  obtain ⟨s, hs'⟩ := hs e₁ m₁ E₁ e₂ m₂ E₂ d u₁ u₂ hd
  exact ⟨s, (ProofFile.fileDescBy_start₃_iff o mk Z A B get start c x.pub e₁ e₂ s).2
    ⟨hf e₁ m₁ E₁ u₁, d, hd, hs'⟩⟩

/-- **The file's last test says yes**, from what the threads say at their last borders: the reply
heard is the one asked about; the request's words are still the instance's; the shared chain has
ended; the last chain's seat is done. -/
theorem finYes_of_ends {T₁ : Thread Bk (𝔽).S₁ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {T₂ : Thread Bk (𝔽).S₂ (𝔽).Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {T₃ : Thread Bk (𝔽).S₃ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {x : ProofFile.Inst} {k : Coins Bk}
    (hask : ∀ e m E, Thr T₁ (𝔽).first.blocksInOrder.length k e m E → (get e).finAsked x.asked = true)
    (hreq : ∀ e m E, Thr T₁ (𝔽).first.blocksInOrder.length k e m E →
      ((get e).req == OnBytes.Model.Verify.words32 x.pub.request) = true)
    (he : ∀ e m E, Thr T₂ (𝔽).shared.blocksInOrder.length k e m E → (A.ended e).isSome = true)
    (hd : ∀ e m E, Thr T₃ (𝔽).second.blocksInOrder.length k e m E → B.done e = true) :
    FinYes 𝔽 T₁ T₂ T₃ x k := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ u₁ u₂ u₃
  show ((get e₁).finAsked x.asked && (get e₁).req == OnBytes.Model.Verify.words32 x.pub.request &&
    (A.ended e₂).isSome && B.done e₃) = true
  rw [hask e₁ m₁ E₁ u₁, hreq e₁ m₁ E₁ u₁, he e₂ m₂ E₂ u₂, hd e₃ m₃ E₃ u₃] <;> rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.doorYes_of_ends
#print axioms ProofFile.Honest.finYes_of_ends
