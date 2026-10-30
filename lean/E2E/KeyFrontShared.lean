--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyFrontShared.lean: THE KEY FILE's SHARED CHAIN's FRONT IS ACCEPTED. Its sub-protocol number 0
has no round, and its decision returns the state as it is (`sharedFront`,
Johnson/Desc/Key/Chains23.lean: its tests are tests on the plan). One call of `accepted_quiet`
(E2E/KeyThreads.lean).

  **`accepted_front₂`**: `Accepted` at number 0, at every thread over the shared chain's flat list
    and at every fall. No premise on the thread's sentence.
  `yes₂_laid'`: so `Yes` at the shared chain's thread as laid (E2E/KeyAcceptLaid.lean's `yes₂_laid`)
    from `Accepted` at its sub-protocols but the first and the last.

Limits. On one sub-protocol. In scope the shared chain has two further sub-protocols without a
round, and the first chain eleven (E2E/KeyPlaces.lean); their decisions test something: they have no
adapter here.

-/
import E2E.KeyAcceptLaid

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink

variable {W₀ Rc Ky X₀ : Type} {Bk : ProverCoinCounts} (X : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (T₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)

/-- **The shared chain's front is accepted.** -/
theorem accepted_front₂ {fall : Nat → (keyFileDescription X N P).S₂ → List Fmt.Drawn → Option String}
    (hbs : T₂.bs = (keyFileDescription X N P).shared.blocksInOrder) : Accepted T₂ fall 0 := by
  have hb : ∃ blk, (keyFileDescription X N P).shared.blocksInOrder[0]? = some blk ∧ blk.rounds = [] ∧
      ∀ s, blk.decide s [] [] = .ok s := ⟨_, rfl, rfl, fun _ => rfl⟩
  obtain ⟨blk, e, hr, hd⟩ := hb
  exact accepted_quiet T₂ (b := 0) (by rw [hbs]; exact e) hr fun _ s _ _ _ => ⟨s, hd s⟩

/-- **`Yes` at the shared chain**, from `Accepted` at its sub-protocols but the first and the last.
-/
theorem yes₂_laid' (q : KeyNums)
    (U₂ : Thread Bk (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    {fall : Nat → (keyFileDescription X N P).S₂ → List Fmt.Drawn → Option String}
    (hbs : U₂.bs = (keyFileDescription X N P).shared.blocksInOrder)
    (hn : (U₂.hs.find? fun g => g.place == (keyFileDescription X N P).shared.last.place) = none)
    (h : ∀ b, 0 < b → b + 1 < (keyFileDescription X N P).shared.blocksInOrder.length →
      Accepted (withForm U₂ (Form₂ X N P q)) fall b) :
    Yes (withForm U₂ (Form₂ X N P q)) fall :=
  yes₂_laid X N P q U₂ hbs hn fun b hb => by
    rcases Nat.eq_zero_or_pos b with rfl | h0
    · exact accepted_front₂ X N P (withForm U₂ (Form₂ X N P q)) hbs
    · exact h b h0 hb

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accepted_front₂
#print axioms AtPublicFiles.AtFiles.yes₂_laid'
