-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Seated.lean: THE FRAME's SENTENCE "IT IS ACCEPTED" (`Accepted`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) AT A MEMBER OF A CHAIN AT WHICH A SEATED PROXIMITY
TEST STANDS, WITH THE HALF `proverSideOfProximityTest J`. General in the thread T, in the seat and in the letter
fall, at any type of claims. A structure of named premises on T's letters, a statement and its
proof: `saysYes_seat` (SaysYesSeat.lean in this folder) through `accepted_of_saysYes`
(Johnson/Desc/ProofFile/Honest/Thread/FileRowYes.lean).

  `K12Seated`    THE PREMISES ON THE THREAD's LETTERS, each under its name:
                 member   the chain's member number b is a block that seats the test (`SeatOf`)
                 half     the half that stands at the test's place is `proverSideOfProximityTest J`
                 stages   the place has two stages or more, and k = h + g at the first
                 stands   FROM THE THREAD IN FRONT, at every run's coins, at every list that the
                          member's rounds can sample, outside the fall, at whatever coins the book
                          lends the two parts: `K12At`
  **`accepted_k12`**   `K12Seated` ⟹ `Accepted T fall b`

Limits. `K12Seated` is asked; no thread is shown to meet it. Its clause "stands" holds all of
`K12At`: see SaysYesK12.lean's limits, which stand here. `Accepted` is a premise's form of the
frame's. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.ProofFile.Honest.Thread.FileRowYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The premises on the thread's letters.** -/
structure K12Seated (T : Thread Bk S Cl V W X Pb) (b : ℕ) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (fall : ℕ → S → List Fmt.Drawn → Option String) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g
  stands : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    Thr T b k st m E → drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
    fall b st ds = none →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    K12At J enter leave st m E ds c

/-- **It is accepted.** -/
theorem accepted_k12 (T : Thread Bk S Cl V W X Pb) (b : ℕ) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (h : K12Seated T b J enter leave fall) :
    Accepted T fall b := by
  obtain ⟨s, t, rest, hst, hk⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  exact accepted_of_saysYes T hblk
    (saysYes_seat T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (fall b) (Thr T b) s t rest hst
      hk h.half h.stands)
    (fun _ _ _ _ x => x) fun _ _ x => x

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.accepted_k12
