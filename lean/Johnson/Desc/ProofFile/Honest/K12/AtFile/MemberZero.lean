-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/MemberZero.lean: member 0 of a shared thread: the frame's quiet block in
front of the chain. It has no round and no message, and its decision returns the state as it is.

  `row_zero`     row 0 shuts and owes nothing; `pinT` is open at the start
  `five_zero`    the five sentences at member 0: `PlaysS`, `AcceptedS` at every fall, `BehindS`, `ExchangeS`,
                 `RidesPastS`

The premises on letters. hform, hrides, hkeep: the form at 1, the riders at 1 and what member 0 keeps, at a stand:
the state behind the member is the one in front. hE: what member 0 keeps leaves the state. hC: the open item
`pinT` at the start reads nothing of the trees in hand.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each has `ThrS` as a premise.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw
import Johnson.Desc.ProofFile.Honest.Thread.Shared
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import E2E.KeyThreads
import Johnson.Desc.ProofFile.Honest.K14.Thread2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block step_iff)
open VerifiableInference.Desc.Shared (ItemS)
open Desc.K14 (St frontBlock)
open Desc.K14.Honest (Like)

/-- Row 0 shuts and owes nothing, and what is open at the start is `pinT`. -/
theorem row_zero : (SharedRows.rows true 0).owes = [] ∧ (SharedRows.rows true 0).shuts = [] ∧
    fwdOpen SharedRows.start (SharedRows.rows true) 0 = [.pinT] := by decide

variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
  (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)

/-- **The five sentences at member 0.** -/
theorem five_zero (hsp : L.split = true) (c : OnBytes.Model.Verify.Chains) {b₀ : Block St Cl}
    (hb₀ : L.thread.bs[0]? = some b₀) (hl : Like b₀ (frontBlock c))
    (hform : ∀ k s m E, ThrS L.thread Said 0 k s m E → L.shape 1 s = true)
    (hrides : ∀ k s m E, ThrS L.thread Said 0 k s m E → L.thread.rides 1 m.st.input s)
    (hkeep : ∀ k s m E, ThrS L.thread Said 0 k s m E → L.thread.keeps 0 s s)
    (hE : ∀ k s m E s', ThrS L.thread Said 0 k s m E → L.thread.keeps 0 s s' → s' = s)
    (hC : ∀ w s y y' v, (L.Mg w).pinT s y v → (L.Mg w).pinT s y' v)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS L.thread Said 0 ∧ AcceptedS L.thread Said fall 0 ∧ BehindS L.thread Said 0 ∧
      ExchangeS L.thread Said 0 ∧ RidesPastS L.thread Said 0 := by
  have hr : b₀.rounds = [] := hl.rounds
  have ho : b₀.oracles = [] := hl.oracles
  have hd : ∀ s rs gs, b₀.decide s rs gs = .ok s := fun s rs gs => by
    rw [hl.decide]
    rfl
  have hrow : L.thread.row 0 = SharedRows.rows true 0 := by
    show SharedRows.rows L.split 0 = _
    rw [hsp]
  obtain ⟨h1, h2, h3⟩ := row_zero
  refine ⟨playsS_of _ _ (plays_quiet L.thread hb₀ hr ho),
    acceptedS_of _ _ (AtPublicFiles.AtFiles.accepted_quiet L.thread hb₀ hr fun _ s _ _ _ => ⟨s, hd s [] []⟩),
    ?_, ?_, ?_⟩
  · intro blk hblk k s m E ds y cols s' u _ hS
    rw [hb₀] at hblk
    cases hblk
    obtain ⟨_, hdec, _⟩ := (step_iff _ b₀ s s' _ cols _).1 hS.2
    rw [hd] at hdec
    obtain rfl : s = s' := Except.ok.inj hdec
    have hM := hS.1
    unfold Thread.Moved at hM
    obtain ⟨⟨l, -, hp⟩, -⟩ := hM
    have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hp).1
    refine ⟨⟨?_, u.1.2.2.1.2⟩, ?_, hkeep k s m E u⟩
    · show (L.shape 1 s && (!decide ((VerifiableInference.Desc.Shared.sharedPlaces L.split).length ≤ 1) ||
        L.nothingLeft s)) = true
      have hlen : (VerifiableInference.Desc.Shared.sharedPlaces true).length = 12 := rfl
      rw [hform k s m E u, hsp, hlen]
      rfl
    · rw [hi]
      exact hrides k s m E u
  · intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
    rw [hrow, h1] at hi
    cases hi
  · intro k s m E s' ps i v u hk hi _ _ hu
    obtain rfl := hE k s m E s' u hk
    have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 0 := by
      have e : i ∈ fwdOpen SharedRows.start (SharedRows.rows L.split) 0 := hi
      rw [hsp] at e
      exact e
    rw [h3] at hi'
    obtain rfl : i = .pinT := List.mem_singleton.1 hi'
    exact hC m.st.input _ _ _ v hu

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.row_zero
#print axioms ProofFile.Honest.K12.AtFile.five_zero
