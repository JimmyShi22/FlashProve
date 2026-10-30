-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontClaim.lean: the proof of `FrontClaimAtHead`
(Honest/K11/Plays/FrontClaimStatement.lean), to the letter. A lemma; none of the library's goals.

How. The thread's sentence holds a fold of the description's first 346 sub-protocols, from the
description's own first state, over all that was seen, which leaves no round (its clause "made"); so
the rounds seen are just these sub-protocols' rounds (the frame's `fold_rest`,
Honest/Thread/ReachRounds.lean), and their challenges are the challenges heard. No mark: the
thread's form. The reply: the thread's rider from b₀ on (`head_reply`,
Honest/Thread/FirstHead.lean). Then `headClaimIsOfK3` (Honest/K11/ClaimIsOfK3.lean) at that fold, at
the letter claims laid as the written text at every link.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontClaimStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsOfK3
import Johnson.Desc.ProofFile.Honest.Thread.ReachRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (foldBlocks)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open ProofFile.Honest.FirstThread (head_reply)

/-- **The last clause of the field front, at the head's thread.** -/
theorem frontClaim_at_head : FrontClaimAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    a claim hB hb hTS ha hcl
  obtain ⟨hT, _⟩ := hTS
  obtain ⟨_, _, hForm, _, hMade, hrides, _⟩ := hT
  obtain ⟨hseen, _, _, _, s₀, cols, hbeg, _, hf⟩ := hMade
  have hs₀ : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  subst hs₀
  have hf' : foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp m.st.input.x.pub) m.seen cols =
      .ok (s, [], []) := hf
  have hrest : m.seen.drop (roundsAhead cF.blocksInOrder 346) = [] := (fold_rest 0 _ _ _ _ _ _ _ hf').symm
  have htake : m.seen.take (roundsAhead cF.blocksInOrder 346) = m.seen := by
    have e := List.take_append_drop (roundsAhead cF.blocksInOrder 346) m.seen
    rwa [hrest, List.append_nil] at e
  have hfail : s.failed = none := Option.isNone_iff_eq_none.1 hForm.1
  have hrep : s.out.reply = some m.st.input.x.asked :=
    head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hrides
  have h1 : some (headClaimsAt cF Zp Bs.G₀ m.st.input.x
      ((m.seen.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn))).toArray = some #[claim] :=
    headClaimIsOfK3 Z D r Zp Np cF x Bs 24
      (fun _ y hd => some (headClaimsAt cF Zp Bs.G₀ y hd).toArray) h hB (fun _ _ => rfl)
      m.st.input.x m.seen cols s [] a claim (by rw [hrest]; exact hf') hfail hrep ha hcl
  rw [htake, hseen] at h1
  have h2 := congrArg Array.toList (Option.some.inj h1)
  simpa using h2

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.frontClaim_at_head
