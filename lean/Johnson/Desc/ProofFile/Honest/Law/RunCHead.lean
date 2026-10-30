-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunCHead.lean: what the player `runC` (Honest/Walk.lean) hands to
the last chain's start, read off `runC_ends` (Honest/Law/RunC.lean). Where `runC` returns and the
first chain's end is a state s₁, that state is what the verifier's `foldBlocks` returns over the
first chain's whole flat list, from the chain's first state, at the run's own rounds and columns,
with nothing left over; the like for the shared chain; and the last chain's door is the
description's `start₃` at these two states. Then the first chain's fold and the door at the proof
file's description, in the letters `cF.blocksInOrder` and `ProofFile.startS Zp`.

  1  `runC_first_fold`, `runC_shared_fold`   the two ends, general in the description
  2  `runC_door`   the door at the two ends
  3  `runC_hands_head`   the first chain's fold and the door at `P5J.F0T`

Limits.
  * Corollaries of `runC_ends` and `fold_some`. Nothing on whether `runC` returns, or on whether an
    end is a state: where a sub-protocol has refused the end is `none`.
  * These are sentences on the player. The threads' letter `ends` (Honest/Thread/Last.lean) is not
    treated: no term for it stands here.
  * In 3 the first chain's rounds are the first view's with the sealing round put back.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunC
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open P5J (TS)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

section General
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F}

/-- The first chain's end is the fold's return, with nothing left over. -/
theorem runC_first_fold (h : runC F B H w₀ rc x c ρ = .ok r) {s₁ : F.S₁}
    (h₁ : r.ends.1 = some s₁) :
    foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened = .ok (s₁, [], []) :=
  (fold_some 0 _ _ _ _ _ (runC_ends h).1.1 (runC_ends h).1.2.1).1
    ((runC_ends h).1.2.2.symm.trans h₁)

/-- The shared chain's end likewise. -/
theorem runC_shared_fold (h : runC F B H w₀ rc x c ρ = .ok r) {s₂ : F.S₂}
    (h₂ : r.ends.2.1 = some s₂) :
    foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened = .ok (s₂, [], []) :=
  (fold_some 0 _ _ _ _ _ (runC_ends h).2.1.1 (runC_ends h).2.1.2.1).1
    ((runC_ends h).2.1.2.2.symm.trans h₂)

/-- The last chain's door at the two ends is the description's `start₃` at them. -/
theorem runC_door {s₁ : F.S₁} {s₂ : F.S₂} (h₁ : r.ends.1 = some s₁) (h₂ : r.ends.2.1 = some s₂) :
    door₃ F x r.ends.1 r.ends.2.1 = (F.start₃ (F.pub x) s₁ s₂).toOption := by
  rw [h₁, h₂]
  rfl

end General

/-- At the proof file's description: the state that the player hands to the last chain's start as
its first state is what `foldBlocks 0 cF.blocksInOrder` returns of `ProofFile.startS Zp` at the instance's public
part, at the run's own rounds and columns. -/
theorem runC_hands_head {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {B : ProverCoinCounts} {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {c : Coins B} {ρ : Draws} {r : RunC (P5J.F0T o Zp Np cF)}
    (h : runC (P5J.F0T o Zp Np cF) B H w₀ rc x c ρ = .ok r) {s₁ : TS}
    {s₂ : (P5J.F0T o Zp Np cF).S₂} (h₁ : r.ends.1 = some s₁) (h₂ : r.ends.2.1 = some s₂) :
    foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp x.pub) (withEmptySealRound r.run.views.1).rounds
        r.run.views.1.opened = .ok (s₁, [], []) ∧
      door₃ (P5J.F0T o Zp Np cF) x r.ends.1 r.ends.2.1 =
        ((P5J.F0T o Zp Np cF).start₃ x.pub s₁ s₂).toOption :=
  ⟨runC_first_fold h h₁, runC_door h₁ h₂⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.runC_first_fold
#print axioms ProofFile.Honest.runC_shared_fold
#print axioms ProofFile.Honest.runC_door
#print axioms ProofFile.Honest.runC_hands_head
