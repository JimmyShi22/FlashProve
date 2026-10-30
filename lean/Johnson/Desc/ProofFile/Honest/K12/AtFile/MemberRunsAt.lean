-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/MemberRunsAt.lean: what a member's round asks at a run: where `ready`
returns, each member of the shared chain has its steps, and where no half stops no part stops. So
`MemberRuns` (Honest/ThruWalk.lean) at each member of a shared thread, at every list that fits.

  `steps_member`   where `chainSteps` returns at a list it returns at each member of the list
  `runs_of_ready`  `MemberRuns` at a member of a thread of the chain, from `ready`

Limits.
- `ready` returns is a premise: that it does at the term is another law's.
- hstops: no half stops: that is the prover's sides' test.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.ThruWalk
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Run
import E2E.NoStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

/-- **Where `chainSteps` returns at a list it returns at each member.** -/
theorem steps_member {S Cl V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} (hs : List (Placed V W X)) :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W X)), chainSteps B rows look v bs hs = .ok ss →
      ∀ b ∈ bs, ∃ l, chainSteps B rows look v [b] hs = .ok l := by
  intro bs ss h b hb
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb
  rw [chainSteps_append, show b :: l₂ = [b] ++ l₂ from rfl, chainSteps_append] at h
  cases h₁ : chainSteps B rows look v l₁ hs with
  | error e =>
    simp [h₁, Except.bind] at h
  | ok r₁ =>
    cases h₂ : chainSteps B rows look v [b] hs with
    | error e =>
      simp [h₁, h₂, Except.bind, Except.map] at h
    | ok r₂ => exact ⟨r₂, rfl⟩

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Cl' V Pb : Type}

/-- **`MemberRuns` at a member of a shared thread, from `ready`.** -/
theorem runs_of_ready {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w₀ rc x k = .ok R)
    (T : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hbs : T.bs = F.shared.blocksInOrder)
    (hhs : T.hs = H.shared) (hch : T.chain = 1) (hφ : T.φ = .shared)
    (hstops : AtPublicFiles.Stops.NoStop T.hs) {j : ℕ} {blk : Block F.S₂ F.Cl} (hb : T.bs[j]? = some blk)
    {ds : List Fmt.Drawn} (hd : drawsFit blk.rounds ds = true) : MemberRuns T k j ds := by
  obtain ⟨-, -, -, -, -, -, s2, -⟩ := ready_ok hR
  refine ⟨blk, hb, hd, fun m => ⟨AtPublicFiles.Stops.chainStopAt_none _ hstops [blk] _ _, ?_⟩⟩
  have hm : blk ∈ F.shared.blocksInOrder := by
    rw [← hbs]
    exact List.mem_of_getElem? hb
  obtain ⟨l, hl⟩ := steps_member _ _ _ s2 blk hm
  refine ⟨l, ?_⟩
  rw [hhs, hch, hφ]
  exact hl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.steps_member
#print axioms ProofFile.Honest.K12.AtFile.runs_of_ready
