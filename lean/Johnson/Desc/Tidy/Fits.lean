-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/Fits.lean: a third way in which a block keeps a relation on its record, between
`Decides` (Johnson/Desc/FoldKeeps.lean: at every yes of the decision) and `Steps`
(Johnson/Desc/StepKeeps.lean: at a yes of the step, the plan's test passed): at a yes of the
decision ON ROUNDS THAT FIT THE DECLARED ONES, the plan's test passed. It is what a law that spends
the rounds' fit proves, and, unlike `Steps`, it goes through the joining of a block with a block
without a round behind it.
Main names: `Fits`, `fits_of_decides`, `steps_of_fits`, `fit_length`, `andThen_fits`.

What is not claimed. Nothing on any one block. Nothing on soundness.

-/
import Johnson.Desc.StepKeeps
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps

variable {S Cl : Type}

/-- Where the block's test on the plan passes, a yes of its decision on rounds that fit keeps R. -/
def Fits (R : S → S → Prop) (b : Block S Cl) : Prop :=
  b.planOk = true → ∀ (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : S),
    roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' → R s s'

theorem fits_of_decides {R : S → S → Prop} {b : Block S Cl} (h : Decides R b) : Fits R b :=
  fun _ _ _ _ _ _ hd => h _ _ _ _ hd

theorem steps_of_fits {R : S → S → Prop} {b : Block S Cl} (h : Fits R b) : Steps R b := by
  intro hp ft s rs cols s' k hs
  obtain ⟨hfit, gs, hd⟩ := step_fit ft b s s' rs cols k hs
  exact h hp s rs gs s' hfit hd

/-- Rounds that fit are as many as are declared. -/
theorem fit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    rs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [roundsFit] at h
  | _ :: _, [], h => by simp [roundsFit] at h
  | d :: ds, r :: rs, h => by
    simp only [roundsFit, Bool.and_eq_true] at h
    simp [fit_length ds rs h.2]

/-- **A block with a block without a round behind it.** -/
theorem andThen_fits (R : S → S → Prop) (ht : ∀ a b c, R a b → R b c → R a c) (n : String)
    (p q : Block S Cl) (hq0 : q.rounds = []) (hp : Fits R p) (hq : Decides R q) :
    Fits R (p.andThen n q) := by
  intro hpl s rs gs s' hfit h
  have hpl' : (p.planOk && q.planOk) = true := hpl
  have hfit' : roundsFit (p.rounds ++ q.rounds) rs = true := hfit
  rw [hq0, List.append_nil] at hfit'
  obtain ⟨a, h1, h2⟩ := ebind_ok
    (x := p.decide s ((rs.map noDigest).take p.rounds.length) (gs.take p.openings)) h
  have e : (rs.map noDigest).take p.rounds.length = rs.map noDigest := by
    refine List.take_of_length_le (Nat.le_of_eq ?_)
    rw [List.length_map, fit_length _ _ hfit']
  rw [e] at h1
  exact ht _ _ _ (hp (Bool.and_eq_true _ _ ▸ hpl').1 s rs _ a hfit' h1) (hq _ _ _ _ h2)

end VerifiableInference.Desc.Keeps
