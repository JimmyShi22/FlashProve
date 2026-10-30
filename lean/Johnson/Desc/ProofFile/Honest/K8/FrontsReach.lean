-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontsReach.lean: EVERY STATE THAT `frontsOf`
(Johnson/Desc/ProofFile/Honest/Fall.lean) LISTS IN FRONT OF A MEMBER IS A STATE THAT THE CHAIN's OWN
BLOCKS REACH THERE (`Reach`, Johnson/Top/H0/Walk/Reach.lean). Statements and proofs, on
`Block.step`, `frontsOf` and `Reach` alone: general in the state, the claims and the description; no
run, no prover, no coin. LEMMAS; NONE OF THE LIBRARY's GOALS.

  `stepYes_of_step`   a yes of a block's step at as many rounds as it declares, at whatever columns,
      is a yes at just the columns that it reads: the step reads a front stretch of the columns and
      returns its length (step_ok_iff, Johnson/Desc/Sound/RunIsDecide.lean)
  **`frontsOf_reach`**   from a state reached at number k, along the members from k on: entry n of
      `frontsOf` holds a state reached at number k + n, and the place of member k + n
  **`frontsOf_reach₀`**   from the chain's start: entry n holds a state reached at number n: at
      every list of rounds and columns
Limits. Nothing on which rounds and columns a run lays. That no other member bears an entry's place
is not said.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Fall
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Block OpenedColumn)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

variable {S Cl P : Type}

/-- A yes of the step at whatever columns is a yes at just the columns that it reads. -/
theorem stepYes_of_step {ft : ℕ} {b : Block S Cl} {s s' : S} {R : List Fmt.RoundView} {c : List OpenedColumn}
    {n : ℕ} (hR : R.length = b.rounds.length) (h : b.step ft s R c = .ok (s', n)) :
    StepYes ft b s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := (VerifiableInference.Desc.Sound.step_ok_iff ft b s s' R c n).1 h
  have hlen : (c.take n).length = n := by
    have e := congrArg List.length h2
    rw [List.length_map] at e
    rw [e, ← h3]
  refine ⟨R, c.take n, hR, ?_⟩
  rw [hlen]
  refine (VerifiableInference.Desc.Sound.step_ok_iff ft b s s' R (c.take n) n).2 ⟨h1, ?_, h3, ?_⟩
  · rw [List.take_take, Nat.min_self]
    exact h2
  · rw [List.take_take, Nat.min_self]
    exact h4

/-- **Every state that `frontsOf` lists is reached.** -/
theorem frontsOf_reach (ft : ℕ) (all : List (Block S Cl)) (start : P → S) (z : P) :
    ∀ (bs : List (Block S Cl)) (k : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ)
      (e : VerifiableInference.Desc.Place × S × List Fmt.Drawn),
      Reach ft all start k (z, s) → all.drop k = bs → (frontsOf ft bs s rs cols)[n]? = some e →
      Reach ft all start (k + n) (z, e.2.1) ∧ (all[k + n]?).map (·.place) = some e.1
  | [], _, _, _, _, _, _, _, _, he => by
    simp [frontsOf] at he
  | b :: l, k, s, rs, cols, n, e, hr, hd, he => by
    have hb : all[k]? = some b := by
      have e0 := congrArg (fun x => x[0]?) hd
      simpa [List.getElem?_drop] using e0
    have hd' : all.drop (k + 1) = l := by
      have e0 := congrArg (List.drop 1) hd
      simpa [List.drop_drop, Nat.add_comm] using e0
    unfold frontsOf at he
    simp only at he
    split at he
    · simp at he
    · rename_i hg
      have hlen : (rs.take b.rounds.length).length = b.rounds.length := by simpa using hg
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        exact ⟨hr, by simp [hb]⟩
      | succ n =>
        rw [List.getElem?_cons_succ] at he
        cases hst : b.step ft s (rs.take b.rounds.length) cols with
        | error e' =>
          rw [hst] at he
          simp at he
        | ok x =>
          obtain ⟨s', m⟩ := x
          rw [hst] at he
          have ih := frontsOf_reach ft all start z l (k + 1) s' _ _ n e
            (Reach.succ hr hb (stepYes_of_step hlen hst)) hd' he
          rwa [show k + 1 + n = k + (n + 1) by omega] at ih

/-- **From the chain's start.** -/
theorem frontsOf_reach₀ (ft : ℕ) (all : List (Block S Cl)) (start : P → S) (z : P)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ)
    (e : VerifiableInference.Desc.Place × S × List Fmt.Drawn)
    (he : (frontsOf ft all (start z) rs cols)[n]? = some e) :
    Reach ft all start n (z, e.2.1) ∧ (all[n]?).map (·.place) = some e.1 := by
  have h := frontsOf_reach ft all start z all 0 (start z) rs cols n e (Reach.zero z) rfl he
  rwa [Nat.zero_add] at h

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.stepYes_of_step
#print axioms ProofFile.Honest.K8.frontsOf_reach
#print axioms ProofFile.Honest.K8.frontsOf_reach₀
