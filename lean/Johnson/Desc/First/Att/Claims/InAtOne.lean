-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InAtOne.lean: kind K5: ALONG THE LEDGERS OF ONE SEGMENT THE KIND's RUNS GIVE ONE ANSWER: what "first" and "second"
read and gather at a ledger U of which the named premise K5OkAt holds (Claims/InAt.lean) is what they read and gather at every later
ledger with U's width at the array of the reads: THE SAME RETURN, OR A REFUSAL AT BOTH.

Main names: inAt_forth (no premise on U but "later" and the width) · inAt_one · firstAt_one · secondAt_one: equations of Options.
Forth is Claims/LeftLater.lean's ptsFrom_later; back is Claims/InAt.lean's inAt_back.
For whom: a reader that "is the run itself" is asked to give one list at every border at which its item is open.
IS IT EMPTY HERE? No: an equation, at a refusal too. K5OkAt is shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InAt

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)

variable {c : ParC} {g : Forest.Heard} {h : Heard} {U G' : Fork}

/-- Forth: what inAt returns at U it returns at a later ledger of U's width. -/
theorem inAt_forth (hL : Later U G') (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K))
    {x : P.Runs.In × ℕ} (e : inAt c g h U = some x) : inAt c g h G' = some x := by
  unfold inAt at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨p, hp, t, ht, K, hk, r⟩ := e
  exact ⟨p, ptsFrom_later hL hp, t, ht, K, hK ▸ hk, r⟩

/-- **One answer.** -/
theorem inAt_one (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) : inAt c g h G' = inAt c g h U := by
  cases e : inAt c g h G' with
  | some x => exact (inAt_back Q hL hK e).symm
  | none =>
    cases e' : inAt c g h U with
    | none => rfl
    | some x => rw [inAt_forth hL hK e'] at e; cases e

theorem firstAt_one (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) : firstAt c g h G' = firstAt c g h U := by
  unfold firstAt
  rw [inAt_one Q hL hK]

theorem secondAt_one (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) : secondAt c g h G' = secondAt c g h U := by
  unfold secondAt
  rw [inAt_one Q hL hK]

end K5Law

#print axioms K5Law.inAt_one
#print axioms K5Law.firstAt_one
#print axioms K5Law.secondAt_one
