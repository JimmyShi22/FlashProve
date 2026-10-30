-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FromGiven.lean: FROM THE BLOCK THAT RUNS TO THE LAW OF fromLookup: where
HeadFrame.lean's given returns, the lookup's points were laid, a next token was heard, the points pass
the test that the law of fromLookup asks (PointsOk, HeadInLaw.lean), and the letters that the kind's
formulas then read ARE fromLookup's at these points (given_ok). With the tests on the plan the letters are
the weights that they are taken for: Law/GivenLetters.lean. No chance in it.
WHAT IT DOES NOT SAY. That the points in the carried record are the lookup's draws; that the record's
request and token are the instance's and the heard one: laws of the seat and of other blocks.

-/
import Mathlib
import Johnson.Desc.Kinds.HeadFrame
import Johnson.Desc.Kinds.Law.Call

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Norm (lt ls d S2 T)

section Sized
variable [Sizes]

/-- A test on all calls holds of each. -/
theorem all_calls (i : FromLookup) (hi : i.calls.length = 6)
    (f : (E × List PlaceKey) × Nat → Bool) (h : i.calls.zipIdx.all f = true) :
    ∀ c, c < 6 → f (i.calls.getD c (0, []), c) = true := by
  intro c hc
  rw [List.all_eq_true] at h
  apply h
  rw [List.mem_zipIdx_iff_getElem?]
  simp only [Nat.sub_zero, Nat.zero_le, true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

theorem calls_length (floor : Nat) (zx : Point) (zk : Nat → Point) :
    (fromLookup floor zx zk).calls.length = 6 := rfl

theorem calls_keys (floor : Nat) (zx : Point) (zk : Nat → Point) {c : Nat} (hc : c < 6) :
    ((fromLookup floor zx zk).calls.getD c (0, [])).2 = callKeys c := by
  interval_cases c <;> rfl

/-- given's third test, as it is typed there, gives PointsOk. -/
theorem pointsOk_of_test (floor : Nat) (zx : Point) (zk : Nat → Point)
    (h : ((fromLookup floor zx zk).calls.zipIdx.all fun c =>
      (zk c.2).size == lJ floor c.1.2 + Norm.lt &&
        (zk c.2).last (Norm.ls + Norm.lt) == zx.last (Norm.ls + Norm.lt)) = true) :
    PointsOk floor zx zk := by
  intro c keys hc
  have hc6 : c < 6 := by
    by_contra hge
    have hn : callList[c]? = none := List.getElem?_eq_none (by
      have : callList.length = 6 := rfl
      omega)
    rw [hn] at hc
    cases hc
  have hk : keys = callKeys c := by
    rw [call_get hc6] at hc
    exact (Option.some.inj hc).symm
  subst hk
  have h1 := all_calls _ (calls_length floor zx zk) _ h c hc6
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  rw [calls_keys floor zx zk hc6] at h1
  exact h1

end Sized

variable {S : Type}

/-- **Where given returns.** -/
theorem given_ok (p : Par) (L : Seat S) (s : S) (g : Given) (h : given p L s = .ok g) :
    ∃ (z : Point × (Nat → Point)) (y : Nat), L.lookup s = some z ∧
      Reply.token L.toSeat s = some y ∧
      @PointsOk p.sizes p.floor z.1 z.2 ∧
      g = { sizes := p.sizes, policy := p.policy, request := L.request s, token := ⟨y⟩,
            normIn := (@fromLookup p.sizes p.floor z.1 z.2).norm,
            headIn := (@fromLookup p.sizes p.floor z.1 z.2).head,
            calls := (@fromLookup p.sizes p.floor z.1 z.2).calls } := by
  unfold given at h
  cases hz : L.lookup s with
  | none =>
    rw [hz] at h
    simp [named, bind, Except.bind] at h
  | some z =>
    cases hy : Reply.token L.toSeat s with
    | none =>
      rw [hz, hy] at h
      simp [named, bind, Except.bind] at h
    | some y =>
      rw [hz, hy] at h
      letI := p.sizes
      by_cases ht : ((fromLookup p.floor z.1 z.2).calls.zipIdx.all fun c =>
          (z.2 c.2).size == lJ p.floor c.1.2 + Norm.lt &&
            (z.2 c.2).last (Norm.ls + Norm.lt) == z.1.last (Norm.ls + Norm.lt)) = true
      · refine ⟨z, y, rfl, rfl, pointsOk_of_test p.floor z.1 z.2 ht, ?_⟩
        simp only [named, need, bind, Except.bind, ht, if_true, pure, Except.pure] at h
        exact (Except.ok.inj h).symm
      · simp only [named, need, bind, Except.bind, ht, pure, Except.pure] at h
        simp at h

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok
