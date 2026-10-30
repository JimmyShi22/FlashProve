--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsWithCostsAt.lean.
WHAT IT DOES NOT SHOW. All that Law/CellsWithCosts.lean says it does not show. The sizes and the
policy are typed in here as numbers: THAT THEY ARE THOSE OF THE STORED FULL-SIZE EXAMPLE IS BY
READING another desk's record of them (Law/K07MemberAt.lean: hR, through sizesOf | parOf): no tie is
typed. The request is MADE UP: 1024 tokens 0; positions 0 up to 1022 are checked; the next token 0.
WHAT IT IS. THE PREMISES OF cells_with_costs ARE MET TOGETHER, AT A REQUEST WITH 1023 POSITIONS THAT
HAVE A COST: so that theorem is not empty.
  sizesX, policyX, requestX, tokenX   the letters.
  plan_X, request_X, token_X, admits_X, costed_X, rc_X   the premises; every position below 1023 has
                    a cost; RC = 1023.
  cells_X           cells_with_costs at these letters: no premise is left.
At these letters theta = C = 256 = 2^sh: the policy admits just the cost of a position whose token
wins every tie; the slacks of the mean and of the clip are 0.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsWithCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtX

open Norm (lt ls d lPd T S2)

@[reducible] def sizesX : Sizes :=
  { lt := 10, ls := 6, d := 5120, MF := 44, KF := 30, epsF := 53687, V := 202048, sh := 8, F := 24 }
@[reducible] def policyX : Policy := { C := 256, theta := 256, cap := 0 }
@[reducible] def requestX : Request := { tok := fun _ => 0, r := 0, e := 1023 }
@[reducible] def tokenX : Token := ⟨0⟩

attribute [local instance] sizesX policyX requestX tokenX

theorem plan_X : planOk 4 = true := by decide

theorem request_X : Request.ok = true := by
  unfold Request.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨by decide, by decide⟩, fun _ _ => (by decide : (0 : Nat) < 202048)⟩

theorem token_X : y < V := by decide

theorem win_X (t : Nat) : win t = 0 := by
  unfold win
  split <;> rfl

theorem admits_X : Admits :=
  ⟨fun t _ => by
      unfold costN
      rw [win_X]
      decide,
    by decide, last_of_lt (by decide)⟩

theorem costed_X {t : Nat} (ht : t < 1023) : costed t = true :=
  (costed_iff_min t).mpr ⟨Nat.zero_le _, by
    show t < min 1023 (2 ^ 10 - 1)
    omega⟩

theorem rc_X : RC = 1023 := by decide

/-- **cells_with_costs AT THESE LETTERS: NO PREMISE IS LEFT.** -/
theorem cells_X :
    ∃ c : NCells, (dataOf c).Holds ∧ TableOk stepTab ∧ CellRel c.toCells stepTab ∧
      IntRel c.toCells stepTab ∧
      (∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 ∧ tableAt c.toCells (corner 0 t) = 0) ∧
      meanAt c.toCells = 0 ∧ countAt c.toCells = 0 ∧
      (∀ n t, numZ c.toCells n t = (headNum n t : Int)) ∧ (∀ k v, c.Wh k v = 0) ∧
      ∀ t, numZ c.toCells .paid t = cost c.toCells t :=
  cells_with_costs plan_X request_X token_X admits_X

end VerifiableInference.Desc.Kinds.Head.Law.AtX
