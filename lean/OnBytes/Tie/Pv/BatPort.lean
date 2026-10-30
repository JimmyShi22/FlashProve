-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/BatPort.lean: the round before a proximity test's first fold against
the round "BAT" that the planner adds: as many values, and the planner's price covers the block's
error.

The block is that of Cb/Pv/Bat.lean: one round, the error L * Z.err of as many seeds as Z has.
The planner's routine `planBat` (OnBytes/Params/Planner.lean) prices the round at the largest list
size of the groups times (rows - 1) / q. Statements with their proofs.
Main names:
  `runs`: `planBat` adds the one round `batRound` (`runs_bat`, OnBytes/Params/PlanListsProx.lean).
  `vals_port`: the block's verifier's message has as many values as the planned round's, if Z has as
    many seeds as the setting's field has elements.
  `covered`: the block's error, as a share of its seeds, is at most the error that a plan holds for
    the round under the scope `.once`, if Z has rows - 1 bad seeds and L is at most the largest list
    size of the groups (`list_powers_covers`, OnBytes/Params/MorePrices.lean).
  `covered_num`: the same at the error list * (rows - 1) of `Cb.Pv.Bat.HNum`.
Limits: an inequality, not an equality: the planner's list size may be larger than L, and its
bound is a product of two bounds, rounded upward. That the price is not marked bad is a hypothesis;
`close` has tested it wherever the routine ended well. That L bounds the lists of a group of a key
file's chains is not shown.

-/
import Cb.Pv.Bat
import OnBytes.Tie.Pv.PortKit
import OnBytes.Params.PlanListsProx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Bat
open OnBytes OnBytes.Params Iop IOR Cb

/-- The planner's routine adds one round. -/
theorem runs (σ : Setting) (c : Scope) (groups : List GroupSize) (rows : ℕ) :
    Runs σ c 0 0 0 (planBat groups rows) () [batRound σ groups rows] 0 0 0 := runs_bat groups rows

theorem values_bat (σ : Setting) (groups : List GroupSize) (rows : ℕ) :
    valuesOf σ.cardE (batRound σ groups rows) = σ.cardE := by
  simp [valuesOf, batRound]

/-- As many values. -/
theorem vals_port {E : Type} [Field E] [Fintype E] (s : Size E) (St₀ : Type) (E₀ : ExtSpec)
    (σ : Setting) (groups : List GroupSize) (rows : ℕ) (hD : Fintype.card s.Z.D = σ.cardE) :
    (R s St₀ E₀).shape.chalList = [batRound σ groups rows].map (valuesOf σ.cardE) := by
  rw [vals, hD, List.map_singleton, values_bat]

/-- The planner's price covers list * (rows - 1) of q, for a list size up to the planner's. -/
theorem covered_num (σ : Setting) (groups : List GroupSize) (rows list : ℕ)
    (hL : list ≤ largestList σ groups)
    (g : (Bound.ofNat (largestList σ groups) * powersError σ rows).bad = false) :
    Covered σ .once (list * (rows - 1), σ.cardE) (batRound σ groups rows) := by
  unfold Covered batRound
  rw [(round_once σ _ _ _ _ _ _ _).1]
  have h := list_powers_covers σ rows hL g
  show (((list * (rows - 1) : ℕ) : ℝ)) / (σ.cardE : ℝ) ≤ _
  rw [Nat.cast_mul]
  exact h

/-- The planner's price covers the block's error. -/
theorem covered {E : Type} [Field E] [Fintype E] (s : Size E) (σ : Setting)
    (groups : List GroupSize) (rows : ℕ) (hD : Fintype.card s.Z.D = σ.cardE)
    (hZ : s.Z.err = rows - 1) (hL : s.L ≤ largestList σ groups)
    (g : (Bound.ofNat (largestList σ groups) * powersError σ rows).bad = false) :
    Covered σ .once (s.L * s.Z.err, Fintype.card s.Z.D) (batRound σ groups rows) := by
  rw [hD, hZ]
  exact covered_num σ groups rows s.L hL g

end Cb.Pv.Bat

#print axioms Cb.Pv.Bat.vals_port
#print axioms Cb.Pv.Bat.covered
