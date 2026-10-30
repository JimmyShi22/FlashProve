-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanAtB.lean: A TEST WITH CODE for one clause of `PlanAt`
(LastFive.lean), with its law: so that a file that evaluates it evaluates the clause itself.
  `fitsB cs a sh lg`, `fitsB_iff`: its yes is `ShapeFits cs a sh lg`
    (Johnson/Desc/K12/Coin/SiteAtSeats.lean). (The like for `K1.Tie`:
    `ToldDesc.tieB`, `ToldDesc.tie_iff`, Johnson/ToldDescR/TieB.lean.)
Limits. Nothing on soundness.
-/
import Johnson.Desc.K12.Coin.SiteAtSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12.Coin

/-- `ShapeFits`, as one Bool. -/
def fitsB (cs : Codes) (a : Fmt.M1.Stage) (sh : OracleShape) (lg : ℕ) : Bool :=
  (decide (0 < sh.mainRows) && decide (sh.maskRows = 0 → cs.mask.size ≤ sh.maskCode)) ||
    (decide (0 < sh.maskRows) && decide (cs.base.size ≤ sh.code) && decide (lg ≤ a.Z.a))

theorem fitsB_iff (cs : Codes) (a : Fmt.M1.Stage) (sh : OracleShape) (lg : ℕ) :
    fitsB cs a sh lg = true ↔ ShapeFits cs a sh lg := by
  unfold fitsB ShapeFits
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end LLT25

#print axioms LLT25.fitsB_iff
