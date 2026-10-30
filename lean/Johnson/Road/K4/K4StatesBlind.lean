-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4StatesBlind.lean: WHAT THE SEATED FEED-FORWARD SEGMENT's CALLER (K4) STATES
COMMUTES WITH THE ONE WRITING OF THE APPROXIMATE RANGE PROOF's DRAW: in the goals' scope, at an
opening, at each of the twelve groups. One statement with its proof: calls.

  `k4Block_blind` · `k4Block_leaves`: K4ClaimsBlind.lean's two at the lot's own sub-protocol
    `ProofFile.k4Block x`.
  **`k4_states_blind`**: hS · hR · an opening · g < 12 ⟹ ∃ Lk, c.links[2 * g]? = some Lk ∧ ∀ ρ ∈
    statesOfLink Lk 2, RunBlind (ρ.2 0): by `IM.k4_of` (Johnson/IMR/K4Seat.lean) and the
    approximate range proof's files' `claimsBlind_alone` and `states_blind` (WalkAlone.lean).

Limits. That there is an opening is shown by no theorem here. K04_law, the law of K4's sub-protocol
itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4ClaimsBlind
import Johnson.P1K8R.WalkAlone
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (RunBlind ClaimsBlind)
open VerifiableInference.Desc.K9 (statesOfLink)
open ProofFile (Cl)

theorem k4Block_blind (x : Bool × Par) : ClaimsBlind (ProofFile.k4Block x) :=
  k4_claimsBlind { x.2 with k3Runs := true }

theorem k4Block_leaves (x : Bool × Par) : P1K8T.LeavesOut (ProofFile.k4Block x) :=
  k4_leaves { x.2 with k3Runs := true }

/-- **WHAT THE SEATED SEGMENT's CALLER STATES COMMUTES WITH THE DRAW.** -/
theorem k4_states_blind {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : VerifiableInference.Desc.Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) :
    ∃ Lk, c.links[2 * g]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk 2, RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, x, e1, e2, _, ha, _⟩ := IM.k4_of hS hR O g hg
  exact ⟨Lk, e1, P1K8T.states_blind e2
    (P1K8T.claimsBlind_alone ha (k4Block_blind x) (k4Block_leaves x))⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Block_blind
#print axioms OnBytes.Road.K4.k4Block_leaves
#print axioms OnBytes.Road.K4.k4_states_blind
