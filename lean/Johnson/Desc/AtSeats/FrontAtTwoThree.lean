-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FrontAtTwoThree.lean: THE TEST `frontB`
(Johnson/Desc/K13/Law/BridgeG.lean: what the tie at the first segment's opening reads of the
walk's copy of the frame) AT THE REACHED STATES OF BORDERS 2 AND 3: what that tie's bridge asks of
the fold. One statement with its proof; general in the list of sub-protocols and in the first
state. `front_23`: WHERE (h2) at border 2 the reached state is the first state itself (
  `reach_two`, Johnson/P1L20R/RoomFold.lean, says so in the goals' scope); (hstart) the first
  state, where it bears no mark, passes the test (two facts on that function's own text: its
  frame's groups are its shape's; nothing is kept); (hb, hu) the sub-protocol at number 2 stands
  under the joined opening. At border 3 the state comes by one accepting step from the state at 2,
  and the opening leaves the test (`openingZero_front`) and the mark.
What is not claimed. h2, hstart, hu. Nothing on soundness.

-/
import Johnson.IMR.HandsDef
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.K13.Law.BridgeG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (frontB openingZero_front StepG)
open VerifiableInference.Desc
open ProofFile (Cl)

/-- **The test at the reached states of borders 2 and 3.** -/
theorem front_23 {Q : Type} {bs : List (Block S Cl)} {start : Q → S}
    (h2 : ∀ z s, Reach 0 bs start 2 (z, s) → s = start z)
    (hstart : ∀ z, (start z).failed = none → frontB (start z) = true) {e : Block S Cl}
    (hb : bs[2]? = some e) {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ}
    (hu : e.UnderR (K1.openingZero q gp nm X fvs kCol : Block S Cl)) :
    ∀ j a, Reach 0 bs start j a → j = 2 ∨ j = 3 → a.2.failed = none → frontB a.2 = true := by
  intro j a hr hj hm
  rcases hj with rfl | rfl
  · obtain ⟨z, s⟩ := a
    obtain rfl := h2 z s hr
    exact hstart z hm
  · cases hr with
    | @succ _ z s s' b hr2 hb' hy =>
      obtain rfl : e = b := Option.some.inj (hb.symm.trans hb')
      obtain ⟨R, c, _, hst⟩ := hy
      have hY : IM.Yes 0 (K1.openingZero q gp nm X fvs kCol : Block S Cl) s s' :=
        (show IM.Yes 0 e s s' from ⟨R, c, c.length, hst⟩).under hu
      obtain ⟨rs, cols, n, h1⟩ := hY
      have hG : StepG Cl q gp nm X fvs kCol (z, s) (z, s') := ⟨rfl, 0, rs, cols, n, h1⟩
      obtain ⟨r₁, r₂, gs, hd⟩ := hG.decide
      have hf : s'.failed = s.failed := (K1.openingZero_rec hd).2.2.1
      obtain rfl := h2 z s hr2
      show frontB s' = true
      rw [openingZero_front hd]
      exact hstart z (hf.symm.trans hm)

end HashBuild
