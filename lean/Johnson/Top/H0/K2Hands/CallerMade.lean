-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/CallerMade.lean: `CallerAt` (TiePaid.lean), put together at the caller as it
is made of a place's numbers r (`SwRow`), general in r.
`CallerAt` asks five things of the typed caller's letters and of a public frame W₀. Here the group
is `(rowsAt r H t₀ oM oZ).keep r.kp` (K2Caller/Row.lean; `selR` of K2Caller/LawAt.lean), and the
three readings of a slot are those of `slotsEquiv` (K2Caller/SlotsOfFrame.lean).
`codesAt r W₀`: A TEST on r and the frame: the stage's two codes are the frame's two.
`memAt`, `rowAt`, `plAt`: a slot's place in W₀.kept, its row, the entry of W₀.kept at that place.
`slots_made`: `SlotsAll` at these three, under the test `SwRow.keptAt`: `slotsAll_frame` carried
along `slotsEquiv` by `slotsAll_equiv` (FrontPub.lean).
`callerAt_made`: `CallerAt`, under the two tests, at the two maps of names that
`Johnson.Top.H.iJ` and `iQ` make of a proof F₀ of `Fit`: the clauses mapJ and mapQ then hold by
definition.
Limits. The two tests and `Fit` are premises: that they hold at any r and frame is not shown
here. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.TiePaid
import Johnson.Top.H0.K2Hands.FrontPub
import Johnson.Top.H0.K2Caller.SlotsOfFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Caller

/-- **The test**: the stage's two codes are the frame's. -/
def codesAt (r : SwRow) (W : OnBytes.SwitchFrame) : Bool :=
  decide ((stageOf r.g 0).C = codeOf W.code) && decide ((stageOf r.g 0).Z = codeOf W.zk)

variable {r : SwRow} (H : r.OK) {W₀ : OnBytes.SwitchFrame} (h : r.keptAt W₀ = true)
  (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

/-- A slot's place in the frame's list of kept members. -/
noncomputable def memAt (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : ℕ :=
  (slotsEquiv H h t₀ oM oZ κ).1.val

/-- A slot's row. -/
noncomputable def rowAt (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : ℕ :=
  (slotsEquiv H h t₀ oM oZ κ).2.val

/-- The frame's entry at a slot's place. -/
noncomputable def plAt (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : OnBytes.KeptPlace :=
  W₀.kept.get (slotsEquiv H h t₀ oM oZ κ).1

/-- The row is the typed slot's own. -/
theorem rowAt_eq (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : rowAt H h t₀ oM oZ κ = κ.2.val := rfl

/-- At the slot's place the list r.kept holds the number of the slot's member. -/
theorem memAt_kept (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) :
    r.kept[memAt H h t₀ oM oZ κ]? = some κ.1.1.1.val :=
  slotsEquiv_kept H h t₀ oM oZ κ

/-- **What is asked of the kept slots, at the caller as it is made.** -/
theorem slots_made : SlotsAll ((rowsAt r H t₀ oM oZ).keep r.kp).Kp W₀ (memAt H h t₀ oM oZ)
    (rowAt H h t₀ oM oZ) (plAt H h t₀ oM oZ) :=
  slotsAll_equiv (slotsEquiv H h t₀ oM oZ) (slotsAll_frame W₀)

/-- **`CallerAt`, put together.** -/
theorem callerAt_made (hc : codesAt r W₀ = true)
    (F₀ : Fit r.cs r.l (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
      (plAt H h t₀ oM oZ)) :
    CallerAt ((rowsAt r H t₀ oM oZ).keep r.kp) r.cs r.l
      (Johnson.Top.H.iJ (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
        (plAt H h t₀ oM oZ) r.cs r.l F₀.nameJ)
      (Johnson.Top.H.iQ (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ) r.cs r.l
        F₀.nameQ)
      (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ) (plAt H h t₀ oM oZ) W₀ := by
  unfold codesAt at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1, hc.2, slots_made H h t₀ oM oZ, fun _ => rfl, fun _ => rfl⟩

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.slots_made
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_made
