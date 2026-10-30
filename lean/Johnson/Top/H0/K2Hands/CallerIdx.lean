-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/CallerIdx.lean: `CallerAt` (TiePaid.lean) at three readings of a kept slot
that are written out: the member's place in the list r.kept, the slot's own row, the frame's entry
at that place.
CallerMade.lean reads a slot through `slotsEquiv` (K2Caller/SlotsOfFrame.lean).
`memAt_idx`, `rowAt_eq` (CallerMade.lean), `plAt_getD`: these readings are: `r.kept.idxOf` of the
member's number; the slot's second part; `W.kept.getD` at that place, whatever the default.
`memI`, `rowI`, `plI`: the three readings under names, with the default entry of six zeros.
`slots_idx`, `fit_idx`: `SlotsAll` (Numbering.lean) and `Fit` (Johnson/Top/H/SwitchMapsFit.lean) at
them, under the tests `SwRow.keptAt` and `fitAt`.
`callerAt_idx`: `CallerAt` at them, on the three tests. `callerAt_renumbered_idx`: the same at the
frame with other numbers of messages (CallerRenumber.lean). `plRe_idx`: the renumbered third
reading is the third reading at the renumbered frame.
Limits. The tests are premises. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.CallerRenumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller

variable {r : SwRow} (H : r.OK) {W : SwitchFrame} (h : r.keptAt W = true)
  (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

/-- A slot's place is the place of its member's number in the list r.kept. -/
theorem memAt_idx (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) :
    memAt H h t₀ oM oZ κ = r.kept.idxOf κ.1.1.1.val := rfl

/-- The frame's entry at a slot's place, read with a default. -/
theorem plAt_getD (d : KeptPlace) (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) :
    plAt H h t₀ oM oZ κ = W.kept.getD (r.kept.idxOf κ.1.1.1.val) d := by
  rw [← memAt_idx H h t₀ oM oZ κ]
  exact (List.getD_eq_getElem _ d (slotsEquiv H h t₀ oM oZ κ).1.isLt).symm

/-- The member's place in r.kept. -/
def memI (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : ℕ := r.kept.idxOf κ.1.1.1.val

/-- The slot's own row. -/
def rowI (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : ℕ := κ.2.val

/-- The frame's entry at the member's place. -/
def plI (W : SwitchFrame) (κ : ((rowsAt r H t₀ oM oZ).keep r.kp).Kp) : KeptPlace :=
  W.kept.getD (memI H t₀ oM oZ κ) ⟨0, 0, 0, 0, [], 0⟩

theorem memAt_is : memAt H h t₀ oM oZ = memI H t₀ oM oZ := rfl

theorem rowAt_is : rowAt H h t₀ oM oZ = rowI H t₀ oM oZ := rfl

theorem plAt_is : plAt H h t₀ oM oZ = plI H t₀ oM oZ W :=
  funext fun κ => plAt_getD H h t₀ oM oZ _ κ

include h in
/-- `SlotsAll` at the three readings. -/
theorem slots_idx : SlotsAll ((rowsAt r H t₀ oM oZ).keep r.kp).Kp W (memI H t₀ oM oZ)
    (rowI H t₀ oM oZ) (plI H t₀ oM oZ W) :=
  plAt_is H h t₀ oM oZ ▸ slots_made H h t₀ oM oZ

include h in
/-- `Fit` at the three readings. -/
theorem fit_idx (hf : fitAt r W = true) :
    Fit r.cs r.l (stageOf r.g t₀) W (memI H t₀ oM oZ) (rowI H t₀ oM oZ) (plI H t₀ oM oZ W) :=
  fit_of_test (s := stageOf r.g t₀) (slots_idx H h t₀ oM oZ) hf

/-- **`CallerAt` at the three readings, on three tests.** -/
theorem callerAt_idx (hc : codesAt r W = true) (hf : fitAt r W = true) :
    CallerAt ((rowsAt r H t₀ oM oZ).keep r.kp) r.cs r.l
      (Johnson.Top.H.iJ (stageOf r.g t₀) W (memI H t₀ oM oZ) (rowI H t₀ oM oZ)
        (plI H t₀ oM oZ W) r.cs r.l (fit_idx H h t₀ oM oZ hf).nameJ)
      (Johnson.Top.H.iQ (stageOf r.g t₀) W (memI H t₀ oM oZ) (rowI H t₀ oM oZ) r.cs r.l
        (fit_idx H h t₀ oM oZ hf).nameQ)
      (memI H t₀ oM oZ) (rowI H t₀ oM oZ) (plI H t₀ oM oZ W) W := by
  unfold codesAt at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1, hc.2, slots_idx H h t₀ oM oZ, fun _ => rfl, fun _ => rfl⟩

/-- **The same at the frame with other numbers of messages.** -/
theorem callerAt_renumbered_idx (hc : codesAt r W = true) (hf : fitAt r W = true) (g : ℕ)
    (olds anew : Array ℕ) :
    CallerAt ((rowsAt r H t₀ oM oZ).keep r.kp) r.cs r.l
      (Johnson.Top.H.iJ (stageOf r.g t₀) W (memI H t₀ oM oZ) (rowI H t₀ oM oZ)
        (plI H t₀ oM oZ W) r.cs r.l (fit_idx H h t₀ oM oZ hf).nameJ)
      (Johnson.Top.H.iQ (stageOf r.g t₀) W (memI H t₀ oM oZ) (rowI H t₀ oM oZ) r.cs r.l
        (fit_idx H h t₀ oM oZ hf).nameQ)
      (memI H t₀ oM oZ) (rowI H t₀ oM oZ)
      (plRe olds anew (memI H t₀ oM oZ) (plI H t₀ oM oZ W)) (renumber W g olds anew) :=
  callerAt_renumber _ _ _ _ _ g olds anew (callerAt_idx H h t₀ oM oZ hc hf)

include h in
/-- The renumbered reading is the renumbered frame's entry at the member's place. -/
theorem plRe_idx (g : ℕ) (olds anew : Array ℕ) :
    plRe olds anew (memI H t₀ oM oZ) (plI H t₀ oM oZ W) =
      plI H t₀ oM oZ (renumber W g olds anew) := by
  funext κ
  have m := (slotsAll_renumber g olds anew (slots_idx H h t₀ oM oZ)).member κ
  show _ = (renumber W g olds anew).kept.getD (memI H t₀ oM oZ κ) _
  rw [List.getD_eq_getElem?_getD, m]
  rfl

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.memAt_idx
#print axioms VerifiableInference.Desc.First.K2Hands.plAt_getD
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_idx
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_renumbered_idx
#print axioms VerifiableInference.Desc.First.K2Hands.plRe_idx
