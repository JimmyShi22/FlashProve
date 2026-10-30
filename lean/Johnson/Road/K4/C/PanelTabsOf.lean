-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelTabsOf.lean: CONDITIONAL.

What is here. The honest side's function that lays a panel's two sides as tables (`panelTabs`,
Johnson/Desc/K4/Honest/Stack.lean) returns wherever the verifier's own step over that panel at the
end of the batched sumcheck returns (`stackEndOf`, OnBytes/Model/LayerPanels.lean), the panel has a
first weight claim or a B side, and each form that the panel holds is valued (`panelTabs_there` over
`there_of_end`). Where the verifier's step does not refuse, neither does the honest side's function
(the converse is not shown); the places of refusal that are held against each other: a panel with
the selector, or with a never-sent vector, without a first weight claim; a panel of forms without an
A side; a form that a side does not return at a row and a column of the panel. `PanelThere` says
that none of these is met; `there_of_end` reads it off the verifier's step's return, with the
library's foldlM_each (Johnson/Road/FormsKeysEnd.lean), whose stackEnd_each has a step's return for
each panel wherever the whole end returns.

  `PanelThere b`   what a panel must hold for its two tables to be made.
  `there_of_end`   PanelThere where the verifier's step returns.
  `grid_in`   a place of a table of ni rows and ny columns: its row and column lie in the panel.
  `panelTabs_there`   the two tables are made.

Not shown here. That the verifier's step returns (h); that the panel has a first weight claim or a B
side (hH); that each form is valued (hX, hA, hB): hypotheses. What the tables hold. No example is
known. Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.C.RowMapsOf
import Johnson.Desc.K4.Honest.Stack
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay SBlk StackEnd stackEndOf)
open OnBytes.Desc.First.K4.Honest (Sides Tab panelTabs)

/-- **What a panel must hold for its two tables to be made.** This defines a hypothesis; the
definition claims nothing. -/
structure PanelThere (b : SBlk) : Prop where
  /-- a panel with the selector has a first weight claim -/
  triV : b.tri = true → b.v0.isSome = true
  /-- so has a panel with a never-sent vector -/
  virtV : b.tri = false → b.virt.isSome = true → b.v0.isSome = true
  /-- a panel of forms has an A side, which returns at each row and column -/
  sideA : b.tri = false → b.virt = none →
    ∃ A, b.A = some A ∧ ∀ i yv, i < b.ni → yv < b.ny → (A i yv).isSome = true
  /-- without a first weight claim it has a B side, which returns likewise -/
  sideB : b.tri = false → b.virt = none → b.v0 = none →
    ∃ B, b.B = some B ∧ ∀ i yv, i < b.ni → yv < b.ny → (B i yv).isSome = true

/-- **PanelThere WHERE THE VERIFIER's STEP RETURNS.** CONDITIONAL: on hH and h. -/
theorem there_of_end {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {s s' : StackEnd}
    {b : SBlk} (hH : b.v0.isSome = true ∨ b.B.isSome = true)
    (h : stackEndOf y rs lam om H1 V s b = some s') : PanelThere b := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  unfold stackEndOf at h
  dsimp only at h
  split at h
  · cases h
  cases tri with
  | true =>
    refine ⟨fun _ => ?_, (fun e => by cases e), (fun e => by cases e), (fun e => by cases e)⟩
    cases v0 with
    | none => cases h
    | some a => rfl
  | false =>
    cases virt with
    | some k =>
      refine ⟨(fun e => by cases e), fun _ _ => ?_, (fun _ e => by cases e),
        (fun _ e => by cases e)⟩
      cases v0 with
      | none => cases h
      | some a => rfl
    | none =>
      cases A with
      | none => cases h
      | some A =>
        have step : ∀ i yv, i < ni → yv < ny → (A i yv).isSome = true ∧
            (v0 = none → ∀ B', B = some B' → (B' i yv).isSome = true) := by
          intro i yv hi hy
          obtain ⟨s1, s2, h1⟩ := foldlM_each _ _ _ _ h i (List.mem_range.mpr hi)
          obtain ⟨s3, h3, _⟩ := bind_some h1
          obtain ⟨s4, s5, h5⟩ := foldlM_each _ _ _ _ h3 yv (List.mem_range.mpr hy)
          obtain ⟨a, ha, h6⟩ := bind_some h5
          refine ⟨by rw [ha]; rfl, fun e0 B' eB => ?_⟩
          subst e0
          subst eB
          obtain ⟨c, hc, _⟩ := bind_some h6
          rw [hc]
          rfl
        refine ⟨(fun e => by cases e), (fun _ e => by cases e),
          fun _ _ => ⟨A, rfl, fun i yv hi hy => (step i yv hi hy).1⟩, fun _ _ e0 => ?_⟩
        have e0' : v0 = none := e0
        subst e0'
        cases B with
        | none => rcases hH with e | e <;> cases e
        | some B' => exact ⟨B', rfl, fun i yv hi hy => (step i yv hi hy).2 rfl B' rfl⟩

/-- A place of a table of ni rows and ny columns: its row and its column lie in the panel. -/
theorem grid_in {ni ny x : ℕ} (hx : x < ni * ny) : x / ny < ni ∧ x % ny < ny := by
  have h0 : 0 < ny := by
    rcases Nat.eq_zero_or_pos ny with e | e
    · rw [e, Nat.mul_zero] at hx
      exact absurd hx (Nat.not_lt_zero _)
    · exact e
  exact ⟨(Nat.div_lt_iff_lt_mul h0).mpr hx, Nat.mod_lt _ h0⟩

/-- **A PANEL's TWO TABLES ARE MADE.** CONDITIONAL: on every hypothesis named. -/
theorem panelTabs_there (S : Sides) (val : Aff → Option E) (om : Array E) (F : Array (Array E))
    (hZ hR : Tab) {b : SBlk} (T : PanelThere b)
    (hX : ∀ yv, (val (b.xx.getD yv {})).isSome = true)
    (hA : ∀ A i yv f, b.A = some A → A i yv = some f → (val f).isSome = true)
    (hB : ∀ B i yv f, b.B = some B → B i yv = some f → (val f).isSome = true) :
    ∃ x, panelTabs S val om F hZ hR b = some x := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  cases tri with
  | true =>
    cases v0 with
    | none => exact absurd (T.triV rfl) (by simp)
    | some v0 =>
      cases virt with
      | some k =>
        obtain ⟨cols, hc⟩ := amapM_there
          (g := fun yv => some (hR.getD (S.routedAt (k - 1) yv) zeroE)) (Array.range ny)
          (fun _ _ => rfl)
        exact ⟨_, Option.bind_eq_some_iff.mpr ⟨cols, hc, rfl⟩⟩
      | none =>
        obtain ⟨cols, hc⟩ := amapM_there (g := fun yv => val (xx.getD yv {})) (Array.range ny)
          (fun yv _ => hX yv)
        exact ⟨_, Option.bind_eq_some_iff.mpr ⟨cols, hc, rfl⟩⟩
  | false =>
    cases virt with
    | some k =>
      cases v0 with
      | none => exact absurd (T.virtV rfl rfl) (by simp)
      | some v0 => exact ⟨_, rfl⟩
    | none =>
      obtain ⟨A', eA, rA⟩ := T.sideA rfl rfl
      have eA' : A = some A' := eA
      subst eA'
      obtain ⟨a, ha⟩ := amapM_there (g := fun x => do
          pure (mulE (mulE (mulE (om.getD claim zeroE) ec) (wt.getD (x / ny) zeroE))
            (← val (← A' (x / ny) (x % ny))))) (Array.range (ni * ny)) (fun x hx => by
        have hx' : x < ni * ny := by simpa using hx
        obtain ⟨p1, p2⟩ := grid_in hx'
        obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (rA _ _ p1 p2)
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hA A' _ _ f rfl hf)
        show (do
          pure (mulE (mulE (mulE (om.getD claim zeroE) ec) (wt.getD (x / ny) zeroE))
            (← val (← A' (x / ny) (x % ny)))) : Option E).isSome = true
        rw [hf]
        show (do
          pure (mulE (mulE (mulE (om.getD claim zeroE) ec) (wt.getD (x / ny) zeroE))
            (← val f)) : Option E).isSome = true
        rw [hz]
        rfl)
      cases v0 with
      | some v0 =>
        exact ⟨_, Option.bind_eq_some_iff.mpr ⟨a, ha, rfl⟩⟩
      | none =>
        obtain ⟨B', eB, rB⟩ := T.sideB rfl rfl rfl
        have eB' : B = some B' := eB
        subst eB'
        obtain ⟨c, hc⟩ := amapM_there (g := fun x => do val (← B' (x / ny) (x % ny)))
          (Array.range (ni * ny)) (fun x hx => by
          have hx' : x < ni * ny := by simpa using hx
          obtain ⟨p1, p2⟩ := grid_in hx'
          obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (rB _ _ p1 p2)
          show (do val (← B' (x / ny) (x % ny)) : Option E).isSome = true
          rw [hf]
          exact hB B' _ _ f rfl hf)
        exact ⟨_, Option.bind_eq_some_iff.mpr
          ⟨a, ha, Option.bind_eq_some_iff.mpr ⟨c, hc, rfl⟩⟩⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.there_of_end
#print axioms OnBytes.Road.K4.C.grid_in
#print axioms OnBytes.Road.K4.C.panelTabs_there
