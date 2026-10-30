-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Coef.lean
(kind K9's soundness lemma): THEOREMS: a step that stands between the adding and the
door, and writes into the ledger's arrays, leaves the ledger's sums alone.
  core_onRow     HTailF2.onRow with a function that turns neither L nor L0 of a virtual row keeps
                 core (Law/Stages.lean): the sums, chi, the count of claims, the plan's number.
  core_coefBody  coefBody (Johnson/Desc/First/TailClaims/Coefficients.lean: it sets the weights coef
                 of every virtual row and their product forms) keeps core, at every ledger.
  coefficientsP_core   so does the step coefficientsP, where it returns.
So keepsSums | KeepCore is a fact at this step, not a premise. Not claimed: that no other step
between the first adding and the door writes into the ledger: each such step owes the like.

-/
import Johnson.Desc.First.TailClaims.Coefficients
import Johnson.Desc.First.Batch.Law.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims (coefBody coefficientsP)

theorem core_onRow (F : Fork) (t r : Nat) (f : HRow → HRow)
    (hf : ∀ row, (f row).L = row.L ∧ (f row).L0 = row.L0) : core (onRow F t r f) = core F := by
  have e : (onRow F t r f).trees.map (fun X => X.rows.map fun r => (r.L, r.L0)) =
      F.trees.map fun X => X.rows.map fun r => (r.L, r.L0) := by
    unfold onRow
    dsimp only
    apply map_modify_same
    intro X
    apply map_modify_same
    intro row
    rw [(hf row).1, (hf row).2]
  unfold core sums
  rw [e]
  rfl

/-- A loop in which each step keeps a property keeps it. -/
theorem forIn_keeps {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (Id.run (f a b)).value) :
    ∀ (l : List α) (init : β), P init → P (Id.run (forIn l init f))
  | [], init, h => h
  | a :: l, init, h => by
    rw [List.forIn_cons]
    have h1 := hf a init h
    show P (match Id.run (f a init) with
      | .done b => b
      | .yield b => Id.run (forIn l b f))
    cases hq : Id.run (f a init) with
    | done b =>
      rw [hq] at h1
      exact h1
    | yield b =>
      rw [hq] at h1
      exact forIn_keeps P f hf l b h1

theorem forIn_keepsA {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (Id.run (f a b)).value) (l : Array α) (init : β) (h : P init) :
    P (Id.run (forIn l init f)) := by
  rw [← Array.forIn_toList]
  exact forIn_keeps P f hf l.toList init h

theorem run_bind_keeps {β γ : Type} (Q : β → Prop) (R : γ → Prop) (x : Id β) (f : β → Id γ)
    (hx : Q x.run) (hf : ∀ b, Q b → R (f b).run) : R (x >>= f).run := hf _ hx

/-- **The step that sets the virtual rows' weights keeps the ledger's sums, chi, the count of claims
and the plan's number.** -/
theorem core_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    core (coefBody tl g F) = core F := by
  unfold coefBody
  dsimp only
  have st : ∀ (G : Fork) (t r : Nat) (f : HRow → HRow),
      (∀ row, (f row).L = row.L ∧ (f row).L0 = row.L0) → core G = core F →
      core (onRow G t r f) = core F := fun G t r f hf hG => (core_onRow G t r f hf).trans hG
  refine run_bind_keeps (fun G => core G = core F) (fun G => core G = core F) _ _ ?_ ?_
  · refine forIn_keeps (fun G => core G = core F) _ (fun n b hb => ?_) _ _ rfl
    dsimp only
    split
    · split
      · exact st _ _ _ _ (fun row => ⟨rfl, rfl⟩) hb
      · exact hb
    · exact hb
  intro r1 h1
  refine run_bind_keeps (fun G => core G = core F) (fun G => core G = core F) _ _ ?_ ?_
  · refine forIn_keeps (fun G => core G = core F) _ (fun q b hb => ?_) _ _ h1
    refine run_bind_keeps (fun G => core G = core F)
      (fun (s : ForInStep Fork) => core s.value = core F) _ _ ?_ (fun b' hb' => hb')
    refine forIn_keepsA (fun G => core G = core F) _ (fun p b' hb' => ?_) _ _ hb
    exact st _ _ _ _ (fun row => ⟨rfl, rfl⟩) hb'
  intro r2 h2
  refine run_bind_keeps (fun G => core G = core F) (fun G => core G = core F) _ _ ?_ ?_
  · refine forIn_keeps (fun G => core G = core F) _ (fun e b hb => ?_) _ _
      (st _ _ _ _ (fun row => ⟨rfl, rfl⟩) (st _ _ _ _ (fun row => ⟨rfl, rfl⟩) h2))
    exact st _ _ _ _ (fun row => ⟨rfl, rfl⟩) hb
  intro r3 h3
  refine run_bind_keeps (fun G => core G = core F) (fun G => core G = core F) _ _ ?_
    (fun b hb => hb)
  refine forIn_keeps (fun G => core G = core F) _ (fun mu b hb => ?_) _ _
    (st _ _ _ _ (fun row => ⟨rfl, rfl⟩) h3)
  exact st _ _ _ _ (fun row => ⟨rfl, rfl⟩) hb

/-- The step, where it returns. -/
theorem coefficientsP_core (tl : HTailF2) (F G : Fork) (h : coefficientsP tl F = .ok G) :
    core G = core F := by
  unfold coefficientsP at h
  split at h
  · simp at h
  · rw [← Except.ok.inj h]
    exact core_coefBody tl _ F

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.core_coefBody
#print axioms VerifiableInference.Desc.K9L.coefficientsP_core
