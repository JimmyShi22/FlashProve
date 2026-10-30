-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttPlan.lean

From the plan of an attention sub-proof to its shape, in the verifier's own calls: what the
functions "plan" (OnBytes/Model/AttentionPlan.lean) and "group" (OnBytes/Model/AttentionConfig.lean)
have called when they return a plan.

* "plan_shape": plan settings i cf = .ok X: the shape and the lookup's numbers in X are what
  shapeHid returns for cf, and X keeps what the caller passed.
* "group_plan": group P y sc midQ lines g = .ok X: the configuration is what fill returns, X is what
  plan returns for it, and the shape has as many layers in a group as the layers' layout.
* "shaped_of_group": so the fields of X.S are functions of that configuration ("Shaped",
  Johnson/Road/Lane5AttShape.lean).

Only what is named here is read off the two functions; their other tests are not looked at.
-/
import Johnson.Road.Lane5AttShape
import OnBytes.Model.AttentionConfig

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

/-- If "refuse under a condition, then go on" returns a value, the condition is false and what
follows returns the value. -/
theorem jp_ok {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = Except.ok y) :
    ¬ c ∧ jp PUnit.unit = Except.ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = Except.ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- The same for the verifier's refuseIf. -/
theorem refuse_ok {β : Type} {b : Bool} {n : String} {f : Unit → Except String β} {y : β}
    (h : Model.refuseIf b n >>= f = Except.ok y) : b = false ∧ f () = Except.ok y := by
  cases b with
  | true =>
    have h' : (Except.error n : Except String β) = Except.ok y := h
    cases h'
  | false => exact ⟨rfl, h⟩

/-- **What plan has called.** -/
theorem plan_shape {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings i cf = Except.ok X) :
    Attention.shapeHid settings.lidb cf = Except.ok (X.S, X.fs) ∧ X.inp = i := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam0, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨hr, rfl⟩

/-- **What group has called.** -/
theorem group_plan {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (h : Attention.group P y sc midQ lines g = Except.ok X) :
    ∃ cf, Attention.fill P y sc lines g = Except.ok cf ∧
      Attention.plan P.settings (Attention.inOf P.settings y (midQ g) g) cf = Except.ok X ∧
      X.S.Lam = y.Lam := by
  unfold Attention.group at h
  obtain ⟨cf, hf, h⟩ := bind_ok h
  obtain ⟨X', hp, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  obtain ⟨e6, h⟩ := refuse_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  refine ⟨cf, hf, hp, ?_⟩
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at e6
  exact e6.1.1.1.1

/-- The fields of the shape in a group's plan are functions of the configuration that fill
returns. -/
theorem shaped_of_group {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (h : Attention.group P y sc midQ lines g = Except.ok X) :
    ∃ cf, Attention.fill P y sc lines g = Except.ok cf ∧ Shaped cf X.S ∧ X.S.Lam = y.Lam ∧
      X.inp = Attention.inOf P.settings y (midQ g) g := by
  obtain ⟨cf, hf, hp, hL⟩ := group_plan h
  exact ⟨cf, hf, shaped_of_hid (plan_shape hp).1, hL, (plan_shape hp).2⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.plan_shape
#print axioms OnBytes.Road.L5.group_plan
#print axioms OnBytes.Road.L5.shaped_of_group
