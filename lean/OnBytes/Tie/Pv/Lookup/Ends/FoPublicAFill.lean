-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAFill.lean.
The attention plans of a record that Verify.publicOf returns: the plan's own configuration is what
Attention.fill returns.

States:
  pubOf_sc, public_sc: the scales in the record's layers are what Layer.scalesOf returns on the file
    of scales.
  public_A_fill: Attention.fill at the record's parameter file, its layers' layout and scales, the
    call lines and the group's number returns the configuration of the group's attention plan. The
    call lines are what Attention.readLines returns on the parameter file's lines: a premise in the
    form of that equation, so that nothing stands under "there is".
  public_A_lines: that equation has a solution where the record has an attention plan.
Under: Verify.publicOf's equation; in the last two also that the plan is a member of X.A; in
public_A_fill also readLines' equation.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- Layer.Pub.of keeps the scales. -/
theorem pubOf_sc {y : Layer.Lay} {sc : Layer.Scales} {rope : Array ℕ} {wsLay : WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.sc = sc := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- The scales in the record's layers. -/
theorem public_sc (h : Verify.publicOf pol KL layout = .ok X) :
    Layer.scalesOf X.layers.y.h (fileWords KL) = .ok X.layers.sc := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := Pub.ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  show Layer.scalesOf layers.y.h (fileWords KL) = .ok layers.sc
  rw [Pub.pubOf_y k4, pubOf_sc k4]
  exact k2

/-- **The plan's own configuration is what Attention.fill returns.** -/
theorem public_A_fill (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) (lines : List Attention.Line)
    (hl : Attention.readLines X.P.polCallsA = .ok lines) :
    Attention.fill X.P X.layers.y X.layers.sc lines g = .ok a.S.cf := by
  obtain ⟨sc, lines', cf, a0, hs, hl', hf, hp, ha, _, _⟩ := Pub.public_A h g a hg
  obtain rfl : sc = X.layers.sc := Except.ok.inj (hs.symm.trans (public_sc h))
  obtain rfl : lines' = lines := Except.ok.inj (hl'.symm.trans hl)
  have eS : a.S = a0.S := by rw [ha]
  obtain ⟨hS, _⟩ := Pub.planA_shapeHid _ _ cf a0 hp
  rw [eS, (Pub2.shapeOf_shapeHid hS).2]
  exact hf

/-- The call lines are read where the record has an attention plan. -/
theorem public_A_lines (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : ∃ lines, Attention.readLines X.P.polCallsA = .ok lines := by
  obtain ⟨_, lines, _, _, _, hl, _⟩ := Pub.public_A h g a hg
  exact ⟨lines, hl⟩

end

end Fo.PubA
