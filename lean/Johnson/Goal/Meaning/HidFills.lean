-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidFills.lean: the four numbers Fills of an attention sub-proof's shape, in
scope.

inside_of_plan (Johnson/Goal/Meaning/HidLaws.lean) has a public premise Fills S: the parts of as
have at least 7,200 columns together, and ah, ao and qa have at least 2,880, 40,960 and 98,304
features, filler counted. The first is among what eleven_of_core gives. This file shows the other
three, with equality, of the shapes Hd.shapeA X g at what publicOf returns under the public core.

Main names:
  fills_of_shape, fills_of_hid   what the verifier's functions shape and shapeHid
    (OnBytes/Model/AttentionShape.lean) lay in the three fields, as formulas of the configuration.
  fills_ref   at a configuration with the reference numbers (CfRef): 2,880, 40,960 and 98,304.
  fills_eq_of_core, fills_of_core   the three equations, and Fills (Hd.shapeA X g), for g < 12, in
    scope.
  inside_of_core   so, in scope, Inside s (Hd.shapeA X g) needs PlanSizes alone.

What is not claimed. PlanSizes: that a sub-proof's signature has the sizes of the plan's list. The
full size alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (roundUp)
open OnBytes.Model.Verify (publicOf layerShape)
open Cb.Pv.Tail (Size)

/-- The three fields, as the verifier's function shape lays them. -/
def FillsAre (cf : Attention.Cfg) (S : Attention.Shape) : Prop :=
  S.fillH = roundUp (8 * 2 ^ cf.ll * cf.H + 2 ^ cf.ll * cf.lt * cf.H) cf.wcH ∧
  S.fillO = roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) cf.wcO ∧
  S.fillQ = roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) cf.wcQ

theorem fills_of_shape {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) : FillsAre cf S := by
  unfold Attention.shape at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨Tt, hT, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨calls, _, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl, rfl⟩

theorem fills_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    FillsAre cf S := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have e := (Prod.mk.inj (Except.ok.inj h)).1
  have P := fills_of_shape hA
  subst e
  exact P

/-- At the reference numbers. -/
theorem fills_ref {cf : Attention.Cfg} {S : Attention.Shape} (P : FillsAre cf S) (hc : CfRef cf) :
    S.fillH = 2880 ∧ S.fillO = 40960 ∧ S.fillQ = 98304 := by
  obtain ⟨a, b, c⟩ := P
  rw [hc.ll, hc.H, hc.lt, hc.wcH] at a
  rw [hc.ll, hc.H, hc.ldh, hc.wcO] at b
  rw [hc.ll, hc.H, hc.ldh, hc.lgk, hc.wcQ] at c
  exact ⟨a.trans (by decide), b.trans (by decide), c.trans (by decide)⟩

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- In scope the three numbers are the library's. -/
theorem fills_eq_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    ∀ g < 12, (Hd.shapeA X g).fillH = 2880 ∧ (Hd.shapeA X g).fillO = 40960 ∧
      (Hd.shapeA X g).fillQ = 98304 := by
  intro g hg
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have F := Hd.fillRef_of_core C B
  obtain ⟨lines, A0, seenG, seenA, -, H⟩ := Hd.groups_of_public h B.p4
  obtain ⟨Xg, Ag, s, hG, -, -, -, -, -, -, -, eS⟩ := H g (by rw [B.groups]; exact hg)
  obtain ⟨cf, hf, hp, -⟩ := group_plan hG
  obtain ⟨hc, -, -, -⟩ := cfRef_of_fill hf F
  rw [eS]
  exact fills_ref (fills_of_hid (plan_shape hp).1) hc

/-- **In scope the shapes of the twelve attention sub-proofs meet Fills.** -/
theorem fills_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    ∀ g < 12, Fills (Hd.shapeA X g) := by
  intro g hg
  obtain ⟨a, b, c⟩ := fills_eq_of_core h C g hg
  refine ⟨(Hd.eleven_of_core h C (Hd.npOf X.hS)).2.2.2.2 g hg, ?_, ?_, ?_⟩
  · rw [a]
  · rw [b]
  · rw [c]

/-- **In scope every valid name's place lies within the sizes of the plan's list.** -/
theorem inside_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) {s : Size} (P : PlanSizes s (Hd.shapeA X g)) : Inside s (Hd.shapeA X g) :=
  inside_of_plan ((Hd.eleven_of_core h C (Hd.npOf X.hS)).2.1 g hg) (fills_of_core h C g hg) P

end Core

end Meaning

#print axioms Meaning.fills_of_shape
#print axioms Meaning.fills_of_hid
#print axioms Meaning.fills_ref
#print axioms Meaning.fills_eq_of_core
#print axioms Meaning.fills_of_core
#print axioms Meaning.inside_of_core
