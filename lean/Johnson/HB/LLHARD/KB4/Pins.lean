-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Pins.lean: what the tests on a key file's plan read of X, N and P as written
values: one structure of named equations; and what follows from it by rewriting.

Main names.
  Pins X N P: twenty-three equations: the seven items as read back beside the plans; the three plans
  as read back; the five values by which the declared rounds and the tenants were cut; the declared
  rounds; the tenants as told; the setting; the planner's sized key and its three plans for the key;
  that the planner holds the same three chains as read; N and P.
  slimK_of, slimY_of, slimC_of: so the slim values (Slim.lean) are the written ones
  (SourceW.lean).
  chainPins_of: Pins gives ChainPins (Frame.lean); its field "front", the shared chain's front's own
  six tests, is DERIVED here (front_W, CFile.lean).
  kb8Pins_of: Pins gives the smaller structure KB8.Pins.
Limits. Every field is a premise for whoever uses a theorem over Pins. Not read as written values,
and so no fields: the three chains' parameter bytes, the digest, the items' bytes, the units of
rows. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Frame
import Johnson.HB.LLHARD.KB4.CFile
import Johnson.HB.LLHARD.KB8.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- **What the tests on the plan read of X, N and P as written values.** -/
structure Pins (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : Prop where
  /-- the seven items as read back beside the plans -/
  idx : X.Y.k.oneTime.indexMasks = keyFull.once.input
  ranges : X.Y.k.oneTime.ranges = keyFull.ranges.x
  binding : X.Y.k.oneTime.binding = keyFull.binding
  codes₁ : X.Y.k.oneTime.codes = keyFull.codes
  lin₁ : X.Y.k.oneTime.lin = keyFull.once.shape
  codes₂ : X.Y.k.shared.codes = keyFull.codes
  lin₂ : X.Y.k.shared.lin = keyFull.once.shape
  /-- the three plans as read back -/
  plan₁ : X.Y.k.oneTime.given.plan = keyThree.A.plan.plan
  plan₂ : X.Y.k.shared.given.plan = keyThree.B.plan.plan
  plan₃ : X.Y.k.second.given.plan = keyThree.C.plan.plan
  /-- what the declared rounds and the tenants were cut by -/
  cutShape : X.Y.cutShape = keyFull.once.shape
  cutCodes : X.Y.cutCodes = (keyFull.codes, keyFull.codes, keyFull.codes)
  cutIdx : X.Y.cutIdx = keyFull.once.input
  cutRanges : X.Y.cutRanges = keyFull.ranges.x
  cutSamples : X.Y.cutSamples = recordSet.samples
  /-- the declared rounds and the tenants as told -/
  D : X.Y.D = declKeyFull
  told : X.Y.told = toldKeyFull
  /-- the setting; the planner's sized key and its three plans; its copy of the chains as read -/
  set : X.set = keyFull.set
  sized : X.chains.made.sized.key = keyFull
  plans : X.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan]
  same : X.chains.key = X.Y.k
  /-- the four places' numbers -/
  N : N = rangesNumsFull
  P : P = laterPlacesFull

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem slimK_of (h : Pins X N P) : slimK X.Y.k = kW := by
  unfold slimK kW
  rw [h.plan₁, h.idx, h.ranges, h.binding, h.codes₁, h.lin₁, h.plan₂, h.codes₂, h.lin₂, h.plan₃]

theorem slimY_of (h : Pins X N P) : slimY X.Y = YW := by
  unfold slimY YW
  rw [slimK_of h, h.cutShape, h.cutCodes, h.cutIdx, h.cutRanges, h.cutSamples, h.D, h.told]

theorem slimC_of (h : Pins X N P) : slimC X.chains = chainsW := by
  unfold slimC chainsW
  rw [h.sized, h.plans, h.same, slimK_of h]

/-- The first written plan's answers to a sample are the written setting's. -/
theorem samples_W : keyThree.A.plan.plan.samples = recordSet.samples := by decide +kernel

theorem front_of (h : Pins X N P) : sharedFrontOk X.chains = true := by
  rw [front_slim, slimC_of h]
  exact front_W

theorem chainPins_of (h : Pins X N P) : ChainPins X N P where
  samples := by rw [h.plan₁]; exact samples_W
  idx := h.idx
  ranges := h.ranges
  codes := h.codes₁
  lin := h.lin₁
  D₁ := congrArg (·.1) h.D
  told₁ := congrArg (·.1) h.told
  set := h.set
  sized := h.sized
  front := front_of h
  N := h.N
  P := h.P

theorem kb8Pins_of (h : Pins X N P) : Johnson.KB8.Pins X N P where
  set := h.set
  ranges := h.ranges
  lin := h.lin₁
  idx := h.idx
  codes := h.codes₁
  sized := h.sized
  nC := by rw [h.N]; rfl
  nN := by rw [h.N]; rfl
  uC := by rw [h.P]; rfl
  uN := by rw [h.P]; rfl
  o := ⟨laterPlacesFull.O.getD rangesNumsFull, by rw [h.P]; rfl, rfl, rfl⟩
  wC := by rw [h.P]; rfl
  wN := by rw [h.P]; rfl

end Johnson.KB4

#print axioms Johnson.KB4.slimK_of
#print axioms Johnson.KB4.slimY_of
#print axioms Johnson.KB4.slimC_of
#print axioms Johnson.KB4.samples_W
#print axioms Johnson.KB4.front_of
#print axioms Johnson.KB4.chainPins_of
#print axioms Johnson.KB4.kb8Pins_of
