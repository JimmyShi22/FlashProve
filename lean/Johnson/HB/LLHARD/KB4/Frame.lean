-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Frame.lean: under named equations on what it is made of, a key file's
description (Key.descriptionFromSource X N P, Johnson/Desc/Key/Desc.lean) has the three chains of the closed
description WK (WK.lean): equations of chains. General in X, N and P.

Main names.
  ChainPins X N P: what the three chains read of X, N and P, as equations to written values: of the
  one-time chain's values as read back the number of answers, the index-mask message's notice, the
  item "ranges", the codes and the shape; the first chain's declared rounds and tenants as told; the
  setting; the planner's sized key; that the shared chain's front says yes; N and P whole.
  first_of, shared_of, second_of: (Key.descriptionFromSource X N P).first = WK.first, and the like.
  roots_of, places_of: so what the blocks say of the roots, and the table of places, are WK's.
Limits. The equations are premises: what is meant to give each is said in PinsOfMade.lean's head
(Pins gives ChainPins: chainPins_of, Pins.lean). ChainPins is met by a closed source (another file);
that it is met at what Key.sourceOf, Key.rangesNumbers and Key.laterPlaces return at any public
files is shown nowhere here. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- **What the three chains read of X, N and P, as equations.** -/
structure ChainPins (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : Prop where
  /-- five fields of the one-time chain's public values, as read back -/
  samples : X.Y.k.oneTime.given.plan.samples = recordSet.samples
  idx : X.Y.k.oneTime.indexMasks = keyFull.once.input
  ranges : X.Y.k.oneTime.ranges = keyFull.ranges.x
  codes : X.Y.k.oneTime.codes = keyFull.codes
  lin : X.Y.k.oneTime.lin = keyFull.once.shape
  /-- the first chain's declared rounds and tenants as told -/
  D₁ : X.Y.D.1 = declKeyFull.1
  told₁ : X.Y.told.1 = toldKeyFull.1
  /-- the setting, and the planner's sized key -/
  set : X.set = keyFull.set
  sized : X.chains.made.sized.key = keyFull
  /-- the shared chain's front's six tests on the plan -/
  front : sharedFrontOk X.chains = true
  /-- the four places' numbers -/
  N : N = rangesNumsFull
  P : P = laterPlacesFull

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem first_of (h : ChainPins X N P) : (descriptionFromSource X N P).first = WK.first := by
  show firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N = firstW
  rw [firstChain_at, h.samples, h.idx, h.ranges, h.codes, h.lin, h.D₁, h.told₁, h.set, h.N]
  exact firstFull_eq

theorem shared_of (h : ChainPins X N P) : (descriptionFromSource X N P).shared = WK.shared := by
  show (sharedChain X.chains P).retype = sharedFull
  rw [sharedChain_eq, h.sized, h.front, h.P]
  rfl

theorem second_of (h : ChainPins X N P) : (descriptionFromSource X N P).second = WK.second := by
  show (thirdChain X.chains P).retype = thirdFull
  rw [thirdChain_eq, h.sized, h.P]
  rfl

theorem decl_of (h : ChainPins X N P) : (descriptionFromSource X N P).roundsDeclaredByBlocks = declKeyFull := by
  unfold FileDescription.roundsDeclaredByBlocks
  rw [first_of h, shared_of h, second_of h]
  exact WK_decl

theorem roots_of (h : ChainPins X N P) : (descriptionFromSource X N P).roots = WK.roots := by
  unfold FileDescription.roots
  rw [first_of h, shared_of h, second_of h]
  rfl

theorem places_of (h : ChainPins X N P) : (descriptionFromSource X N P).places = WK.places := by
  unfold FileDescription.places
  rw [first_of h, shared_of h, second_of h]
  rfl

end Johnson.KB4

#print axioms Johnson.KB4.first_of
#print axioms Johnson.KB4.shared_of
#print axioms Johnson.KB4.second_of
#print axioms Johnson.KB4.decl_of
#print axioms Johnson.KB4.roots_of
#print axioms Johnson.KB4.places_of
