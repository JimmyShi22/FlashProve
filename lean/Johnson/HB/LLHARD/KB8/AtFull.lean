-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/AtFull.lean: the first and the shared chain's rounds of a key file's
description (`firstRoundsOf`, `sharedRoundsOf`, Chains.lean in this folder) at the typed sizes of a
key of full size (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean) are the written declared
rounds (`declKeyFull`, Written.lean). A law on the lookups, and closed statements by evaluations in
Lean's kernel.

How. A lookup's block asks the planner's own routine for its rounds. That run is not evaluated: by
`entriesG_eq` (Laws.lean) its entries are those of the plain list `lookupList`, where the setting
fits and two tests on the lookup's numbers say yes. The kernel evaluates these tests (`lookOk`), the
plain lists, the sendings', the batching's and the proximity tests' rounds, and holds the whole
against the written list by the test `==`.

Main names.
  `lookList`, `lookOk`, `looks_eq`: a lookup's rounds off the plain list; the two tests; the law.
  `fit_full`, `looks_ok_full`: the setting fits; both lookups of the full size pass.
  `rsR`, `rsU`, `rsO`; `some_R`, `some_U`, `some_O`: three proximity tests' rounds (the fourth's:
    `third_full`, Tests4.lean).
  `first_list_full`, `first_full`: the first chain: 18,851 rounds.
  `shared_full`: the shared chain: 68 rounds.
  `fit_bent`, `looks_ok_bent`: at a target of 0 bits, and with 2 ^ 32 in the prime's place, the
    tests say no.
  `first_bent`, `shared_bent`: with one row less at the ranges' test's "BAT", and with the two
    tests' rounds in the other order, the tests say no.
  `first_bent_free`, `shared_bent_first`: two values typed by hand are bent: no.
  `first_bent_look`: the lookups' own rounds (18,801 of the 18,851) are bent: no.

The counts in this head and in the comments (18,851 and 68 rounds; two lookups) are shown in
Tests4.lean (`decl_lengths`) and here (`lookups_two`).

A name that ends in `_bent`: the same test with one value changed, at which it says no: so the test
is seen to be able to fail.

Limits. Closed statements at typed and written values. That a description is made of these values
is a premise elsewhere (Row.lean). Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Chains
import Johnson.HB.LLHARD.KB8.Tests4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-! ## The lookups -/

/-- A lookup's rounds off the plain list. -/
def lookList (set : Setting) (x : Lookup) : List Fmt.DeclaredRound :=
  (lookupList set (K3.faceOfLkp x).size).map fun y => { entry := (y.round set .once).entry }

/-- The planner's two tests on a lookup's numbers. -/
def lookOk (set : Setting) (x : Lookup) : Bool :=
  let z := (K3.faceOfLkp x).size
  (decide (1 ≤ z.mu) && decide (z.mu ≤ 6) &&
      decide (2 ≤ (if z.live != 0 then z.live else 2 ^ min z.mu 6)) &&
      decide ((if z.live != 0 then z.live else 2 ^ min z.mu 6) ≤ 2 ^ min z.mu 6)) &&
    (decide (sumT ((if z.parts.isEmpty then [z.v] else z.parts).map (2 ^ ·)) <
        2 ^ (if z.live != 0 then z.live else 2 ^ min z.mu 6)) &&
      decide (2 ^ z.d * (2 ^ (if z.live != 0 then z.live else 2 ^ min z.mu 6) - 1) < set.p))

/-- One lookup: where the setting fits and it passes, its block's rounds are the plain list's. -/
theorem look_eq {set : Setting} (hf : First.Look.Made.FieldFit set .once) {x : Lookup}
    (h : lookOk set x = true) : lookRounds set x = lookList set x := by
  have h' := Bool.and_eq_true_iff.1 h
  unfold lookRounds lookList
  rw [entriesG_eq hf h'.1 h'.2, Option.getD_some, List.map_map]
  rfl

/-- **Where the setting fits and the lookups pass, their blocks' rounds are the plain lists'.** -/
theorem looks_eq {set : Setting} (hf : First.Look.Made.FieldFit set .once) :
    ∀ l : List Lookup, l.all (lookOk set) = true →
      l.flatMap (lookRounds set) = l.flatMap (lookList set)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, List.flatMap_cons, look_eq hf h.1, looks_eq hf l h.2]

/-! ## The closed statements -/

/-- The setting of the typed sizes fits what a lookup's rounds ask, at the scope "once". -/
theorem fit_full : First.Look.Made.FieldFit keyFull.set .once := by
  unfold First.Look.Made.FieldFit
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Both lookups of the full size pass the planner's two tests. -/
theorem looks_ok_full : (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).all
    (lookOk keyFull.set) = true := by decide +kernel

/-- The full size has two lookups. -/
theorem lookups_two :
    (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).length = 2 := by
  decide +kernel

/-- Not three: the test can fail. -/
theorem lookups_two_bent : decide
    ((Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).length = 3) = false := by
  decide +kernel

/-- At a target of 0 bits the setting does not fit: the test can fail. -/
theorem fit_bent : ¬ First.Look.Made.FieldFit { keyFull.set with target := 0 } .once := by
  unfold First.Look.Made.FieldFit
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With 2 ^ 32 in the prime's place the sum of all counts could wrap: the test says no. -/
theorem looks_ok_bent : (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).all
    (lookOk { keyFull.set with p := 2 ^ 32 }) = false := by decide +kernel

/-- A value that is there is what `getD` gives. -/
theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

/-- The rounds of the test on the ranges' group. -/
def rsR : List Fmt.DeclaredRound := (H2U.roundsOfNums rNums).getD []

/-- Of the test on the folded row's group. -/
def rsU : List Fmt.DeclaredRound := (H2U.roundsOfNums uNums).getD []

/-- Of the test on Omega's group. -/
def rsO : List Fmt.DeclaredRound := (H2U.roundsOfNums oNums).getD []

/-- `four_some` (Tests4.lean), place by place, for three of the four. -/
theorem four_each : ((H2U.roundsOfNums rNums).isSome = true ∧
    (H2U.roundsOfNums uNums).isSome = true) ∧ (H2U.roundsOfNums oNums).isSome = true := by
  have h := four_some
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩

/-- The ranges' test's numbers give `rsR`. -/
theorem some_R : H2U.roundsOfNums rNums = some rsR := some_getD [] four_each.1.1

/-- The folded row's test's numbers give `rsU`. -/
theorem some_U : H2U.roundsOfNums uNums = some rsU := some_getD [] four_each.1.2

/-- Omega's test's numbers give `rsO`. -/
theorem some_O : H2U.roundsOfNums oNums = some rsO := some_getD [] four_each.2

set_option maxRecDepth 1000000 in
/-- **The shared chain: 68 rounds.** -/
theorem shared_full : sharedRoundsOf keyFull rsU rsO = declKeyFull.2.1 :=
  eq_of_beq (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- With the two tests' rounds in the other order the test says no. -/
theorem shared_bent : (sharedRoundsOf keyFull rsO rsU == declKeyFull.2.1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first chain, with the lookups' rounds off the plain lists: 18,851 rounds. -/
theorem first_list_full : firstRoundsOf (lookList keyFull.set) keyFull.ranges.x keyFull.once.shape
    keyFull.once.input keyFull.codes rsR = declKeyFull.1 :=
  eq_of_beq (by decide +kernel)

/-- **The first chain: 18,851 rounds.** -/
theorem first_full : firstRoundsOf (lookRounds keyFull.set) keyFull.ranges.x keyFull.once.shape
    keyFull.once.input keyFull.codes rsR = declKeyFull.1 := by
  unfold firstRoundsOf
  rw [looks_eq fit_full _ looks_ok_full]
  exact first_list_full

set_option maxRecDepth 1000000 in
/-- With one row less at the ranges' test's "BAT" the test says no. -/
theorem first_bent : (firstRoundsOf (lookList keyFull.set) keyFull.ranges.x keyFull.once.shape
    keyFull.once.input keyFull.codes
    ((H2U.roundsOfNums { rNums with rows := 980 }).getD []) == declKeyFull.1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With 3 for 2 as the first free number at the ranges' test, a number typed by hand: no. -/
theorem first_bent_free : (firstRoundsOf (lookList keyFull.set) keyFull.ranges.x keyFull.once.shape
    keyFull.once.input keyFull.codes
    ((H2U.roundsOfNums { rNums with free := 3 }).getD []) == declKeyFull.1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With each lookup's table one bit deeper, so that the lookups' own rounds part from the written
ones: no. -/
theorem first_bent_look : (firstRoundsOf (fun x => lookList keyFull.set { x with d := x.d + 1 })
    keyFull.ranges.x keyFull.once.shape keyFull.once.input keyFull.codes rsR ==
    declKeyFull.1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the first opening's second tree left out at the folded row's test, a list typed by hand:
no. -/
theorem shared_bent_first : (sharedRoundsOf keyFull
    ((H2U.roundsOfNums { uNums with first := uNums.first.dropLast }).getD []) rsO ==
    declKeyFull.2.1) = false := by
  decide +kernel

end Johnson.KB8

#print axioms Johnson.KB8.look_eq
#print axioms Johnson.KB8.looks_eq
#print axioms Johnson.KB8.fit_full
#print axioms Johnson.KB8.looks_ok_full
#print axioms Johnson.KB8.lookups_two
#print axioms Johnson.KB8.lookups_two_bent
#print axioms Johnson.KB8.fit_bent
#print axioms Johnson.KB8.looks_ok_bent
#print axioms Johnson.KB8.some_getD
#print axioms Johnson.KB8.four_each
#print axioms Johnson.KB8.some_R
#print axioms Johnson.KB8.some_U
#print axioms Johnson.KB8.some_O
#print axioms Johnson.KB8.shared_full
#print axioms Johnson.KB8.shared_bent
#print axioms Johnson.KB8.first_list_full
#print axioms Johnson.KB8.first_full
#print axioms Johnson.KB8.first_bent
#print axioms Johnson.KB8.first_bent_free
#print axioms Johnson.KB8.first_bent_look
#print axioms Johnson.KB8.shared_bent_first
