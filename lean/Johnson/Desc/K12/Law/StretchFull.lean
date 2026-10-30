-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StretchFull.lean: the declared rounds of three closed places of a proximity
test (the kind K12) at the full size, as readers take them, are stretches of the written
lists of the proof file's rounds; by the kernel.

Why. WrittenOfG.lean's `writtenOf_at_stretch` asks of a closed place that readers take of its
declared rounds just a given stretch of what they take of a chain. In the goals' scope a
description's chains, written out, are the lists `Johnson.G.dryProofFull`
(Johnson/G/DryProofLit.lean). This file has the closed facts at these lists.
Main names:
  `xsShared`, `xsSecond`: what readers take of the shared and of the second chain's written list.
    `earlierFull`: the closed stand-ins for the two earlier chains (83 and 11 roots). `dsOf p`: a
    closed place's declared rounds.
  At `piUFull` (the folded row's test): `rounds_UFull`: it has declared rounds. `bat_UFull`: the
    shared chain's first round "BAT" is number 8. `stretch_UFull`: readers take of its declared
    rounds the stretch from 8 on. `roots_UFull`: the rounds in front send 3 roots.
    `stretch_UFull_no`: a control: not the stretch from 9 on.
  At `piOFull` (Omega's test): the like: the second "BAT" is number 43; 7 roots in front.
  At `piWFull` (the request's own test): the like from the second chain's first round on.
  `rootsE`, `roots_first`, `roots_shared`: the first chain's rounds send 83 roots, the shared
    chain's 11.
What it adds to PlacesFull.lean: that file's three places were made by a program off a run's print.
Here their declared rounds are held against DryProofLit.lean's literals by the kernel.
Limits: these lists are themselves what a print showed (DryProofLit.lean's head says against
what they were held). Not the first chain's last test: by evaluation its 33 declared rounds are the
stretch from round 48,237 on, with 77 roots in front; no kernel line. The full size only. Nothing on
soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.WrittenOfDecl
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Plan.PlaceOfPlan
import Johnson.G.DryProofLit
import Johnson.G.Eager

set_option autoImplicit false
namespace H2K.Member
open Johnson.G (dryProofFull)
open OnBytes.Three (tagRoot tagRun)
open H2U (roundsOfNums batPlaces)

/-- What readers take of the shared chain's and of the second chain's written list. -/
def xsShared : List Fmt.Round := dryProofFull.2.1.map (·.1)
def xsSecond : List Fmt.Round := dryProofFull.2.2.map (·.1)

/-- The closed stand-ins for the two earlier chains: 83 and 11 roots. -/
def earlierFull : List (List ByteArray × ByteArray) :=
  [((List.range 83).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]

/-- The declared rounds of a closed place; none where there are none. -/
def dsOf (p : VerifiableInference.Desc.K12.P12) : List Fmt.DeclaredRound :=
  (roundsOfNums p.nums).getD []

/-! ## The folded row's test: from round 8 on, 35 rounds -/

theorem rounds_UFull : roundsOfNums piUFull.nums = some (dsOf piUFull) := by decide +kernel

theorem bat_UFull : (batPlaces (xsShared.map (·.entry)))[0]? = some 8 := by decide +kernel

theorem stretch_UFull : (dsOf piUFull).mapM (·.round []) =
    some ((xsShared.drop 8).take (dsOf piUFull).length) := by decide +kernel

theorem roots_UFull : ((xsShared.take 8).map (·.entry.roots)).sum = 3 := by decide +kernel

/-- A control: one round later the stretch is another. -/
theorem stretch_UFull_no : ((dsOf piUFull).mapM (·.round []) ==
    some ((xsShared.drop 9).take (dsOf piUFull).length)) = false := by decide +kernel

/-! ## Omega's test: from round 43 on, 24 rounds -/

theorem rounds_OFull : roundsOfNums piOFull.nums = some (dsOf piOFull) := by decide +kernel

theorem bat_OFull : (batPlaces (xsShared.map (·.entry)))[1]? = some 43 := by decide +kernel

theorem stretch_OFull : (dsOf piOFull).mapM (·.round []) =
    some ((xsShared.drop 43).take (dsOf piOFull).length) := by decide +kernel

theorem roots_OFull : ((xsShared.take 43).map (·.entry.roots)).sum = 7 := by decide +kernel

theorem stretch_OFull_no : ((dsOf piOFull).mapM (·.round []) ==
    some ((xsShared.drop 44).take (dsOf piOFull).length)) = false := by decide +kernel

/-! ## The request's own test: from the second chain's first round on -/

theorem rounds_WFull : roundsOfNums piWFull.nums = some (dsOf piWFull) := by decide +kernel

theorem stretch_WFull : (dsOf piWFull).mapM (·.round earlierFull) =
    some (xsSecond.take (dsOf piWFull).length) := by decide +kernel

theorem stretch_WFull_no : ((dsOf piWFull).mapM (·.round earlierFull) ==
    some ((xsSecond.drop 1).take (dsOf piWFull).length)) = false := by decide +kernel

/-! ## The first chain's roots: 83 -/

/-- a plus the roots that the rounds send; each sum is made before the next step (`force`,
Johnson/G/Eager.lean), so that the kernel gets through a long list. -/
def rootsE : Nat → OnBytes.Params.Rounds → Nat
  | a, [] => a
  | a, x :: xs => Johnson.G.force (a + x.1.entry.roots) fun v => rootsE v xs

theorem rootsE_eq (l : OnBytes.Params.Rounds) :
    ∀ a, rootsE a l = a + ((l.map (·.1)).map (·.entry.roots)).sum := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    simp only [rootsE, Johnson.G.force_eq, ih, List.map_cons, List.sum_cons]
    omega

set_option maxRecDepth 1000000 in
theorem roots_first : ((dryProofFull.1.map (·.1)).map (·.entry.roots)).sum = 83 := by
  have h : rootsE 0 dryProofFull.1 = 83 := by decide +kernel
  rw [rootsE_eq] at h
  omega

theorem roots_shared : (xsShared.map (·.entry.roots)).sum = 11 := by decide +kernel

end H2K.Member

#print axioms H2K.Member.roots_first
#print axioms H2K.Member.stretch_UFull
#print axioms H2K.Member.stretch_OFull
#print axioms H2K.Member.stretch_WFull
#print axioms H2K.Member.bat_UFull
#print axioms H2K.Member.roots_OFull
