-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StretchKeyFull.lean: closed facts, each by an evaluation in Lean's kernel:
where the three later proximity tests of a key file lie in the written lists of a key file's rounds
at the full size (`dryKeyFull`, Johnson/G/DryKeyLit.lean), and that the declared rounds of the three
closed places (Johnson/Desc/K12/Law/PlacesKeyFull.lean), written out, ARE these stretches. The like
of StretchFull.lean, which does it for a proof file.

Main names.
  `xsKShared`, `xsKSecond`: the written rounds of the shared and of the last chain.
  `earlierKFull`: the stand-ins for the trees of the two chains in front of the last one: 6 and 11.
  `rounds_KUFull`, `bat_KUFull`, `stretch_KUFull`, `roots_KUFull`: the folded row's test: the closed
    place has declared rounds; the shared chain's first round named "BAT" is number 8; from there on
    the written rounds are the place's, written out; three roots are sent in front.
  `…_KOFull`: Omega's test: from the second round named "BAT", number 43; seven roots in front.
  `…_KWFull`: the own test: from the last chain's first round on, which is named "BAT".
  `stretch_KUFull_no`, `stretch_KOFull_no`, `stretch_KWFull_no`: controls: one round later each
    stretch is another.
  `rootsK_first`, `rootsK_shared`: the roots that the first and the shared chain send: 6 and 11.
Limits. Two written values are compared. The written lists are what a print of the planner showed;
so are four numbers of each closed place (the trees of its first opening, the roots in front, its
first tree's number, its first group's). Their agreement here is a check of copying, no second
witness. Nothing says that a description declares these rounds. No soundness is claimed. Nothing on
hiding.

-/
import Johnson.Desc.K12.Law.StretchFull
import Johnson.Desc.K12.Law.PlacesKeyFull
import Johnson.G.DryKeyLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Member
open Johnson.G (dryKeyFull)
open OnBytes.Three (tagRoot tagRun)
open H2U (roundsOfNums batPlaces)

/-- The written rounds of a key file's shared chain. -/
def xsKShared : List Fmt.Round := dryKeyFull.2.1.map (·.1)

/-- Of its last chain. -/
def xsKSecond : List Fmt.Round := dryKeyFull.2.2.map (·.1)

/-- The closed stand-ins for the trees of the two chains in front: 6 and 11 roots. -/
def earlierKFull : List (List ByteArray × ByteArray) :=
  [((List.range 6).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]

/-! ## The folded row's test: from round 8 on -/

theorem rounds_KUFull : roundsOfNums piKUFull.nums = some (dsOf piKUFull) := by decide +kernel

theorem bat_KUFull : (batPlaces (xsKShared.map (·.entry)))[0]? = some 8 := by decide +kernel

theorem stretch_KUFull : (dsOf piKUFull).mapM (·.round []) =
    some ((xsKShared.drop 8).take (dsOf piKUFull).length) := by decide +kernel

theorem roots_KUFull : ((xsKShared.take 8).map (·.entry.roots)).sum = 3 := by decide +kernel

/-- A control: one round later the stretch is another. -/
theorem stretch_KUFull_no : ((dsOf piKUFull).mapM (·.round []) ==
    some ((xsKShared.drop 9).take (dsOf piKUFull).length)) = false := by decide +kernel

/-! ## Omega's test: from round 43 on -/

theorem rounds_KOFull : roundsOfNums piKOFull.nums = some (dsOf piKOFull) := by decide +kernel

theorem bat_KOFull : (batPlaces (xsKShared.map (·.entry)))[1]? = some 43 := by decide +kernel

theorem stretch_KOFull : (dsOf piKOFull).mapM (·.round []) =
    some ((xsKShared.drop 43).take (dsOf piKOFull).length) := by decide +kernel

theorem roots_KOFull : ((xsKShared.take 43).map (·.entry.roots)).sum = 7 := by decide +kernel

theorem stretch_KOFull_no : ((dsOf piKOFull).mapM (·.round []) ==
    some ((xsKShared.drop 44).take (dsOf piKOFull).length)) = false := by decide +kernel

/-! ## The own test: from the last chain's first round on -/

theorem rounds_KWFull : roundsOfNums piKWFull.nums = some (dsOf piKWFull) := by decide +kernel

theorem bat_KWFull : (batPlaces (xsKSecond.map (·.entry)))[0]? = some 0 := by decide +kernel

theorem stretch_KWFull : (dsOf piKWFull).mapM (·.round earlierKFull) =
    some (xsKSecond.take (dsOf piKWFull).length) := by decide +kernel

theorem stretch_KWFull_no : ((dsOf piKWFull).mapM (·.round earlierKFull) ==
    some ((xsKSecond.drop 1).take (dsOf piKWFull).length)) = false := by decide +kernel

/-! ## The roots of the two chains in front -/

theorem rootsK_first : ((dryKeyFull.1.map (·.1)).map (·.entry.roots)).sum = 6 := by
  have h : rootsE 0 dryKeyFull.1 = 6 := by decide +kernel
  rw [rootsE_eq] at h
  omega

theorem rootsK_shared : (xsKShared.map (·.entry.roots)).sum = 11 := by decide +kernel

end H2K.Member

#print axioms H2K.Member.stretch_KUFull
#print axioms H2K.Member.stretch_KOFull
#print axioms H2K.Member.stretch_KWFull
#print axioms H2K.Member.rootsK_first
