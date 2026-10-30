-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PlacesKeyFull.lean: the three later places of a proximity test (the kind K12)
in the key file at the full size, as closed terms, the key file's table of codes, and the planner's
radii. Definitions alone; no theorem; no Mathlib beneath.

Why. As Johnson/Desc/K12/Law/PlacesFull.lean (the proof file's four places), for the key file's
shared and last chain. These are the plan's numbers: sizes, counts and names of trees. No state of
the verifier in a run, no drawn value and no entry of a message is here. They are other numbers than
the proof file's: 32 bits of work at each; other counts of positions; other radii.
Main names: all in the namespace `H2K.Member`.
  `piKUFull`: the folded row, at ⟨2, none, 9, .K12⟩. `piKOFull`: Omega, at ⟨2, none, 10, .K12⟩; its
    first fold sends its own mask. `piKWFull`: the own test, at ⟨3, none, 2, .K12⟩; its first switch
    opens trees of the two chains in front.
  `codesKeyFull`: the two lists of codes of the key file's sizes.
  `rKUFull`, `rKOFull`, `rKWFull`: a radius for each stage of a place, as a function of the stage:
    the planner's own radii, as the same print has them. 0 at any other stage.
Limits: THE THREE PLACES AND THE TABLE WERE MADE BY A PROGRAM OFF THE PRINT OF A RUN of Lean's
evaluator: `Johnson.G.OfPlan.madeOf` at the library's own full-size texts of the three public files
(OnBytes/Tie/Pv/Plan/PlanKits.lean, PlanLayoutFull.lean), then the key file's description's own
maker of these places, `VerifiableInference.Desc.Key.laterPlaces` (Johnson/Desc/Key/Places.lean),
each laid at its address by `H2U.proximityTestParametersAt` [the print is not in this library; its sha256 is
484719fec2a4cca4b7d83ef54c92f7a768014272d7a35cc4feef99ec85d5daa6]. THE THREE FUNCTIONS OF RADII WERE
TYPED BY HAND after the same print's lines (`radiusOf` at the key's setting, stage by stage) and
held against these lines by a program. That they are these places and radii is that run's word: no
theorem here. What of them is held against a typed value of the library by the kernel:
Johnson/Desc/K12/Law/RoundsAtKeyPlaces.lean. The key file's fourth place (the ranges' test, on its
first chain) is not here. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Join

set_option autoImplicit false
namespace H2K.Member
open VerifiableInference.Desc.K12 (P12)

/-- The key file's place of the folded row, at the full size. -/
def piKUFull : P12 :=
  { place :=
      { chain := 2, link := none, piece := 9, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 66,
        work := 32,
        stages :=
          [⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 7, 0, 97⟩,
           ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 5, 2, 52⟩,
           ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩,
           ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩,
           ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩],
        ownMask := false,
        «first» :=
          [({ a := 24, W := 324, stored := false, tree := 0 }, Fmt.TreeSource.own 0),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 3,
        firstTree := 0 },
    idx := [(0, 0), (1, 1), (2, 1), (3, 1), (4, 2)],
    oracles :=
      [[], [], [], [], [], [], [], [], [],
       [{ logLength := 21,
          words := 120,
          tenants :=
            [{ main := 96, mask := 12, degree := 3, sampled := true, groups := [2] },
             { main := 0, mask := 12, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [], [],
       [{ logLength := 17,
          words := 72,
          tenants :=
            [{ main := 48, mask := 12, degree := 3, sampled := true, groups := [3] },
             { main := 0, mask := 12, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 13,
          words := 72,
          tenants :=
            [{ main := 48, mask := 12, degree := 3, sampled := true, groups := [4] },
             { main := 0, mask := 12, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 14,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [5] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(2, 0), (2, 2)],
    answers := 1,
    early := true }

/-- The key file's place of Omega, at the full size. -/
def piKOFull : P12 :=
  { place :=
      { chain := 2, link := none, piece := 10, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 3,
        work := 32,
        stages :=
          [⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 4, 0, 49⟩,
           ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 4, 3, 49⟩,
           ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 4, 3, 49⟩,
           ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩],
        ownMask := true,
        «first» :=
          [({ a := 22, W := 36, stored := false, tree := 1 }, Fmt.TreeSource.own 1),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 7,
        firstTree := 0 },
    idx := [(5, 0), (6, 3), (7, 4), (8, 5)],
    oracles :=
      [[],
       [{ logLength := 13,
          words := 3,
          tenants :=
            [{ main := 0, mask := 3, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [],
       [{ logLength := 18,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [6] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 14,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [7] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [8] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(2, 1), (2, 2)],
    answers := 1,
    early := true }

/-- The key file's place of the own test, at the full size. -/
def piKWFull : P12 :=
  { place :=
      { chain := 3, link := none, piece := 2, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 5,
        work := 32,
        stages :=
          [⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 5, 1, 49⟩,
           ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 4, 3, 49⟩,
           ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 3, 49⟩,
           ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 3, 41⟩,
           ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩],
        ownMask := false,
        «first» :=
          [({ a := 13, W := 3, stored := false, tree := 0 }, Fmt.TreeSource.taken 0 0),
           ({ a := 22, W := 12, stored := false, tree := 5 }, Fmt.TreeSource.taken 0 5),
           ({ a := 22, W := 36, stored := false, tree := 1 }, Fmt.TreeSource.taken 1 1)],
        free := 0,
        firstTree := 7 },
    idx := [(5, 6), (6, 7), (9, 8), (10, 9), (11, 10)],
    oracles :=
      [[], [], [], [], [], [], [],
       [{ logLength := 18,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [5] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [6] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 13,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [7] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [8] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 0), (1, 5), (2, 1)],
    answers := 1,
    early := true }

/-- The two lists of codes of the key file's sizes. -/
def codesKeyFull : OnBytes.Codes :=
  { base :=
      #[{ logN := 24, ell := 4194304, r := 97 }, { logN := 21, ell := 131072, r := 52 },
        { logN := 17, ell := 8192, r := 52 }, { logN := 13, ell := 512, r := 52 },
        { logN := 14, ell := 512, r := 49 }, { logN := 22, ell := 262144, r := 98 },
        { logN := 18, ell := 16384, r := 49 }, { logN := 14, ell := 1024, r := 49 },
        { logN := 15, ell := 1024, r := 39 }, { logN := 15, ell := 2048, r := 49 },
        { logN := 13, ell := 256, r := 41 }, { logN := 15, ell := 256, r := 29 },
        { logN := 22, ell := 262144, r := 49 }, { logN := 19, ell := 16384, r := 39 },
        { logN := 17, ell := 2048, r := 33 }, { logN := 20, ell := 2048, r := 25 }],
    mask :=
      #[{ logN := 13, ell := 64, r := 146 }, { logN := 12, ell := 256, r := 52 },
        { logN := 14, ell := 1024, r := 49 }, { logN := 14, ell := 128, r := 49 },
        { logN := 13, ell := 64, r := 49 }, { logN := 15, ell := 512, r := 39 },
        { logN := 13, ell := 256, r := 49 }, { logN := 15, ell := 128, r := 49 },
        { logN := 14, ell := 64, r := 49 }, { logN := 13, ell := 64, r := 41 },
        { logN := 15, ell := 256, r := 29 }, { logN := 16, ell := 4096, r := 49 },
        { logN := 17, ell := 2048, r := 39 }, { logN := 17, ell := 1024, r := 33 },
        { logN := 20, ell := 4096, r := 25 }] }

/-- The planner's own radii at the stages of the key file's U, at the full size. -/
def rKUFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 24 then 8342420 else if s.C.a = 21 then 1519572 else if s.C.a = 17 then 95065 else if
    s.C.a = 13 then 5944 else if s.C.a = 14 then 12184 else 0

/-- The planner's own radii at the stages of the key file's O, at the full size. -/
def rKOFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 22 then 3138896 else if s.C.a = 18 then 196275 else if s.C.a = 14 then 12184 else if
    s.C.a = 15 then 26851 else 0

/-- The planner's own radii at the stages of the key file's W, at the full size. -/
def rKWFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 22 then 3138896 else if s.C.a = 18 then 196275 else if s.C.a = 15 then (if s.C.r = 49
    then 24460 else if s.C.r = 29 then 29702 else 0) else if s.C.a = 13 then 6631 else 0

end H2K.Member
