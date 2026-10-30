-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PlacesFull.lean: the four places of a proximity test (the kind K12) in the
proof file of the full-size stored example proof, as closed terms, the record's table of codes
there, and the planner's radii. Definitions alone; no theorem; no Mathlib beneath.

Why. As Johnson/Desc/K12/Law/PlacesSmall.lean, at the full size. These are the plan's numbers:
sizes, counts and names of trees. No record of a run, no drawn value and no entry of a message is
here.
Main names: all in the namespace `H2K.Member`.
  `piUFull`: the folded row. `piOFull`: Omega; its first fold sends its own mask. `piWFull`: the own
    test. `piLFull`: the last test behind the links.
  `codesFull`: the two lists of codes in the record in front of the test at O; at U, W and L it is
    taken for the same table, one a file: `pubOk` says yes at it there too
    (Johnson/Desc/K12/Law/CondMembersFull.lean).
  `rUFull`, `rOFull`, `rWFull`, `rLFull`: a radius for each stage of a place, as a function of the
    stage: the planner's own radii, as the same print has them. 0 at any other stage.
Limits: THE FOUR PLACES AND THE TABLE WERE MADE BY A PROGRAM OFF THE PRINT OF A RUN that dumps the
four places which a description makes of the stored public files [the print is not in this library;
its sha256 is 868dcd497add0d9b94b089233402e886273d1d51c2799de49e1d01ddf74acd98]. That they are these
places is that run's word: no theorem. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Join

set_option autoImplicit false
namespace H2K.Member
open VerifiableInference.Desc.K12 (P12)

/-- The place of the folded row, at the full size. -/
def piUFull : P12 :=
  { place :=
      { chain := 2, link := none, piece := 0, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 68,
        work := 28,
        stages :=
          [{ C := { a := 24, l := 4194304, r := 101 },
             Z := { a := 13, l := 64, r := 152 },
             k := 7,
             h := 0,
             t := 101 },
           { C := { a := 21, l := 131072, r := 54 },
             Z := { a := 12, l := 256, r := 54 },
             k := 5,
             h := 2,
             t := 54 },
           { C := { a := 17, l := 8192, r := 54 },
             Z := { a := 12, l := 256, r := 54 },
             k := 4,
             h := 2,
             t := 54 },
           { C := { a := 13, l := 512, r := 54 },
             Z := { a := 12, l := 256, r := 54 },
             k := 4,
             h := 2,
             t := 54 },
           { C := { a := 14, l := 512, r := 51 },
             Z := { a := 14, l := 1024, r := 51 },
             k := 0,
             h := 0,
             t := 51 }],
        ownMask := false,
        «first» :=
          [({ a := 24, W := 324, stored := false, tree := 0 }, Fmt.TreeSource.own 0),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 3,
        firstTree := 0 },
    idx := [(6, 6), (7, 7), (8, 7), (9, 7), (10, 8)],
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

/-- The place of Omega, at the full size. -/
def piOFull : P12 :=
  { place :=
      { chain := 2, link := none, piece := 1, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 3,
        work := 28,
        stages :=
          [{ C := { a := 22, l := 262144, r := 3571 },
             Z := { a := 13, l := 64, r := 152 },
             k := 4,
             h := 0,
             t := 51 },
           { C := { a := 18, l := 16384, r := 51 },
             Z := { a := 14, l := 512, r := 51 },
             k := 4,
             h := 3,
             t := 51 },
           { C := { a := 14, l := 1024, r := 51 },
             Z := { a := 13, l := 256, r := 51 },
             k := 4,
             h := 3,
             t := 51 },
           { C := { a := 15, l := 1024, r := 41 },
             Z := { a := 15, l := 1024, r := 41 },
             k := 0,
             h := 0,
             t := 41 }],
        ownMask := true,
        «first» :=
          [({ a := 22, W := 36, stored := false, tree := 1 }, Fmt.TreeSource.own 1),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 7,
        firstTree := 0 },
    idx := [(11, 6), (12, 9), (13, 10), (14, 11)],
    oracles :=
      [[],
       [{ logLength := 13,
          words := 3,
          tenants := [{ main := 0, mask := 3, degree := 1, sampled := false, groups := [] }] }],
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

/-- The place of the own test, at the full size. -/
def piWFull : P12 :=
  { place :=
      { chain := 3, link := none, piece := 0, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 5,
        work := 20,
        stages :=
          [{ C := { a := 22, l := 262144, r := 3571 },
             Z := { a := 13, l := 256, r := 55 },
             k := 5,
             h := 1,
             t := 55 },
           { C := { a := 18, l := 16384, r := 55 },
             Z := { a := 15, l := 1024, r := 55 },
             k := 4,
             h := 3,
             t := 55 },
           { C := { a := 15, l := 2048, r := 55 },
             Z := { a := 14, l := 512, r := 55 },
             k := 3,
             h := 3,
             t := 55 },
           { C := { a := 13, l := 256, r := 46 },
             Z := { a := 13, l := 256, r := 46 },
             k := 3,
             h := 3,
             t := 46 },
           { C := { a := 15, l := 256, r := 44 },
             Z := { a := 15, l := 1024, r := 44 },
             k := 0,
             h := 0,
             t := 44 }],
        ownMask := false,
        «first» :=
          [({ a := 13, W := 3, stored := false, tree := 1 }, Fmt.TreeSource.taken 0 1),
           ({ a := 22, W := 12, stored := false, tree := 82 }, Fmt.TreeSource.taken 0 82),
           ({ a := 22, W := 36, stored := false, tree := 1 }, Fmt.TreeSource.taken 1 1)],
        free := 0,
        firstTree := 84 },
    idx := [(11, 12), (15, 3), (16, 13), (4, 4), (5, 5)],
    oracles :=
      [[], [], [], [], [], [], [],
       [{ logLength := 18,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [32] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [33] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 13,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [34] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [35] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 1), (1, 82), (2, 1)],
    answers := 1,
    early := true }

/-- The place of the last test behind the links, at the full size. -/
def piLFull : P12 :=
  { place :=
      { chain := 1, link := none, piece := 2, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 659,
        work := 20,
        stages :=
          [{ C := { a := 23, l := 4194304, r := 219 },
             Z := { a := 17, l := 8192, r := 219 },
             k := 1,
             h := 0,
             t := 219 },
           { C := { a := 22, l := 262144, r := 55 },
             Z := { a := 17, l := 4096, r := 55 },
             k := 4,
             h := 3,
             t := 55 },
           { C := { a := 19, l := 32768, r := 55 },
             Z := { a := 16, l := 2048, r := 55 },
             k := 3,
             h := 3,
             t := 55 },
           { C := { a := 16, l := 4096, r := 55 },
             Z := { a := 15, l := 1024, r := 55 },
             k := 3,
             h := 3,
             t := 55 },
           { C := { a := 13, l := 256, r := 46 },
             Z := { a := 13, l := 256, r := 46 },
             k := 4,
             h := 4,
             t := 46 },
           { C := { a := 15, l := 256, r := 44 },
             Z := { a := 15, l := 1024, r := 44 },
             k := 0,
             h := 0,
             t := 44 }],
        ownMask := false,
        «first» := [({ a := 23, W := 9, stored := false, tree := 76 }, Fmt.TreeSource.own 76)],
        free := 77,
        firstTree := 0 },
    idx := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)],
    oracles :=
      [[], [], [],
       [{ logLength := 22,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [26] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 19,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [27] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 16,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [28] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 13,
          words := 144,
          tenants :=
            [{ main := 48, mask := 48, degree := 3, sampled := true, groups := [29] },
             { main := 0, mask := 48, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [30] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 76)],
    answers := 1,
    early := true }

/-- The record's two lists of codes. -/
def codesFull : OnBytes.Codes :=
  { base :=
      #[{ logN := 23, ell := 4194304, r := 219 }, { logN := 22, ell := 262144, r := 55 },
        { logN := 19, ell := 32768, r := 55 }, { logN := 16, ell := 4096, r := 55 },
        { logN := 13, ell := 256, r := 46 }, { logN := 15, ell := 256, r := 44 },
        { logN := 24, ell := 4194304, r := 101 }, { logN := 21, ell := 131072, r := 54 },
        { logN := 17, ell := 8192, r := 54 }, { logN := 13, ell := 512, r := 54 },
        { logN := 14, ell := 512, r := 51 }, { logN := 22, ell := 262144, r := 3571 },
        { logN := 18, ell := 16384, r := 51 }, { logN := 14, ell := 1024, r := 51 },
        { logN := 15, ell := 1024, r := 41 }, { logN := 18, ell := 16384, r := 55 },
        { logN := 15, ell := 2048, r := 55 }],
    mask :=
      #[{ logN := 17, ell := 8192, r := 219 }, { logN := 17, ell := 4096, r := 55 },
        { logN := 16, ell := 2048, r := 55 }, { logN := 15, ell := 1024, r := 55 },
        { logN := 13, ell := 256, r := 46 }, { logN := 15, ell := 1024, r := 44 },
        { logN := 13, ell := 64, r := 152 }, { logN := 12, ell := 256, r := 54 },
        { logN := 14, ell := 1024, r := 51 }, { logN := 14, ell := 512, r := 51 },
        { logN := 13, ell := 256, r := 51 }, { logN := 15, ell := 1024, r := 41 },
        { logN := 13, ell := 256, r := 55 }, { logN := 14, ell := 512, r := 55 }] }

/-- The planner's own radii at U's stages, at the full size. -/
def rUFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 24 then 8342416 else if s.C.a = 21 then 1517714 else if s.C.a = 17 then 94948 else if
    s.C.a = 13 then 5937 else if s.C.a = 14 then 12180 else 0

/-- The planner's own radii at O's stages, at the full size. -/
def rOFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 22 then 3131972 else if s.C.a = 18 then 196271 else if s.C.a = 14 then 12180 else if
    s.C.a = 15 then 26843 else 0

/-- The planner's own radii at W's stages, at the full size. -/
def rWFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 22 then 3131972 else if s.C.a = 18 then 196263 else if s.C.a = 15 then (if s.C.r = 55
    then 24449 else if s.C.r = 44 then 26837 else 0) else if s.C.a = 13 then 6617 else 0

/-- The planner's own radii at L's stages, at the full size. -/
def rLFull (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 23 then 2433820 else if s.C.a = 22 then 3138982 else if s.C.a = 19 then 392563 else if
    s.C.a = 16 then 48999 else if s.C.a = 13 then 6617 else if s.C.a = 15 then 26837 else 0

end H2K.Member
