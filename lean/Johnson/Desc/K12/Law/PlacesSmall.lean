-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PlacesSmall.lean: the four places of a proximity test (the kind K12) in the
proof file of the smaller stored example proof, as closed terms, and the record's table of codes
there. Definitions alone; no theorem; no Mathlib beneath.

Why. A statement on a place `p : P12` has a member in Lean only at a closed place. These four are
the plan's numbers: sizes, counts and names of trees. No record of a run, no drawn value and no
entry of a message is here.
Main names: all in the namespace `H2K.Member`.
  `piU`: the folded row. `piO`: Omega; its first fold sends its own mask. `piW`: the own test.
    `piL`: the last test behind the links.
  `codesSmall`: the two lists of codes in the record in front of the tests at O and W (one text, to
    the sign); at U and L it is taken for the same table, one a file: `pubOk` says yes at it there
    too (Johnson/Desc/K12/Law/CondMembers.lean).
  `rU`, `rO`, `rW`, `rL`: a radius for each stage of a place, as a function of the stage: the
    planner's own radii, as the same print has them. 0 at any other stage.
Limits: THE FIVE TERMS WERE MADE BY A PROGRAM OFF THE PRINT OF A RUN that dumps the places which a
description makes of the stored public files, and holds each dumped term against the run's own value
[the print is not in this library; its sha256 is
da2b25bd09b8545fe8b45a72441d9938161293291b83a320408790dca934ba4b]. That they are these places is
that run's word: no theorem. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Join

set_option autoImplicit false
namespace H2K.Member
open VerifiableInference.Desc.K12 (P12)

/-- The place of the folded row. -/
def piU : P12 :=
  { place :=
      { chain := 2, link := none, piece := 0, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 57,
        work := 28,
        stages :=
          [{ C := { a := 17, l := 32768, r := 101 },
             Z := { a := 13, l := 64, r := 156 },
             k := 5,
             h := 0,
             t := 101 },
           { C := { a := 14, l := 2048, r := 68 },
             Z := { a := 12, l := 256, r := 68 },
             k := 4,
             h := 2,
             t := 68 },
           { C := { a := 14, l := 2048, r := 68 },
             Z := { a := 14, l := 1024, r := 68 },
             k := 0,
             h := 0,
             t := 68 }],
        ownMask := false,
        «first» :=
          [({ a := 17, W := 57, stored := false, tree := 0 }, Fmt.TreeSource.own 0),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 3,
        firstTree := 0 },
    idx := [(5, 5), (6, 6), (6, 7)],
    oracles :=
      [[], [], [], [], [], [], [],
       [{ logLength := 14,
          words := 72,
          tenants :=
            [{ main := 48, mask := 12, degree := 3, sampled := true, groups := [2] },
             { main := 0, mask := 12, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 14,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [3] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(2, 0), (2, 2)],
    answers := 1,
    early := true }

/-- The place of Omega. -/
def piO : P12 :=
  { place :=
      { chain := 2, link := none, piece := 1, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 3,
        work := 28,
        stages :=
          [{ C := { a := 18, l := 16384, r := 3831 },
             Z := { a := 13, l := 64, r := 156 },
             k := 2,
             h := 0,
             t := 55 },
           { C := { a := 14, l := 1024, r := 69 },
             Z := { a := 13, l := 1024, r := 69 },
             k := 4,
             h := 3,
             t := 69 },
           { C := { a := 15, l := 1024, r := 68 },
             Z := { a := 15, l := 4096, r := 68 },
             k := 0,
             h := 0,
             t := 68 }],
        ownMask := true,
        «first» :=
          [({ a := 18, W := 12, stored := false, tree := 1 }, Fmt.TreeSource.own 1),
           ({ a := 13, W := 3, stored := false, tree := 2 }, Fmt.TreeSource.own 2)],
        free := 5,
        firstTree := 0 },
    idx := [(7, 5), (8, 8), (9, 9)],
    oracles :=
      [[],
       [{ logLength := 13,
          words := 3,
          tenants := [{ main := 0, mask := 3, degree := 1, sampled := false, groups := [] }] }],
       [], [],
       [{ logLength := 14,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [4] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [5] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(2, 1), (2, 2)],
    answers := 1,
    early := true }

/-- The place of the own test. -/
def piW : P12 :=
  { place :=
      { chain := 3, link := none, piece := 0, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 5,
        work := 20,
        stages :=
          [{ C := { a := 18, l := 16384, r := 3831 },
             Z := { a := 13, l := 256, r := 59 },
             k := 3,
             h := 0,
             t := 59 },
           { C := { a := 14, l := 1024, r := 75 },
             Z := { a := 13, l := 1024, r := 75 },
             k := 4,
             h := 3,
             t := 75 },
           { C := { a := 15, l := 1024, r := 73 },
             Z := { a := 15, l := 4096, r := 73 },
             k := 0,
             h := 0,
             t := 73 }],
        ownMask := false,
        «first» :=
          [({ a := 13, W := 3, stored := false, tree := 1 }, Fmt.TreeSource.taken 0 1),
           ({ a := 18, W := 6, stored := false, tree := 21 }, Fmt.TreeSource.taken 0 21),
           ({ a := 18, W := 12, stored := false, tree := 1 }, Fmt.TreeSource.taken 1 1)],
        free := 0,
        firstTree := 23 },
    idx := [(7, 10), (10, 11), (11, 4)],
    oracles :=
      [[], [], [], [], [],
       [{ logLength := 14,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [11] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [12] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 1), (1, 21), (2, 1)],
    answers := 1,
    early := true }

/-- The place of the last test behind the links. -/
def piL : P12 :=
  { place :=
      { chain := 1, link := none, piece := 2, kind := VerifiableInference.Desc.KindName.K12 },
    nums :=
      { rows := 656,
        work := 20,
        stages :=
          [{ C := { a := 18, l := 131072, r := 218 },
             Z := { a := 17, l := 8192, r := 218 },
             k := 1,
             h := 0,
             t := 218 },
           { C := { a := 17, l := 8192, r := 55 },
             Z := { a := 17, l := 4096, r := 55 },
             k := 4,
             h := 3,
             t := 55 },
           { C := { a := 16, l := 1024, r := 44 },
             Z := { a := 16, l := 2048, r := 44 },
             k := 3,
             h := 3,
             t := 44 },
           { C := { a := 15, l := 128, r := 44 },
             Z := { a := 15, l := 1024, r := 44 },
             k := 3,
             h := 3,
             t := 44 },
           { C := { a := 15, l := 128, r := 73 },
             Z := { a := 15, l := 4096, r := 73 },
             k := 0,
             h := 0,
             t := 73 }],
        ownMask := false,
        «first» := [({ a := 18, W := 9, stored := false, tree := 16 }, Fmt.TreeSource.own 16)],
        free := 17,
        firstTree := 0 },
    idx := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)],
    oracles :=
      [[], [], [],
       [{ logLength := 17,
          words := 96,
          tenants :=
            [{ main := 48, mask := 24, degree := 3, sampled := true, groups := [6] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [], [],
       [{ logLength := 16,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [7] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 15,
          words := 72,
          tenants :=
            [{ main := 24, mask := 24, degree := 3, sampled := true, groups := [8] },
             { main := 0, mask := 24, degree := 1, sampled := false, groups := [] }] }],
       [], [], [], [], [],
       [{ logLength := 15,
          words := 12,
          tenants :=
            [{ main := 3, mask := 3, degree := 3, sampled := true, groups := [9] },
             { main := 3, mask := 3, degree := 3, sampled := false, groups := [] }] }],
       [], [], []],
    before := [(1, 16)],
    answers := 1,
    early := true }

/-- The record's two lists of codes. -/
def codesSmall : OnBytes.Codes :=
  { base :=
      #[{ logN := 18, ell := 131072, r := 218 }, { logN := 17, ell := 8192, r := 55 },
        { logN := 16, ell := 1024, r := 44 }, { logN := 15, ell := 128, r := 44 },
        { logN := 15, ell := 128, r := 73 }, { logN := 17, ell := 32768, r := 101 },
        { logN := 14, ell := 2048, r := 68 }, { logN := 18, ell := 16384, r := 3831 },
        { logN := 14, ell := 1024, r := 69 }, { logN := 15, ell := 1024, r := 68 },
        { logN := 14, ell := 1024, r := 75 }, { logN := 15, ell := 1024, r := 73 }],
    mask :=
      #[{ logN := 17, ell := 8192, r := 218 }, { logN := 17, ell := 4096, r := 55 },
        { logN := 16, ell := 2048, r := 44 }, { logN := 15, ell := 1024, r := 44 },
        { logN := 15, ell := 4096, r := 73 }, { logN := 13, ell := 64, r := 156 },
        { logN := 12, ell := 256, r := 68 }, { logN := 14, ell := 1024, r := 68 },
        { logN := 13, ell := 1024, r := 69 }, { logN := 15, ell := 4096, r := 68 },
        { logN := 13, ell := 256, r := 59 }, { logN := 13, ell := 1024, r := 75 }] }

/-- The planner's own radii at U's three stages. -/
def rU (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 17 then 65300 else if s.C.a = 14 then 10487 else 0

/-- The planner's own radii at O's three stages. -/
def rO (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 18 then 189103 else if s.C.a = 14 then 10390 else if s.C.a = 15 then 21065 else 0

/-- The planner's own radii at W's three stages. -/
def rW (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 18 then 189103 else if s.C.a = 14 then 10374 else if s.C.a = 15 then 21058 else 0

/-- The planner's own radii at L's five stages: two of them have words of one length, and are told
apart by the tail. -/
def rL (s : Fmt.M1.Stage) : Nat :=
  if s.C.a = 18 then 76267 else if s.C.a = 17 then 98093 else if s.C.a = 16 then 53784
  else if s.C.a = 15 then (if s.C.r = 44 then 26835 else if s.C.r = 73 then 21058 else 0) else 0

end H2K.Member
