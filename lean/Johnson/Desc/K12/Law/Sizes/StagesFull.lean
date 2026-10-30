-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/StagesFull.lean: the planner's sized stages of a proof file's four
proximity tests (the kind K12) at the full size, and the setting, as closed terms.

Definitions only. The planner (OnBytes/Params/) sizes each test as a list of stages (`StageSize`:
the two codes, the numbers of row variables, the rule, its integer m, the positions, the entries
that fill the mask rows up). This file writes the four lists out, so that the kernel can evaluate
tests on them and theorems can name them.
Main names:
  `setAt`: the setting.
  `szLFull`, `szUFull`, `szOFull`, `szWFull`: the first chain's last test, the folded row's,
    Omega's, the request's own.
Limits: the lists and the setting were printed by Lean's evaluator and laid in by a program. That
they are what the planner returns is said by no line of this file: see StageSizesAtScope.lean in
this folder, which says of which lists it is proved and under what. Nothing on soundness. Nothing on
hiding.
-/
import OnBytes.Params.Group

set_option autoImplicit false
namespace H2K.Member
open OnBytes.Params

/-- The setting. -/
def setAt : Setting :=
  { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false
    instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8
    positionBytes := 0, workField := { request := 0, shared := 0, once := 0 }
    workSample := { request := 0, shared := 0, once := 0 }
    workCloseness := { request := 0, shared := 0, once := 0 }
    workQuery := { request := 20, shared := 28, once := 32 }
    workSmall := { request := 0, shared := 0, once := 0 } }

/-- The stages of the first chain's last test, at the full size. -/
def szLFull : List StageSize := [
  { g := { main := { logN := 23, ell := 4194304, r := 219, overE := true }
           mask := { logN := 17, ell := 8192, r := 219, overE := true }
           k := 1, h := 0, slots := 1, rule := .johnson, m := 258 }
    t := 219, rOod := 0 },
  { g := { main := { logN := 22, ell := 262144, r := 55, overE := true }
           mask := { logN := 17, ell := 4096, r := 55, overE := true }
           k := 4, h := 3, slots := 1, rule := .johnson, m := 158 }
    t := 55, rOod := 15727 },
  { g := { main := { logN := 19, ell := 32768, r := 55, overE := true }
           mask := { logN := 16, ell := 2048, r := 55, overE := true }
           k := 3, h := 3, slots := 1, rule := .johnson, m := 241 }
    t := 55, rOod := 8027 },
  { g := { main := { logN := 16, ell := 4096, r := 55, overE := true }
           mask := { logN := 15, ell := 1024, r := 55, overE := true }
           k := 3, h := 3, slots := 1, rule := .johnson, m := 367 }
    t := 55, rOod := 3931 },
  { g := { main := { logN := 13, ell := 256, r := 46, overE := true }
           mask := { logN := 13, ell := 256, r := 46, overE := true }
           k := 4, h := 4, slots := 1, rule := .johnson, m := 378 }
    t := 46, rOod := 1883 },
  { g := { main := { logN := 15, ell := 256, r := 44, overE := true }
           mask := { logN := 15, ell := 1024, r := 44, overE := true }
           k := 0, h := 0, slots := 1, rule := .johnson, m := 345 }
    t := 44, rOod := 374 }]

/-- The stages of the folded row's test, at the full size. -/
def szUFull : List StageSize := [
  { g := { main := { logN := 24, ell := 4194304, r := 101, overE := true }
           mask := { logN := 13, ell := 64, r := 152, overE := true }
           k := 7, h := 0, slots := 1, rule := .johnson, m := 182 }
    t := 101, rOod := 0 },
  { g := { main := { logN := 21, ell := 131072, r := 54, overE := true }
           mask := { logN := 12, ell := 256, r := 54, overE := true }
           k := 5, h := 2, slots := 1, rule := .johnson, m := 168 }
    t := 54, rOod := 491 },
  { g := { main := { logN := 17, ell := 8192, r := 54, overE := true }
           mask := { logN := 12, ell := 256, r := 54, overE := true }
           k := 4, h := 2, slots := 1, rule := .johnson, m := 293 }
    t := 54, rOod := 350 },
  { g := { main := { logN := 13, ell := 512, r := 54, overE := true }
           mask := { logN := 12, ell := 256, r := 54, overE := true }
           k := 4, h := 2, slots := 1, rule := .johnson, m := 510 }
    t := 54, rOod := 350 },
  { g := { main := { logN := 14, ell := 512, r := 51, overE := true }
           mask := { logN := 14, ell := 1024, r := 51, overE := true }
           k := 0, h := 0, slots := 1, rule := .johnson, m := 489 }
    t := 51, rOod := 350 }]

/-- The stages of Omega's test, at the full size. -/
def szOFull : List StageSize := [
  { g := { main := { logN := 22, ell := 262144, r := 3571, overE := true }
           mask := { logN := 13, ell := 64, r := 152, overE := true }
           k := 4, h := 0, slots := 1, rule := .johnson, m := 159 }
    t := 51, rOod := 0 },
  { g := { main := { logN := 18, ell := 16384, r := 51, overE := true }
           mask := { logN := 14, ell := 512, r := 51, overE := true }
           k := 4, h := 3, slots := 1, rule := .johnson, m := 277 }
    t := 51, rOod := 93 },
  { g := { main := { logN := 14, ell := 1024, r := 51, overE := true }
           mask := { logN := 13, ell := 256, r := 51, overE := true }
           k := 4, h := 3, slots := 1, rule := .johnson, m := 489 }
    t := 51, rOod := 871 },
  { g := { main := { logN := 15, ell := 1024, r := 41, overE := true }
           mask := { logN := 15, ell := 1024, r := 41, overE := true }
           k := 0, h := 0, slots := 1, rule := .johnson, m := 299 }
    t := 41, rOod := 359 }]

/-- The stages of the request's own test, at the full size. -/
def szWFull : List StageSize := [
  { g := { main := { logN := 22, ell := 262144, r := 3571, overE := true }
           mask := { logN := 13, ell := 256, r := 55, overE := true }
           k := 5, h := 1, slots := 1, rule := .johnson, m := 159 }
    t := 55, rOod := 0 },
  { g := { main := { logN := 18, ell := 16384, r := 55, overE := true }
           mask := { logN := 15, ell := 1024, r := 55, overE := true }
           k := 4, h := 3, slots := 1, rule := .johnson, m := 277 }
    t := 55, rOod := 3999 },
  { g := { main := { logN := 15, ell := 2048, r := 55, overE := true }
           mask := { logN := 14, ell := 512, r := 55, overE := true }
           k := 3, h := 3, slots := 1, rule := .johnson, m := 423 }
    t := 55, rOod := 1883 },
  { g := { main := { logN := 13, ell := 256, r := 46, overE := true }
           mask := { logN := 13, ell := 256, r := 46, overE := true }
           k := 3, h := 3, slots := 1, rule := .johnson, m := 378 }
    t := 46, rOod := 859 },
  { g := { main := { logN := 15, ell := 256, r := 44, overE := true }
           mask := { logN := 15, ell := 1024, r := 44, overE := true }
           k := 0, h := 0, slots := 1, rule := .johnson, m := 345 }
    t := 44, rOod := 374 }]

end H2K.Member
