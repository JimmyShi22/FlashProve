-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Skeleton/Steps.lean: the Lean verifier program's check of a proof file's first hash chain,
written again as named steps: definitions with code; no theorem is about them.

This folder holds a second form of the stage on a proof file by the Lean verifier program
`verify-on-bytes` (OnBytes/), in which the check of the file's first hash chain is a list of named
steps. No theorem says that this form and the program's own check agree, and we know places where
they differ: among them those under Limits in SpyLay.lean, SpyAtt.lean and SpyTail.lean. The folder
exists so that the check can be run step by step on a stored proof, and
so that a single step can be replaced by another definition. The 22 steps of the head's link lie
outside the folder (Johnson/Top/H/Course/HeadSpy.lean).

This file: what SpyLay.lean, SpyAtt.lean and SpyTail.lean share. `runAll` runs routines one after
the other. `looksOf` runs a list of named steps and keeps, after each step, its name, the record of
local values and the program's context (`Ctx`): together a `Look`. `spy` also keeps these before the
first step. The type of the record is a parameter A. If a step fails, the run fails with it and
nothing is kept. A test that the program only notes in its context (`Blk.check`, the field `failed`)
fails no step: the run goes on, and `looksOf` and `spy` do not read that field.



Limits: definitions only. Nothing is evaluated in this file and nothing is proved about it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.Course.LocRel
import OnBytes.Model.StagesLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course.SpyK1
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- Runs routines that return no value, one after the other; the first that fails ends the run. -/
def runAll : List (SubM Unit) → SubM Unit
  | [] => pure ()
  | r :: rs => do r; runAll rs

/-- What is kept at one point of a run: the step's name, the record of local values, the context. -/
abbrev Look (A : Type) : Type := String × A × Ctx

/-- Runs the named steps in order and returns one `Look` after each. If a step fails, the run fails
and returns none. -/
def looksOf {A : Type} : List (String × (A → Blk A)) → A → Blk (List (Look A))
  | [], _ => pure []
  | (n, s) :: rest, a => do
    let a' ← s a
    let c ← get
    let l ← looksOf rest a'
    pure ((n, a', c) :: l)

/-- `looksOf` with one more `Look` in front, named "start": the record and the context before the
first step. -/
def spy {A : Type} (steps : List (String × (A → Blk A))) (a : A) : Blk (List (Look A)) := do
  let c ← get
  let l ← looksOf steps a
  pure (("start", a, c) :: l)

end KObj.Course.SpyK1
