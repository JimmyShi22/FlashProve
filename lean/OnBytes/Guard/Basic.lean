-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Lean
/-!
# The guard on compiled code: common parts

Where a constant was declared (Lean's core, a package, or this library), and the three axioms. Used
by Csimp.lean, Cone.lean, Cmd.lean and Core.lean. These are programs that run while the library is
built; nothing here is compiled into a verifier.
Written for this library.
-/
set_option autoImplicit false

namespace OnBytes.Guard

open Lean

/-- The three axioms of Lean's standard library. -/
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The first components of the module names of Lean's own libraries. -/
def coreRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- The first components of the module names of the nine packages that this library pins
(lake-manifest.json). -/
def packageRoots : List Name :=
  [`Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph, `LeanSearchClient,
   `Cli]

/-- Where a constant was declared. -/
inductive Origin where
  | core
  | packages
  /-- every module whose first component is neither in coreRoots nor in packageRoots, and the file
  that is being compiled -/
  | own
  deriving DecidableEq, Repr

/-- Where n was declared. A module that is not known counts as this library's, which is the strict
side. -/
def originOf (env : Environment) (n : Name) : Origin :=
  match env.getModuleIdxFor? n with
  | none => .own
  | some i =>
    let r := (env.header.moduleNames.getD i.toNat .anonymous).getRoot
    if coreRoots.contains r then .core else if packageRoots.contains r then .packages else .own

/-- The module that declares n; anonymous for the file that is being compiled and for a name that
does not exist. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | none => .anonymous
  | some i => env.header.moduleNames.getD i.toNat .anonymous

/-- The names of a list, one to a line, sorted. -/
def lines (ns : Array Name) : MessageData :=
  MessageData.joinSep ((ns.qsort Name.lt).toList.map fun n => m!"  {n}") "\n"

end OnBytes.Guard
