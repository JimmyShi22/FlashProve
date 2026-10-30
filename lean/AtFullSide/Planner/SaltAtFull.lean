-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Planner/SaltAtFull.lean: at the goals' two named sets of public files, and at the first
of them under every policy within four bounds, the plan's salt has 40 bytes: `Bind.Cpp.SaltAt`
(Johnson/Bind/Cpp/Defs.lean) at `VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap` and `VerifierAndGoals.zAt C theta cap`. Calls
alone. No definition: no goal is stated.
Why. `SaltAt Z` is the one premise of the five equations between the written committer's typed
queries and the format's own functions (`Bind.Spell.spells`, Johnson/Bind/Spell/Closed.lean). These
equations, and whatever is built on them, can be called only at public files at which it is shown.
  **`saltAt_zFull`**: no premise. By `Bind.Cpp.saltAt_iff` (Johnson/Bind/Cpp/SaltAt.lean) at
    `planLaid_zFull` (MadeReturns.lean); the files are in scope by `VerifierAndGoals.filesRead`
    (Johnson/Goal/Files/FilesReadProof.lean).
  **`saltAt_zGap`**: no premise. From it by `Bind.Policy.saltAt_gap_of_full`
    (Johnson/Bind/Policy/SaltAtGap.lean): the two sets of files part in the policy's three numbers
    alone.
  `saltAt_zAt`: at `VerifierAndGoals.zAt C theta cap` (Johnson/Goal/Files/ScopeAtPolicies.lean: `storedPublicFiles` with
    these three numbers as its policy), for C < 2^32, theta ≤ C, cap ≤ 1024 and 2^8 ≤ theta. By
    `Bind.Policy.saltAt_bounds_of_full` (Johnson/Bind/Policy/SaltAtBounds.lean).
  `spells_zFull`, `spells_zGap`, `spells_zAt`: so the five equations hold at all of these, at every
    hash function.
Limits. AT THESE FILES ALONE: the layout file, the scale file and the parameter file's other free
numbers are `storedPublicFiles`'s throughout. That the planner returns at all files in scope that are read
(`Bind.Cpp.PlannerReturns`) is not shown. All are terms made of those written in Ladder/Stored.lean:
no Lean code ties them to the top-level folder examples/. A fact on the description's frame, not on
any committer and not on any program. This file lies in the side library AtFullSide, which is built
with a larger thread stack (lake build AtFullSide). Nothing on soundness, on a binding of the
commitment (the opening form, `BindsWith`), on correctness of extraction, on completeness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Planner.MadeReturns
import Johnson.Bind.Policy.SaltAtGap
import Johnson.Bind.Policy.SaltAtBounds
import Johnson.Bind.Spell.Closed
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Planner
open Bind.Cpp

/- Lean compares the named files by their names: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zAt

/-- **At `VerifierAndGoals.storedPublicFiles` the plan's salt has 40 bytes.** -/
theorem saltAt_zFull : SaltAt VerifierAndGoals.storedPublicFiles :=
  (saltAt_iff VerifierAndGoals.filesRead.full.1).2 planLaid_zFull

/-- **At `VerifierAndGoals.zGap` too.** -/
theorem saltAt_zGap : SaltAt VerifierAndGoals.zGap :=
  Bind.Policy.saltAt_gap_of_full saltAt_zFull

/-- At `storedPublicFiles` under every policy within the four bounds. -/
theorem saltAt_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) : SaltAt (VerifierAndGoals.zAt C theta cap) :=
  Bind.Policy.saltAt_bounds_of_full h1 h2 h3 h4 saltAt_zFull

/-- The five equations at `VerifierAndGoals.storedPublicFiles`, at every hash function. -/
theorem spells_zFull (hash : VerifiableInference.Hash) : Spells VerifierAndGoals.storedPublicFiles hash :=
  Bind.Spell.spells VerifierAndGoals.storedPublicFiles saltAt_zFull hash

/-- The five equations at `VerifierAndGoals.zGap`, at every hash function. -/
theorem spells_zGap (hash : VerifiableInference.Hash) : Spells VerifierAndGoals.zGap hash :=
  Bind.Spell.spells VerifierAndGoals.zGap saltAt_zGap hash

/-- The five equations at `storedPublicFiles` under every policy within the four bounds. -/
theorem spells_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) (hash : VerifiableInference.Hash) :
    Spells (VerifierAndGoals.zAt C theta cap) hash :=
  Bind.Spell.spells _ (saltAt_zAt h1 h2 h3 h4) hash

end AtFullSide.Planner

#print axioms AtFullSide.Planner.saltAt_zFull
#print axioms AtFullSide.Planner.saltAt_zGap
#print axioms AtFullSide.Planner.saltAt_zAt
#print axioms AtFullSide.Planner.spells_zFull
#print axioms AtFullSide.Planner.spells_zGap
#print axioms AtFullSide.Planner.spells_zAt
