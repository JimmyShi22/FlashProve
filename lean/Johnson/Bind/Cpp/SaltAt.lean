-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SaltAt.lean: what the owed proposition `SaltAt Z` (Johnson/Bind/Cpp/Defs.lean: the
frame that the description lays at Z has salts of 40 bytes) comes to: in the goals' scope it says
that the library's planner returns a plan at Z, no more and no less.

Main statements.
  `saltAt_iff`: in scope, `SaltAt Z` holds exactly where the plan's seat holds a plan.
  `not_saltAt_of_refused`: at all files, where the planner refuses, `SaltAt Z` is false.
  `saltAt_of_live`: in scope, where the description's test on the public files says yes, it holds.
  `PlannerReturns`, `saltInScope_iff`: `SaltInScope` is the closed proposition "the planner returns
    at all public files in scope that are read".

Limits. `PlannerReturns` IS NOT PROVED, here or elsewhere. It is a fact on the library's planner and
reader, free of any committer. By a reading of the planner's text against the reader's last test
(`Inst.Model.Lawful`), no theorem: every test that the planner makes on the scale file and on the
parameter file's eight free numbers follows from what the reader has tested, and every other test
reads bytes that the scope fixes (read by the fields' names through some twenty routines; three sets
of files at the ends of the reader's intervals were evaluated, and the planner returned). Four of
these others compare digests of the model's public tables under the second hash function.
Nothing on soundness, on correctness of extraction or on a binding of the commitment.

-/
import Johnson.Bind.Cpp.Defs
import Johnson.Bind.SaltPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Cpp
open VerifierAndGoals FlashProve

/-- **In scope the frame's salts have 40 bytes exactly where the planner returns.** -/
theorem saltAt_iff {Z : PublicFiles} (hZ : InScope Z = true) :
    SaltAt Z ↔ ∃ G, thePlanLaid (asDescriptionFiles Z) = .ok G :=
  salt_iff_laid hZ

/-- **Where the planner refuses, in scope or not, the proposition is false.** -/
theorem not_saltAt_of_refused {Z : PublicFiles} {m : String} (h : thePlanLaid (asDescriptionFiles Z) = .error m) :
    ¬ SaltAt Z := by
  intro hs
  have h0 : saltLen Z = 0 := salt_of_refused h
  have h40 : saltLen Z = 40 := hs
  omega

/-- **In scope, where the description's test on the public files says yes, it holds.** -/
theorem saltAt_of_live {Z : PublicFiles} (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    SaltAt Z :=
  salt_of_live hZ hl

/-- The library's planner returns a plan at all public files in scope that are read. A closed
proposition on the planner and the reader. NOT PROVED. The binders are those of the goals on the
commitment (`BindsAt`, Ladder.lean). "That are read" narrows nothing: files in scope are read
(`inScope_readFiles`, Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean). -/
def PlannerReturns : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    ∃ G, thePlanLaid (asDescriptionFiles Z) = .ok G

/-- **What is owed under the name SaltInScope is that the planner returns.** -/
theorem saltInScope_iff : SaltInScope ↔ PlannerReturns :=
  ⟨fun h Z pp hZ hr => (saltAt_iff hZ).1 (h Z pp hZ hr),
    fun h Z pp hZ hr => (saltAt_iff hZ).2 (h Z pp hZ hr)⟩

end Bind.Cpp

#print axioms Bind.Cpp.saltAt_iff
#print axioms Bind.Cpp.not_saltAt_of_refused
#print axioms Bind.Cpp.saltAt_of_live
#print axioms Bind.Cpp.saltInScope_iff
