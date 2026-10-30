-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Told.lean: what is told of the trees of a key file's three chains at the full
size, written out: 6, 11 and 4 trees, each with its tenants and every tenant's groups. Data alone.

A tree: ⟨log-length, words of a symbol, tenants⟩; a tenant: ⟨main words, mask words, degree, whether
it has an out-of-domain sample, the groups that it joins⟩ (Johnson/Desc/Oracle.lean).

Whence. Typed by hand by one author, by reading: the oracle messages of the 19 written sendings
(keySendsFull, Johnson/G/SendsWritten.lean), each as a tenant by the text of ProofFile.tenantOf
(Johnson/Desc/ProofFile/Told.lean); the groups by the text of Key.groupsAtLabel
(Johnson/Desc/Key/Source.lean); log-length and words off the shapes at which the written rounds open
the trees (Johnson/G/DryKeyLit.lean). The shared chain's tree 7 is the mask that the first fold of
Omega's test sends itself.
What holds these values elsewhere, and what does not. With the groups struck they are what the
closed description's blocks say of their oracle messages (COracles.lean). The groups are held by the
tests "opened", "alone" and "grouped" and by BookPlan's clauses up to their order: at the shared
chain's trees 1 and 2 the lists [250, 300] and [250, 200] could stand turned round and no test here
would say no ("opened" sorts both sides). The order is held only where Key.toldOfMade's return is
shown.
Limits. No theorem is here. That these are what Key.toldOfMade returns at any public files is not
said here: a theorem that says it can stand only in a file that imports this one. One such theorem,
Johnson.AtFull.KeyBack.toldOfMade_in_scope (Johnson/AtFull/KeyBack/InScopeNamed.lean), says it of
Key.toldOfMade m, under three premises: the public files are in scope of the goals (VerifierAndGoals.InScope),
publicOfO returns on them, and m is what Key.madeAt then returns at the constant digest
Key.fixedDigest. The three premises are met at the library's written copy of the full-size public
files (VerifierAndGoals.storedPublicFiles: three terms written in Lean; no theorem ties
them to the repository's files): the first by VerifierAndGoals.inScope_full
(Johnson/Goal/Files/ScopeExample.lean), the other two by AtFullSide.Planner.theKeyLaid_zFull_returns
(AtFullSide/Planner/KeyLaidReturns.lean), at the format's second hash function (OnBytes.secondHashFunction) and
the same constant digest, not the files' own, in a side library outside the main library (one
constant beneath it passes Lean's kernel only at a larger thread stack; Lean's re-checker,
leanchecker, was run on it and fails there at each shell stack limit that was tried; the toolchain's
own replay passes it at a larger thread stack; so that constant has been checked by the kernel in
the build and by that replay, and by no independent program); no independent checker has replayed
any of the closed facts beneath it, and the full-size example's weights are synthetic. These last
two theorems speak of VerifierAndGoals.storedPublicFiles alone, not of other files in scope.

Nothing on soundness.

-/
import Johnson.Desc.Key.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

/-- The first chain's six trees. -/
def told1 : List ProofFile.Root :=
  [⟨13, 3, [⟨0, 3, 1, true, [300]⟩]⟩,
   ⟨22, 77, [⟨2, 27, 1, true, [100]⟩, ⟨0, 48, 1, false, []⟩]⟩,
   ⟨19, 96, [⟨48, 24, 3, true, [101]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨17, 72, [⟨24, 24, 3, true, [102]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨20, 12, [⟨3, 3, 3, true, [103]⟩, ⟨3, 3, 3, false, []⟩]⟩,
   ⟨22, 12, [⟨3, 3, 3, true, [300]⟩, ⟨0, 6, 1, false, []⟩]⟩]

/-- The shared chain's eleven trees. -/
def told2 : List ProofFile.Root :=
  [⟨24, 324, [⟨321, 0, 3, true, [200]⟩, ⟨0, 3, 1, false, []⟩]⟩,
   ⟨22, 36, [⟨36, 0, 3, true, [250, 300]⟩]⟩,
   ⟨13, 3, [⟨0, 3, 1, true, [250, 200]⟩]⟩,
   ⟨21, 120, [⟨96, 12, 3, true, [201]⟩, ⟨0, 12, 1, false, []⟩]⟩,
   ⟨17, 72, [⟨48, 12, 3, true, [202]⟩, ⟨0, 12, 1, false, []⟩]⟩,
   ⟨13, 72, [⟨48, 12, 3, true, [203]⟩, ⟨0, 12, 1, false, []⟩]⟩,
   ⟨14, 12, [⟨3, 3, 3, true, [204]⟩, ⟨3, 3, 3, false, []⟩]⟩,
   ⟨13, 3, [⟨0, 3, 1, false, []⟩]⟩,
   ⟨18, 96, [⟨48, 24, 3, true, [251]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨14, 96, [⟨48, 24, 3, true, [252]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨15, 12, [⟨3, 3, 3, true, [253]⟩, ⟨3, 3, 3, false, []⟩]⟩]

/-- The third chain's four trees. -/
def told3 : List ProofFile.Root :=
  [⟨18, 96, [⟨48, 24, 3, true, [301]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨15, 72, [⟨24, 24, 3, true, [302]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨13, 72, [⟨24, 24, 3, true, [303]⟩, ⟨0, 24, 1, false, []⟩]⟩,
   ⟨15, 12, [⟨3, 3, 3, true, [304]⟩, ⟨3, 3, 3, false, []⟩]⟩]

/-- **What is told of the three chains' trees.** -/
def toldKeyFull : List ProofFile.Root × List ProofFile.Root × List ProofFile.Root := (told1, told2, told3)

end Johnson.KB4
