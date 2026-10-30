-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarksList.lean: the list of the lookups' marks at a proof
file's first chain, read off the public part. One definition with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a mark is a value of `ProofFile.Honest.Mark`
(Honest/Law/Marks.lean); a site is a lookup of a public part at its place
(`lookSites`, Honest/K3/Lot.lean); `markK3` and `markOut`: Honest/K3/Good/Mark.lean.

Why a file of its own. Whoever names the list imports its file: so the definition stands over what
its code reads alone, and the lemmas on it stand in Honest/K3/Good/MarksHead.lean, over this file.

What is defined.
  `k3Marks Zp G₀`: at each site of `lookSites Zp`, in that list's order, two marks at the site's
    place and face: `markK3`, then `markOut`. The ground G₀ is not read: it is an argument for the
    sake of one form for all kinds' lists. Each mark's stated share is a written pair of numbers and
    no bound: the number of events over the number of the field's elements.
  No `markRun` stands in the list: why, is said in the head of Honest/K3/Good/MarksHead.lean.

Imported. Honest/K3/Good/Mark.lean; Honest/K3/Lot.lean.

Users. Honest/K3/Good/MarksHead.lean. Meant for a list of all kinds' marks.

Limits. Nothing is shown here. Honest/K3/Good/Mark.lean itself stands over
Honest/K3/Good/MarkEvents.lean, and that over Honest/K3/Good/Gives.lean, a file of laws.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Mark
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good

/-- **The lookups' marks at a proof file's first chain.** The ground is not read. Each stated share
is a written pair of numbers and no bound. -/
def k3Marks (Zp : ProofFile.Pub) (_G₀ : ProofFile.Ground) : List Mark :=
  (lookSites Zp).flatMap fun s => [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face]

end ProofFile.Honest.K3.Good
