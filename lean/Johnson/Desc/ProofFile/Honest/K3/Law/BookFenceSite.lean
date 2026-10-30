-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/BookFenceSite.lean: the honest side of the kind "lookup" (K3):
`named_reads` (Honest/K3/Law/BookFence.lean) at a site of a public part: there the hypothesis on the
face's planes is paid. Two theorems.

Why. `DigitsRunAll` (Honest/K3/Law/Thread/ExchangeDigitsAll.lean) reads a coin by `getD … zeroE` at
s.p.first + s.at_.face.slots entries, beside the two tests `bookFits` and `startsFit` at s.at_ and
s.p.first. `named_reads` bounds these indices under the two tests and "at least two planes", which
does not stand in that definition.

What is shown.
  `planes_site`: at a site's face there are at least two planes. No hypothesis but the site.
  `named_reads_site`: at a site, under the two tests as that definition spells them: at every
    j below s.p.first + s.at_.face.slots the index base.e + j is below the length of the owner's
    list of coins.

Hypotheses that remain. The site; `hb`, `hst`: the two tests: hypotheses on a book that other
files make; no theorem of this file shows them.

Imported. Honest/K3/Law/BookFence.lean and Honest/K3/Law/SitesOk.lean, and what stands beneath them.

Users. None in code; named in the docstring of `DigitsRunAll`. No theorem joins it to that
definition: its two hypotheses are two of its conjuncts by reading.

Limits. Nothing shows that a book passes the two tests. Nothing on what a coin is, on who lays it or
on what is sent.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.BookFence
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law

/-- At a site's face there are at least two planes. No premise but the site. -/
theorem planes_site (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) : 2 ≤ s.at_.face.planes := by
  rw [(sites_shape_ok Z s hs).1]
  exact (by decide : 2 ≤ 32)

/-- **At a site, under the two tests, the reading in `DigitsRunAll` never takes the default.** -/
theorem named_reads_site (Bk : ProverCoinCounts) (k : Coins Bk) (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (ow : Addr) (base : Due)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hst : startsFit Bk s.at_ s.p.first ow base = true) :
    ∀ j, j < s.p.first + s.at_.face.slots → base.e + j < (coinsE (k.look 0 ow).2).length :=
  named_reads Bk k s.at_ s.p.first ow base (planes_site Z s hs) hb hst

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.planes_site
#print axioms ProofFile.Honest.K3.Law.named_reads_site
