-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/SiteRng.lean: at a lookup on the digits, the round that
samples the smallness test's matrix stands in front of the lookup: as a test with code on a public
part's sites, and what an acceptance gives: the input that a lot seats at a site has settled at the
site's base. Conditional on the test's acceptance. Two definitions with code, theorems, tests by
evaluation.

Terms. Honest/K3/GLOSSARY.md. In this file: a site's rng is the number, among the chain's rounds, of
the round that samples the matrix; a site's base is the number of the chain's rounds in front of the
lookup (`Site.rng`, `At.base`; Honest/K3/Lot.lean, Honest/K3/Stages.lean).

Why a test and no theorem at every public part. `siteAt` (Honest/K3/Lot.lean) reads both numbers off
the table of places: rng is `baseIn` at the link's one place of the kind K8, base is `baseIn` at the
lookup's own place. Which of the two places stands first is the order of the table, and the table is
made of `Pub.cuts`, a field of the public part on which the type asks nothing. At a public part
whose table lists the lookup first the inequality is false. So it is a fact of a table, not of the
definitions.

What is defined.
  `rngFrontOn ss`, `rngFrontB Z`: at every site of the list (of the public part) that names such a
    round, its number is below the site's base.

What is shown.
  `rng_front`: where `rngFrontB Z` accepts: for every site s of `lookSites Z` and every i, s.rng =
    some i gives i < s.at_.base.
  `who_digits`: `whoOf s` is a lookup on digits with the round r only where s.rng = some r.
  `settled_of_rng`: **the input that `fastWit` reads at a site is settled at the site's base.**
    Conditional on: the site's rng, where there is one, is below its base (`hr`). `fastWit_settled`
    (Honest/K3/Law/Keep/LotsSame.lean [not in this library; so here read: not proved in this
    library]) has the same statement, with a proof of its own.
  `settled_site`: the same at a site of `lookSites Z`, conditional on `rngFrontB Z = true`.
    (`Spec.settled_site`, Honest/K3/Law/MeetsSite.lean [not in this library], bears the same short
    name and is another statement.)

Hypotheses that remain.
  `h`: `rngFrontB Z = true` (in `rngFrontOn_at`: `rngFrontOn ss = true`; in `who_digits`: what
    `whoOf s` is). `hs`, `hi`: the site is one of the list's, or of the public part's; it names the
    round i. The test has code and reads public data alone. At the release's small example a print
    of the ten sites shows, at the five sites on digits, rng | base: 990 | 993,
    2559 | 2562, 4192 | 4195, 5761 | 5764, 7305 | 7308. No run of the test itself at a real public
    part stands behind this file.

Tests by evaluation. At the synthetic sites of Honest/K3/Lot.lean the test accepts; with the second
site's rng laid at its base, or beyond it, it rejects.

Imported. Honest/K3/LotInstFast.lean for `fastWit`; Honest/K3/WitLaw.lean for `Ask.Settled` and
`askOf_settled`. The frame's files lie beneath them.

Users. Honest/K3/Law/Keep/LotsTested.lean [not in this library] and Honest/K3/LotsPlayedAtZ7.lean
[not in this library] import this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstFast
import Johnson.Desc.ProofFile.Honest.K3.WitLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {W₀ Rc Xi Tr : Type}

/-- At every site of the list that names a round that samples the matrix, that round's number is
below the number of the rounds in front of the lookup. -/
def rngFrontOn (ss : List Site) : Bool :=
  ss.all fun s => s.rng.all fun i => decide (i < s.at_.base)

/-- **The test at a public part's sites.** -/
def rngFrontB (Z : Pub) : Bool := rngFrontOn (lookSites Z)

/-- What an acceptance gives at a list, site by site. -/
theorem rngFrontOn_at (ss : List Site) (h : rngFrontOn ss = true) (s : Site) (hs : s ∈ ss) (i : Nat)
    (hi : s.rng = some i) : i < s.at_.base := by
  have h1 := List.all_eq_true.1 h s hs
  rw [hi] at h1
  exact of_decide_eq_true h1

/-- **Conditional on the test's acceptance: at every site the round that samples the matrix stands
in front of the lookup.** -/
theorem rng_front (Z : Pub) (h : rngFrontB Z = true) (s : Site) (hs : s ∈ lookSites Z) (i : Nat)
    (hi : s.rng = some i) : i < s.at_.base :=
  rngFrontOn_at (lookSites Z) h s hs i hi

/-- `whoOf s` is a lookup on digits with the round r only where the site names r. -/
theorem who_digits (s : Site) (link r : Nat) (h : whoOf s = .digits link r) : s.rng = some r := by
  unfold whoOf at h
  split at h
  · rename_i r' hr
    rw [hr]
    injection h with _ h2
    rw [h2]
  · split at h <;> cases h

/-- **The input that `fastWit` reads at a site has settled at the site's base.** Conditional on
hr: the site's round that samples the matrix, where there is one, stands in front of the lookup. -/
theorem settled_of_rng (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site)
    (hr : ∀ i, s.rng = some i → i < s.at_.base) (t : Local W₀ Rc Xi Tr) :
    Ask.Settled s.at_.base (fastWit cells weights req Z s t) := by
  rw [fastWit_eq]
  exact askOf_settled (sourcesAt cells weights req Z) (whoOf s) t s.at_.base
    fun link r h => hr r (who_digits s link r h)

/-- **The same at every site of the public part.** Conditional on the test's acceptance. -/
theorem settled_site (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (h : rngFrontB Z = true)
    (s : Site) (hs : s ∈ lookSites Z) (t : Local W₀ Rc Xi Tr) :
    Ask.Settled s.at_.base (fastWit cells weights req Z s t) :=
  settled_of_rng cells weights req Z s (rng_front Z h s hs) t

namespace LotToy

-- the synthetic sites: the second names the round just in front of it. It fails if the test turns.
#guard rngFrontOn sites
-- the round's number laid at the base, and beyond it: the test rejects. It fails if "<" becomes
-- "≤", or if the test reads no site.
#guard !rngFrontOn (sites.map fun s => { s with rng := s.rng.map fun _ => s.at_.base })
#guard !rngFrontOn (sites.map fun s => { s with rng := s.rng.map fun _ => s.at_.base + 5 })
-- a list without a site on digits: accepted, over nothing: said so that it is not leaned on
#guard rngFrontOn (sites.filter (!·.digits))

end LotToy

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.rngFrontOn_at
#print axioms ProofFile.Honest.K3.rng_front
#print axioms ProofFile.Honest.K3.who_digits
#print axioms ProofFile.Honest.K3.settled_of_rng
#print axioms ProofFile.Honest.K3.settled_site
