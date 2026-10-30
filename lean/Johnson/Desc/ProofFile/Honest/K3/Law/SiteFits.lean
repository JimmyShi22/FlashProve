-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SiteFits.lean: the named hypothesis "the site's numbers of
rounds are the description's own", as a test with code on public data, and what it yields. A
definition with code, three small theorems and six tests by evaluation.

Terms. Honest/K3/GLOSSARY.md ("description", "site", "synthetic", "test by evaluation").

What is shown.
  `siteFits`: the test: the number of rounds in front that the site bears is the chain's own count
    (`roundsInFront`, Honest/ForKinds.lean, on the description's flat list); and, at the digits, the
    round that the site names as the one that samples the smallness test's matrix stands in front of
    the lookup, and just one sub-protocol of the link stands behind so many rounds and has one
    round, named "RNG", which samples matrix entries. The two clauses are the text of two of the
    tests of `siteTests` (Honest/K3/Lot.lean).
  `siteFits_of_tests`: where none of a site's tests rejects (`h`), `siteFits` accepts.
  `base_of_fits`: conditional on `siteFits` (`h`): the site's number is the chain's count.
  `heard_of_fits`: conditional on `siteFits` (`h`): where as many challenges were heard as the chain
    has rounds in front of the place (`ht`), so many were heard as the site's public data says: the
    clause base of `Fit` (Honest/K3/Law/Statements.lean).
  The tests by evaluation, at the synthetic chain of Lot.lean: both sites pass; `siteFits` rejects a
  sub-protocol in front with one round more, a site's number altered by one, and the matrix's round
  under another name, without a matrix entry, or at another number.

Imported. Honest/ForKinds.lean lies beneath this file.

Users. This file is imported by Honest/K3/Law/SeatFitsLaw.lean and
Honest/K3/Law/Thread/SitePays.lean.

Limits. At a site on the digits that names no round (rng = none) the second clause passes idly:
`siteTests` has a test of its own for that ("at the digits alone a round is named that draws the
matrix"), which `siteFits` does not take over. `base_of_fits` and `heard_of_fits` read the first
clause alone. Why this is a hypothesis and no theorem: a site's numbers are added up off the chain's
table of places (`baseIn`, `rngIn`, Lot.lean), since a lot's honest side is given no description.
A theorem would need, of every kind's sub-protocol in front, that it has as many rounds as the table
gives its place. It is shown by evaluation alone, through `siteTests`: the lines of
Honest/K3/LotSheet.lean evaluate `siteTests`, not this test; `siteFits_of_tests` leads from "no
test of the site fails" to an acceptance here. At the description of the shipped small example
no test of the ten sites fails, and a number altered by one
makes its test fail.
`k3Fits`, whose acceptance gives that of `siteFits`
(`fits_gives`, Honest/K3/Law/SeatFitsLaw.lean), is evaluated at a synthetic public part and a
synthetic list of sub-protocols in Honest/K3/SeatFitsAtZ7.lean [not in this library], and accepts at
its ten sites (by evaluation); that list is synthetic: it is no description's.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block)

variable {S Cl W X : Type}

/-- **The hypothesis, as a test with code.** bs: the description's first chain as a flat list. -/
def siteFits (bs : List (Block S Cl)) (s : Site) : Bool :=
  roundsInFront bs s.at_.place == some s.at_.base &&
    s.rng.all fun r =>
      decide (r < s.at_.base) &&
        (bs.filter fun c => c.place.link == some s.link &&
          roundsInFront bs c.place == some r &&
          c.rounds.map (fun d => (d.entry.name, d.entry.trits != 0)) == [("RNG", true)]).length
          == 1

/-- Conditional on `siteFits`: the site's number of rounds in front is the chain's own count. -/
theorem base_of_fits (bs : List (Block S Cl)) (s : Site) (h : siteFits bs s = true) :
    roundsInFront bs s.at_.place = some s.at_.base := by
  simp only [siteFits, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- Conditional on `siteFits`: where as many challenges were heard as the chain has rounds in front
of the place, so many were heard as the site's public data says. -/
theorem heard_of_fits (bs : List (Block S Cl)) (s : Site) (h : siteFits bs s = true)
    (t : State W X) (ht : roundsInFront bs s.at_.place = some t.heard.length) :
    t.heard.length = s.at_.base :=
  Option.some.inj (ht.symm.trans (base_of_fits bs s h))

/-- **Where none of a site's tests (`siteTests`, Honest/K3/Lot.lean) rejects, `siteFits` accepts**:
so a print of the lines of Honest/K3/LotSheet.lean on which no test of a site fails shows the
hypothesis there. -/
theorem siteFits_of_tests {V : Type} (bs : List (Block S Cl)) (s : Site)
    (g : Option (Placed V W X)) (h : failing (siteTests bs s g) = []) : siteFits bs s = true := by
  have hall : ∀ t ∈ siteTests bs s g, t.2 = true := by
    intro t ht
    unfold failing at h
    have h' := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 h) t ht
    simpa using h'
  have h1 := hall ("the rounds in front are the chain's own count",
    roundsInFront bs s.at_.place == some s.at_.base) (by simp [siteTests])
  have h2 := hall ("that round is the link's, named RNG, draws matrix entries, and stands in front",
    s.rng.all fun r =>
      decide (r < s.at_.base) &&
        (bs.filter fun c => c.place.link == some s.link &&
          roundsInFront bs c.place == some r &&
          c.rounds.map (fun d => (d.entry.name, d.entry.trits != 0)) == [("RNG", true)]).length
          == 1) (by simp [siteTests])
  simp only [siteFits, Bool.and_eq_true]
  exact ⟨h1, h2⟩

namespace SiteToy
open LotToy

-- The synthetic chain of Honest/K3/Lot.lean: both sites pass.
#guard sites.all (siteFits chain)
-- A sub-protocol in front with one round more; a site's number altered by one: rejected.
#guard !(sites.any (siteFits (chain 4)))
#guard !siteFits chain (site false 4)
-- The matrix's round under another name; without a matrix entry; at another number: rejected.
#guard !siteFits (chain 3 0 "BAT-sigma") (site true (3 + len + 2))
#guard !siteFits (chain 3 0 "RNG" 0) (site true (3 + len + 2))
#guard !siteFits chain { site true (3 + len + 2) with rng := some (3 + len) }

end SiteToy

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.siteFits_of_tests
#print axioms ProofFile.Honest.K3.Law.base_of_fits
#print axioms ProofFile.Honest.K3.Law.heard_of_fits
