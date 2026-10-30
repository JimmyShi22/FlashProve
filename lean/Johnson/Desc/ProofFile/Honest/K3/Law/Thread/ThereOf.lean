-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ThereOf.lean: the test "the site's place stands in the
written list of places" (the field there of `SiteRest'`, Honest/K3/Law/Thread/LotAtSite.lean)
follows from three smaller public facts. Conditional on these three. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the written list of places is `P5J.At.ps`
(Johnson/P5J/LettersAt.lean). The piece that a site reads off the public structure is `pieceAt`
(Johnson/Desc/First/Look/K3Own.lean); the written one is `pieceOf`
(Johnson/Desc/Sound/MgAt/K3Open.lean).

What is shown.
  `piece_full`: under the first two facts the piece that a site reads off the public structure is
    the written one, at every link.
  `site_link_lt`: a site's link is below the number of links of the first chain's shape.
  `there_of_facts`: the test accepts.

Hypotheses that remain. The three facts, each on public data with a decidable text:
  `h4`: attention links stand between the layers' links (X.p4).
  `hN`: there are twelve groups of layers (X.NGr = 12).
  `hL`: the first chain's shape has at most 25 links.
The first two are the first two clauses of `PlanLabels` (Honest/K3/WitPlan.lean). Besides: `hs`, s
is a site of the public part.

Users. Honest/K3/Law/Thread/SiteThereHead.lean imports this file.

Limits. At the full size alone. The three facts are not shown here of any public part. No instance
of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LotAtSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.K3 (pieceAt isHead)
open VerifiableInference.Desc.Sound.MgAt (pieceOf ixOf borderOf places_are_k3)

/-- **The two texts of a lookup's piece agree at every link.** Conditional on X.p4 and X.NGr = 12.
No instance of these hypotheses is exhibited in this file. -/
theorem piece_full (X : OnBytes.Model.Verify.Public) (h4 : X.p4 = true) (hN : X.NGr = 12)
    (l : Nat) (d : Bool) : pieceAt X l d = pieceOf l d := by
  have e : isHead X l = decide (l = 24) := by
    unfold isHead
    rw [h4, hN]
    by_cases h : l = 24 <;> simp [h]
  unfold pieceAt pieceOf ixOf
  rw [e]
  by_cases h : l = 24 <;> cases d <;> simp [h]

/-- A site's link is below the number of links of the first chain's shape. -/
theorem site_link_lt (Zq : Pub) (s : Site) (hs : s ∈ lookSites Zq) :
    s.link < Zq.first.shape.link.length := by
  unfold lookSites at hs
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, _, f3, _, _, _, _, _⟩ := site_facts _ _ y s hsy
  unfold K3Lot.addresses at hy
  obtain ⟨j, hj, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
  rw [f3]
  exact List.mem_range.1 hj

/-- **The place of every lookup of the public part stands in the written list of places.**
Conditional on X.p4, X.NGr = 12 and at most 25 links. No instance of these hypotheses is exhibited
in this file. -/
theorem there_of_facts (Zq : Pub) (s : Site) (hs : s ∈ lookSites Zq) (h4 : Zq.p.X.p4 = true)
    (hN : Zq.p.X.NGr = 12) (hL : Zq.first.shape.link.length ≤ 25) :
    P5J.At.ps.contains s.at_.place = true := by
  have hl : s.link < 25 := Nat.lt_of_lt_of_le (site_link_lt Zq s hs) hL
  rw [List.contains_iff_mem, site_place Zq s hs, piece_full _ h4 hN]
  exact List.mem_of_getElem? (places_are_k3 hl s.digits)

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.piece_full
#print axioms ProofFile.Honest.K3.Law.AtThr.site_link_lt
#print axioms ProofFile.Honest.K3.Law.AtThr.there_of_facts
