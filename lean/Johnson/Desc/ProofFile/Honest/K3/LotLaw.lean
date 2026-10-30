-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotLaw.lean: of the sub-protocols that the lookups' lot hands the
proof file's description (`K3Lot.hear`, Johnson/Desc/ProofFile/Lot/K3.lean): the rounds of each are
the rounds of the verifier's own parameters at its place, and no more: the step without a round that
is joined behind the kind's sub-protocol at some places, and the run of claims "planes", add none.
One definition and theorems.

Terms. Honest/K3/GLOSSARY.md ("lot", "site", "public parameters (of a lookup)", "step without a
round", "member").

What is shown.
  `FromPlace`: what is said of a sub-protocol at an address: a link's number, which of its two
    lookups, the place's parameters; the sub-protocol's rounds are these parameters'.
  `theOwn_from`, `theWhole_from`, `theStated_from`: it holds of the value of `K3.theOwn`,
    `K3.theWhole` and `K3.theStated` at every address at which there is one.
  `hear_from`: it holds of every sub-protocol of the lot.
  `pieceAt_inj`: a link's two lookups stand at two pieces.
  `hear_site`: where a site is made at an address of the lot's list and the lot makes a sub-protocol
    there, the sub-protocol's rounds are the rounds of the site's own parameters.
  `siteAt_rng`: a site names a round that samples the smallness test's matrix at the digits, and at
    no other address.

Hypotheses that remain.
  `h`: in `theOwn_from`, `theWhole_from`, `theStated_from`: the function returns the sub-protocol b
    at the address; in `hear_from`: b is one of the lot's; in `pieceAt_inj`: the two pieces are one.
  `hx`, `hs`, `hb`: (in `hear_site`) the address is one of the lot's list; a site is made there; the
    lot's own call of `theStated` returns b there (`hb` writes out the call inside `K3Lot.hear`).
    `hs`: (in `siteAt_rng` too) a site is made at the address.

Why. A row of the honest side must have a move for each round of the sub-protocol at its place. The
row's numbers come of the site's face, which is made of the same parameters (`siteAt`,
Honest/K3/Lot.lean).

Limits. The file speaks of the lot's sub-protocols. The description's member at the place is that
sub-protocol as the description's makers have wrapped it: that the wrapping adds no round is not
shown here (shown in: Honest/K3/Law/MemberAtSite.lean, `memberAtSite`: the member has the
sub-protocol's rounds, where the description returns); the tests of Lot.lean compare the member's
rounds by number, where a program evaluates them. That the parameters' rounds (the planner's
entries) are those of the face's stages is the sub-protocol's own test on the plan
(`K3.Law.fitsVia`) together with the tests of Honest/K3/RowGuards.lean [not in this library], and is
not shown here. Shown in part: Honest/K3/Law/PlanOkGives.lean (`theOwn_plan`, `theWhole_plan`,
`theStated_plan`), conditional on the sub-protocol's test on the plan: the plan's entries are, but
for the work bits, those that the hearing at the shape's face goes by; and Honest/K3/RowLaw.lean
(`entries_stages`): these are the stages' rounds, at two planes at least. The work bits stay out. No
instance of these hypotheses is exhibited in this file. That the lot has a sub-protocol at all is
seen at a description alone. Shown in: Honest/K3/Law/LotOfSite.lean (`lot_of_site`): where the
description returns, the lot has a sub-protocol at every site's place.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3 (pieceAt theOwn theWhole theStated)

/-- A sub-protocol at the address a has the rounds of the verifier's own parameters there. -/
def FromPlace {Cl : Type} (X : OnBytes.Model.Verify.Public) (a : Place) (b : Block S Cl) : Prop :=
  ∃ i digits p, a.link = some i ∧ a.piece = pieceAt X i digits ∧ placeAt X i digits = some p ∧
    b.rounds = p.rounds

theorem theOwn_from {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theOwn claim runs X codes shape a = some b) :
    FromPlace X a b := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hp
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, hpl, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      refine ⟨i, digits, p, hi, by simpa using hp, hpl, ?_⟩
      cases runs <;> rfl

theorem theWhole_from {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theWhole claim runs X codes shape a = some b) :
    FromPlace X a b := by
  unfold theWhole at h
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨i, digits, p, h1, h2, h3, h4⟩ := theOwn_from claim runs X codes shape a b₀ hb
  refine ⟨i, digits, p, h1, h2, h3, ?_⟩
  split
  · show b₀.rounds ++ [] = p.rounds
    rw [List.append_nil, h4]
  · exact h4

theorem theStated_from {Cl : Type} (claim : OnBytes.Model.Aff → Cl)
    (readers : Nat → Option (VerifiableInference.Desc.K3.Readers S))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block S Cl) (h : theStated claim readers X codes shape a = some b) :
    FromPlace X a b := by
  unfold theStated at h
  obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨i, digits, p, h1, h2, h3, h4⟩ := theWhole_from claim true X codes shape a b₀ hb
  refine ⟨i, digits, p, h1, h2, h3, ?_⟩
  split at h
  · obtain rfl := Option.some.inj h
    exact h4
  · split at h
    · obtain rfl := Option.some.inj h
      exact h4
    · split at h
      · obtain rfl := Option.some.inj h
        exact h4
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact h4

/-- **Every sub-protocol of the lookups' lot has the rounds of the verifier's own parameters at its
address**, which is one of the lot's list. -/
theorem hear_from (Z : Pub) (b : Block S Cl) (h : b ∈ K3Lot.hear Z) :
    ∃ x ∈ K3Lot.addresses Z, FromPlace Z.p.X x.2.2 b := by
  unfold K3Lot.hear at h
  obtain ⟨x, hx, hb⟩ := List.mem_filterMap.1 h
  exact ⟨x, hx, theStated_from _ _ _ _ _ _ b hb⟩

/-- A link's two lookups stand at two pieces. -/
theorem pieceAt_inj (X : OnBytes.Model.Verify.Public) (i : Nat) (d d' : Bool)
    (h : pieceAt X i d = pieceAt X i d') : d = d' := by
  unfold pieceAt at h
  cases d <;> cases d' <;> first | rfl | (exfalso; revert h; split <;> decide)

/-- **At an address of the lot's list: the lot's sub-protocol has the rounds of
the site's parameters.** -/
theorem hear_site (Z : Pub) (ps : List Spot) (x : Nat × Bool × Place) (hx : x ∈ K3Lot.addresses Z)
    (s : Site) (hs : siteAt Z.p.X ps x = some s) (b : Block S Cl)
    (hb : theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape x.2.2 =
      some b) :
    b.rounds = s.p.rounds := by
  obtain ⟨i, d, p, h1, h2, h3, h4⟩ := theStated_from _ _ _ _ _ _ b hb
  unfold K3Lot.addresses at hx
  obtain ⟨j, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
  obtain rfl : j = i := Option.some.inj h1
  obtain rfl : e = d := pieceAt_inj _ _ _ _ h2
  unfold siteAt at hs
  obtain ⟨p', hp', hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain rfl : p = p' := Option.some.inj (h3.symm.trans hp')
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact h4
  · obtain rfl := Option.some.inj hs
    exact h4

/-- **A site that `siteAt` makes names a round that samples the matrix at the digits, and at no
other address.** -/
theorem siteAt_rng (X : OnBytes.Model.Verify.Public) (ps : List Spot) (x : Nat × Bool × Place)
    (s : Site) (hs : siteAt X ps x = some s) : s.rng.isSome = s.digits ∧ s.digits = x.2.1 := by
  unfold siteAt at hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · rename_i hd
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact ⟨hd.symm, rfl⟩
  · rename_i hd
    obtain rfl := Option.some.inj hs
    exact ⟨(Bool.eq_false_iff.2 hd).symm, rfl⟩

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.siteAt_rng
#print axioms ProofFile.Honest.K3.theOwn_from
#print axioms ProofFile.Honest.K3.theWhole_from
#print axioms ProofFile.Honest.K3.theStated_from
#print axioms ProofFile.Honest.K3.hear_from
#print axioms ProofFile.Honest.K3.pieceAt_inj
#print axioms ProofFile.Honest.K3.hear_site
