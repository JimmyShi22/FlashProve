-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarksLooks.lean: under the library's hypothesis `P5J.AtMgA`,
the two marks of the lookup on the digits at each of the 25 links, told by the block's own place and
the built link's own shape, are among the lookups' marks `k3Marks`. The digits' half alone.
Conditional. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: a link's lookup on the digits is the block at number
`borderOf l true` of the first chain's flat list; f9 is the shape of that lookup in a link's
structure of the smallness test.

Why. A hypothesis in another file asks, at each link below 25, that `markK3` and
`markOut` at that block's place and at the face of the built link's f9 stand in a list of marks.
`k3Marks` (Honest/K3/Good/MarksList.lean) is told by the sites of `lookSites`. That the one fifty
are among the other hundred wants five ties, which lie in this folder's files, and one variant.

What is shown.
  `built_tl_pub`: **conditional on `P5J.AtMgA`: the plan's structure at link l is the one of
    `Zp.p.built.links[l]`.** The variant of `built_tl_head`
    (Honest/K3/Law/Thread/DigitsF9Reach.lean), which speaks of a ground's built links under an
    opening; here no opening is asked.
  `site_of_look`: conditional on `P5J.AtMgA`: at l below 25, the built link X and the block blk: a
    site of `lookSites Zp` has the place blk.place and the face `faceOf X.tl.f9`.
  `marks_looks`: **conditional on `P5J.AtMgA`: both marks at (blk.place, faceOf X.tl.f9) are in
    `k3Marks Zp G₀`.**
  `marks_looks_sub`: **the same in every list that holds `k3Marks Zp G₀`.**
  `looks_there`: the hypotheses can be met: conditional on `P5J.AtMgA`: at every l below 25 there
    are a built link X and a block blk that meet the two hypotheses of `marks_looks`.

Hypotheses that remain. `h`: `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): no instance is exhibited in
this file. `hl`: the link's number is below 25. `e`, `hX`: X is the public part's built link number
l. `hb`: blk is the block at the border of link l's lookup on the digits. (In `marks_looks` and
`marks_looks_sub` these three stand inside the statement.) `hsub`: (in `marks_looks_sub`) the list
holds `k3Marks Zp G₀`.

Imported. Honest/K3/Good/MarksList.lean; Honest/K3/Law/Thread/SiteAllFifty.lean;
Honest/K3/Law/SitesOk.lean; Honest/K3/Law/Thread/DigitsShapeHead.lean;
Johnson/P5T/DigStaticAtMg.lean; Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean;
Johnson/HB/LLHARD/BuiltAtName.lean.


Limits. At the full size alone (25 links), as `P5J.AtMgA`. The lookups on calls (`borderOf l false`)
are not treated: of the hundred marks of `k3Marks` these are fifty. `marks_looks_sub` is typed after
the body of a definition in another file, as a note gives it; that its letters for
the state, the claim, a mark, a built link, the border and the face are the types and functions of
this file is a reading: only a call in Lean over both files shows it. Nothing is said on a mark's
share or on what a mark's silence gives.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksList
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAllFifty
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsShapeHead
import Johnson.P5T.DigStaticAtMg
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.HB.LLHARD.BuiltAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (tlAt)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The plan's structure at link l is the one of the public part's built link.** Conditional on
`P5J.AtMgA`. -/
theorem built_tl_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    {X : LinkH} (e : Zp.p.built.links[l]? = some X) : tlAt Zp.p.X l = some X.tl := by
  obtain ⟨b', hb', e'⟩ := ProofFile.Law.pub_builtOf h.laid.pub
  rw [← e'] at e
  have e2 : (b'.links.map ProofFile.Law.blank)[l]? = some X := e
  rw [Array.getElem?_map] at e2
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 e2
  show tlAt Zp.p.X l = some Y.tl
  exact VerifiableInference.Desc.LinkJoin.tlAt_of_built h.scope h.reads h.pubOne hb' hl hY

/-- A site has the block's place and the face of the built link's f9. Conditional on `P5J.AtMgA`. -/
theorem site_of_look (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (X : LinkH) (blk : Block TS ProofFile.Cl) (hX : Zp.p.built.links[l]? = some X)
    (hb : cF.blocksInOrder[borderOf l true]? = some blk) :
    ∃ s ∈ lookSites Zp, s.at_.place = blk.place ∧ s.at_.face = faceOf X.tl.f9 := by
  obtain ⟨s, hs, e1, e2, e3, _⟩ := Law.AtThr.site_at_all_fifty h l hl true
  obtain ⟨_, _, _, _, blk', hb', hp, _⟩ := Law.AtThr.digits_heard_all h l hl
  rw [hb] at hb'
  obtain rfl := Option.some.inj hb'
  obtain ⟨tlP, ht, e4⟩ := Law.AtThr.site_f9_head h s hs e2
  rw [e1, built_tl_pub h l hl hX] at ht
  obtain rfl := Option.some.inj ht
  exact ⟨s, hs, e3.trans hp.symm, ((Law.sites_shape_ok Zp s hs).1).trans (by rw [e4])⟩

/-- **Both marks are among the lookups' marks.** Conditional on `P5J.AtMgA`. -/
theorem marks_looks (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    ∀ l < 25, ∀ (X : LinkH) (blk : Block TS ProofFile.Cl),
      Zp.p.built.links[l]? = some X → cF.blocksInOrder[borderOf l true]? = some blk →
        markK3 blk.place (faceOf X.tl.f9) ∈ k3Marks Zp G₀ ∧
          markOut blk.place (faceOf X.tl.f9) ∈ k3Marks Zp G₀ := by
  intro l hl X blk hX hb
  obtain ⟨s, hs, ep, ef⟩ := site_of_look h l hl X blk hX hb
  unfold k3Marks
  rw [← ep, ← ef]
  exact ⟨List.mem_flatMap.2 ⟨s, hs, List.mem_cons_self⟩,
    List.mem_flatMap.2 ⟨s, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

/-- **The same in every list that holds the lookups' marks.** Conditional on `P5J.AtMgA`. -/
theorem marks_looks_sub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground)
    (hm : List Mark) (hsub : k3Marks Zp G₀ ⊆ hm) :
    ∀ l < 25, ∀ (X : LinkH) (blk : Block TS ProofFile.Cl),
      Zp.p.built.links[l]? = some X → cF.blocksInOrder[borderOf l true]? = some blk →
        markK3 blk.place (faceOf X.tl.f9) ∈ hm ∧ markOut blk.place (faceOf X.tl.f9) ∈ hm :=
  fun l hl X blk hX hb =>
    ⟨hsub (marks_looks h G₀ l hl X blk hX hb).1, hsub (marks_looks h G₀ l hl X blk hX hb).2⟩

/-- **The hypotheses can be met**: at every link below 25 the two hypotheses of `marks_looks` can
be met. Conditional on `P5J.AtMgA`. -/
theorem looks_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (X : LinkH) (blk : Block TS ProofFile.Cl),
      Zp.p.built.links[l]? = some X ∧ cF.blocksInOrder[borderOf l true]? = some blk := by
  have hsz : Zp.p.built.links.size = 25 := P5J.built_size h.scope h.laid
  obtain ⟨_, _, _, _, blk, hb, _⟩ := Law.AtThr.digits_heard_all h l hl
  exact ⟨_, blk, Array.getElem?_eq_getElem (by omega), hb⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.built_tl_pub
#print axioms ProofFile.Honest.K3.Good.site_of_look
#print axioms ProofFile.Honest.K3.Good.marks_looks
#print axioms ProofFile.Honest.K3.Good.marks_looks_sub
#print axioms ProofFile.Honest.K3.Good.looks_there
