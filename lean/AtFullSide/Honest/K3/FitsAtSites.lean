-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/FitsAtSites.lean: the kind "lookup" (K3): under the library's one hypothesis at
the full size (`P5J.AtMgA`, "the head") at each of the goals' two named sets of public files
(`VerifierAndGoals.NamedFiles`): at every site of `lookSites Zp` the three public tests on the frame's book
(`bookFits`, `placeFits`: Honest/K3/Law/RowLends.lean; `startsFit`: Honest/K3/Law/MasksBook.lean)
accept whatever book `bookWhole` returns at the written description, at the site's own record and
first scalar, with the owner and the base of the link's mask row. One closed fact by Lean's kernel
with a negative test; one theorem; no definition.

What is shown.
  `k3SitesW_are`: the fifty written members `k3SitesW` (AtFullSide/K14/RawK3Sites.lean),
  in what the three tests read of them (place, parts, d, first scalar), are the list made
  of the library's addresses `IM.k3Place`, the table `vdW` (ViewNumbers.lean) and the library's
  written first scalars `firstW`. By Lean's kernel, on written data alone. `k3SitesW_bent`: a
  negative test: with every first scalar raised by one the two lists part. `k3Fits_at_sites`: the
  first sentence.

How the proof goes. `link_lt_head`, `site_place_head` (Honest/K3/Law/Thread/): the site's link is
below 25 and its place is `IM.k3Place` there. `site_numbers` at `six_head_named` (SixAtGap.lean):
its three numbers. `sites_ok` (Honest/K3/FastLaw/Sites.lean): its face is `faceOf` of its shape:
five fields by `rfl`. `k3SitesW_are`: the written member at that link and sort. Then one call of
`k3Fits_written` (AtFullSide/K14/RawK3Fits.lean) at the site's own record.

Hypotheses that remain. `hZ`: Z is one of the two named sets. `h`: the head at Z, at every member.
`hB`: `bookWhole` returns B at the written description, the written sendings and the merges by name;
`bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean) has such a book.


Limits, after those of the files called, which all hold here. B is the book at the WRITTEN
description: that it is the book of a thread or of a prover is not said here. At the two named sets
alone. At the stages that send nothing, 4 + v + d of a site's 37 + 2 (v + d), `bookFits` and
`startsFit` say only that no entry names the part. Nothing on a sender's text, a filling or a run.
The laws over these tests stand at the elder row `proverSideOfLookupInChainAtOneOwner`. The merges are a guess off names; the
written description's values were printed by Lean's evaluator (the heads of the files called say
so).

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.ViewNumbers
import AtFullSide.Honest.K3.SixAtGap
import AtFullSide.K14.RawK3Fits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open Johnson.AtFull.Lots.K3 (sortOf firstW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- The hash build's fifty written members, in what the three tests read of them, are the list made
of the library's addresses, our written table and the library's written first scalars. -/
theorem k3SitesW_are :
    AtFullSide.K14.k3SitesW.map (fun s => (s.at_.place, s.at_.face.parts, s.at_.face.d, s.first)) =
      (List.range 25).flatMap fun l => [false, true].map fun d =>
        (IM.k3Place l d, [(vdW (sortOf l) d).1], (vdW (sortOf l) d).2, firstW (sortOf l) d) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: with every member's first scalar raised by one the two lists part. -/
theorem k3SitesW_bent :
    decide (AtFullSide.K14.k3SitesW.map
        (fun s => (s.at_.place, s.at_.face.parts, s.at_.face.d, s.first + 1)) =
      (List.range 25).flatMap fun l => [false, true].map fun d =>
        (IM.k3Place l d, [(vdW (sortOf l) d).1], (vdW (sortOf l) d).2, firstW (sortOf l) d)) = false
        := by
  decide +kernel

/-- **THE TIE, AT EACH OF THE TWO NAMED SETS.** -/
theorem k3Fits_at_sites {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.NamedFiles Z) {D r Zp Np cF x}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits B (B.rowsOf 0) (dueAt B.first) s.at_ = true ∧
      startsFit B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits B (B.rowsOf 0) s.at_ = true := by
  intro s hs
  have hl := AtThr.link_lt_head h s hs
  have hp := AtThr.site_place_head h s hs
  obtain ⟨n1, n2, n3⟩ := site_numbers Zp s hs (six_head_named hZ h s.link hl)
  obtain ⟨hf, _⟩ := FastLaw.sites_ok Zp s hs
  have hm : (IM.k3Place s.link s.digits, [(vdW (sortOf s.link) s.digits).1],
      (vdW (sortOf s.link) s.digits).2, firstW (sortOf s.link) s.digits) ∈
      AtFullSide.K14.k3SitesW.map
        (fun w => (w.at_.place, w.at_.face.parts, w.at_.face.d, w.first)) := by
    rw [k3SitesW_are]
    exact List.mem_flatMap.2 ⟨s.link, List.mem_range.2 hl,
      List.mem_map.2 ⟨s.digits, by cases s.digits <;> simp, rfl⟩⟩
  obtain ⟨w, hw, e⟩ := List.mem_map.1 hm
  have e1 : w.at_.place = IM.k3Place s.link s.digits := congrArg (·.1) e
  have e2 : w.at_.face.parts = [(vdW (sortOf s.link) s.digits).1] := congrArg (·.2.1) e
  have e3 : w.at_.face.d = (vdW (sortOf s.link) s.digits).2 := congrArg (·.2.2.1) e
  have e4 : w.first = firstW (sortOf s.link) s.digits := congrArg (·.2.2.2) e
  obtain ⟨l, r', hlk, hr, H⟩ := AtFullSide.K14.k3Fits_written hB w hw
  have hl' : l = s.link := by
    rw [e1] at hlk
    exact (Option.some.inj hlk).symm
  subst hl'
  obtain ⟨b1, b2, b3⟩ := H s.at_ (hp.trans e1.symm) (by rw [hf]; rfl) (by rw [hf]; rfl)
    (by rw [hf]; rfl) (by rw [hf, e2, ← n2]; rfl) (by rw [hf, e3, ← n3]; rfl)
  exact ⟨r', hr, b1, by rw [n1, ← e4]; exact b2, b3⟩

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.k3SitesW_are
#print axioms AtFullSide.Honest.K3.k3SitesW_bent
#print axioms AtFullSide.Honest.K3.k3Fits_at_sites
