-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBuiltCut.lean.
A run of builtOf, cut: the verifier's own tests on what the first chain's parameter bytes hold as
read back.

The routine planned (OnBytes/Model/Verify.lean) ends in builtOf (OnBytes/Model/VerifyStages.lean),
which runs buildLinksH (OnBytes/Model/StagesLinks.lean) on the links of the public part and on
c.proof.first: the first chain's parameter bytes as read back.
OnBytes/Tie/Pv/Lookup/Ends/FoBuilt.lean has that step's equation (planned_built) and the links that
it returns. This file keeps the yes of five of its tests and says of four what the yes means.

* built_cut: a run of builtOf: the links, the links with their declared arrays, and the yes of
  heldAgainst, tableRows, tableHeld, reqOk and numbersHeld.
* heldAgainst_cut: there are as many links in the shape and in the layout as are declared, and each
  passes linkHeld.
* numbersHeld_cut: the links' plain scalars are 0, .., 0, 1; the pending rows are onTable links; the
  identifiers are the links'.
* tableRows_cut, tableHeld_cut: onTable links = NGr + 1; the rows and the column bits of the test on
  the table are the weight table's. The yes of reqOk is kept and not cut. Dropped: the yes of
  headLast, linksCount, weightLimbs, listedFits and linksFit.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBuilt
import OnBytes.Plan.PlanListsConfigure
import OnBytes.Chain.Lists

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params OnBytes.Plan

/-- A run of builtOf, cut: the links and their declared arrays, and the yes of the tests on what the
first chain's parameter bytes hold as read back. -/
theorem built_cut {X : Public} {c : Chains} {B : LinksH} (h : builtOf X c = .ok B) :
    ∃ links0 links declared, linksOf X default = .ok links0 ∧
      declareLinks links0 X.NGr X.p4 = .ok (links, declared) ∧
      heldAgainst declared c.proof.first = .ok () ∧ tableRows links X.NGr = .ok () ∧
      Stages.tableHeld X.layers.wsLay c.proof.first = .ok () ∧
      reqOk c.proof.first.codes c.proof.first.shape = true ∧
      numbersHeld links c.proof.first = .ok () := by
  unfold builtOf at h
  obtain ⟨l0, h0, h⟩ := exc_bind h
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, h4, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h5, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h7, h⟩ := exc_bind h
  have h8 := exc_guard_not h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h11, h⟩ := exc_bind h
  exact ⟨l0, named, declared, h0, h3, h4, h5, h7, by simpa using h8, h11⟩

/-- The yes of heldAgainst. -/
theorem heldAgainst_cut {declared : Array FrameLink} {p : First}
    (h : heldAgainst declared p = .ok ()) :
    declared.size = p.shape.link.length ∧ declared.size = p.layout.link.length ∧
      ∀ (i : Nat) (D : FrameLink) (L : ReqLink) (A : List ReqArray), declared[i]? = some D →
        p.shape.link[i]? = some L → p.layout.link[i]? = some A → linkHeld D L A = true := by
  unfold heldAgainst at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨e1, e2⟩, e3⟩ := hc
    refine ⟨e1, e2, fun i D L A hD hL hA => ?_⟩
    rw [zipT_eq, zipT_eq, List.all_eq_true] at e3
    refine e3 (D, L, A) (List.mem_of_getElem? (i := i) ?_)
    rw [List.getElem?_zip_eq_some]
    refine ⟨by rw [Array.getElem?_toList]; exact hD, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨hL, hA⟩
  · cases h

/-- The yes of numbersHeld. -/
theorem numbersHeld_cut {links : Array LinkH} {p : First} (h : numbersHeld links p = .ok ()) :
    p.shape.link.map (·.plain) = List.replicate (links.size - 1) 0 ++ [1] ∧
      p.pendingRows = onTable links ∧ p.identifiers = links.toList.map (·.gid) := by
  unfold numbersHeld at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2⟩
  · cases h

/-- The yes of tableRows. -/
theorem tableRows_cut {links : Array LinkH} {NGr : Nat} (h : tableRows links NGr = .ok ()) :
    onTable links = NGr + 1 := by
  unfold tableRows at h
  split at h
  · cases h
  · rename_i hc
    simpa using hc

/-- The yes of tableHeld. -/
theorem tableHeld_cut {wsLay : WsLay} {p : First} (h : Stages.tableHeld wsLay p = .ok ()) :
    p.lin.matrixRows = wsLay.m0 ∧ p.lin.kCol = wsLay.lk := by
  unfold Stages.tableHeld at h
  split at h
  · cases h
  · rename_i hc
    simpa using hc

end Fo
