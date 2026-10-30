-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TreesSized.lean: what the planner's sizing returns meets, if the caller's links
lie in the class of leaves 0, the premises of the bounds in TreesSites.lean and TreesReq.lean: those
on the six numbers that the plans take from treesOf.

Main names.
  TreeClassCap links: all oracle messages of the links lie in the class of leaves 0.
  sized_tests: three tests that sized (OnBytes/Params/Configure.lean) runs itself have passed where
    it returns: linOk at the proof's and at the key's test on the table, reqOk at the request's
    shape.
  linOk_ok: linOk holds the shape's own test.
  proofSized_request: the request's shape as proofSized (OnBytes/Params/DeriveReq.lean) writes it:
    the code 0, the caller's links with the codes filled in, one notice that rides at the start.
  treeLinkCap_fill: the links with the codes filled in have TreeLinkCap 0 (TreesReq.lean), if the
    caller's have TreeClassCap.
  reqShapeOk_riders: what rides at the start has no main rows.
  sized_caps: all together.

What this file does not claim. That the caller's links have TreeClassCap: the class is written where
a layout file's groups are taken in (Plan.takeGroup, OnBytes/Plan/ReqFrame.lean). Nothing on a plan
or on an entry's number of roots: the other numbers of roots are written out in the planner, and an
entry takes all roots that are open.

The program does not import this file.


-/
import OnBytes.Params.Fit.TreesReq
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes

/-- All oracle messages of the links lie in the class of leaves 0. -/
def TreeClassCap (links : List ReqLink) : Prop :=
  ∀ L ∈ links, ∀ m ∈ L.messages, m.leafClass = 0

/-- Three tests that sized runs itself. -/
theorem sized_tests {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    linOk z.proof.codes z.proof.batch.shape = true ∧
      reqOk z.proof.codes z.proof.request = true ∧
      linOk z.key.codes z.key.once.shape = true := by
  unfold sized at h
  extract_lets s tests at h
  replace h := exc_guard h
  obtain ⟨proof, _, h⟩ := exc_bind h
  have g1 := exc_guard_not h
  replace h := exc_guard h
  obtain ⟨key, _, h⟩ := exc_bind h
  have g2 := exc_guard_not h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  simp only [tests, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, not_or,
    Bool.not_eq_false] at g1 g2
  exact ⟨g1.1.1, g1.2, g2.1⟩

/-- linOk holds the shape's own test. -/
theorem linOk_ok {codes : Codes} {S : LinShape} (h : linOk codes S = true) : S.ok = true := by
  unfold linOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

/-- The request's shape as proofSized writes it. -/
theorem proofSized_request {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.request.code = 0 ∧ z.request.link = fillLinks sub.links ∧
      ∃ n, z.request.atStart = [n] := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, _, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, _, h⟩ := opt_bind h
  cases h
  exact ⟨rfl, rfl, _, rfl⟩

/-- The links with the codes filled in. -/
theorem treeLinkCap_fill {links : List ReqLink} (h : TreeClassCap links) :
    ∀ L ∈ fillLinks links, TreeLinkCap 0 L := by
  intro L hL m hm
  unfold fillLinks at hL
  obtain ⟨L0, hL0, e⟩ := List.mem_map.1 hL
  rw [← e] at hm
  obtain ⟨m0, hm0, e2⟩ := List.mem_map.1 hm
  rw [← e2]
  refine ⟨h L0 hL0 m0 hm0, fun q => ?_⟩
  show (canonical { m0.shape with code := 0, maskCode := 0 }).code = 0
  have q' : m0.shape.mainRows ≠ 0 := q
  unfold canonical
  show (if (m0.shape.mainRows == 0) = true then noId else 0) = 0
  rw [if_neg (by simpa using q')]

/-- What rides at the start has no main rows. -/
theorem reqShapeOk_riders {s : ReqShape} (h : reqShapeOk s = true) :
    ∀ n ∈ s.atStart, n.shape.mainRows = 0 := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro n hn
  have t := List.all_eq_true.1 h.1.1.1.1.2 n hn
  simp only [Bool.and_eq_true, beq_iff_eq] at t
  exact t.1.1.1.1.1

/-- reqOk holds the shape's own test. -/
theorem reqOk_shape {codes : Codes} {s : ReqShape} (h : reqOk codes s = true) :
    reqShapeOk s = true := by
  unfold reqOk at h
  rw [Bool.and_eq_true] at h
  exact h.1

/-- **What sized returns meets the premises of the bounds on the numbers of trees, if the caller's
links lie in the class 0.** -/
theorem sized_caps {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z)
    (hc : TreeClassCap x.sub.links) :
    (∀ L ∈ z.proof.request.link, TreeLinkCap z.proof.request.code L) ∧
      (∀ g ∈ (reqGroups z.proof.request).toList, TreeGroupCap z.proof.request.code g) ∧
      TreeRiderCap z.proof.request.atStart ∧ z.proof.batch.shape.ok = true ∧
      z.key.once.shape.ok = true := by
  obtain ⟨t1, t2, t3⟩ := sized_tests h
  obtain ⟨e0, e1, n, e2⟩ := proofSized_request (sized_proof h)
  have hl : ∀ L ∈ z.proof.request.link, TreeLinkCap z.proof.request.code L := by
    rw [e0, e1]
    exact treeLinkCap_fill hc
  refine ⟨hl, treeGroupCap_groups hl, ⟨n.leafClass, fun k hk => ?_⟩, linOk_ok t1,
    linOk_ok t3⟩
  have hk' := hk
  rw [e2] at hk'
  exact ⟨by rw [List.mem_singleton.1 hk'], reqShapeOk_riders (reqOk_shape t2) k hk⟩

end OnBytes.Params
