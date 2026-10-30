-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/KeptRowsPos.lean: in every group of a lawful request's shape, every kept member
of the target of the switch into the group has a main row.

reqGroups (OnBytes/Iop/Req.lean) makes the groups' targets of the shape alone: the kept members of
group l are the messages that are alive before it, each born of a link's message with a life; and
reqMessageOk asks of a message with a life that it has main rows. ReqFrame.start (same file) lays
groups := reqGroups shape and refuses a shape without reqOk.
  links_ok: reqShapeOk gives reqLinkOk at every link.
  groupAt_pos: one group: the kept members of its target, and the messages alive behind it.
  groupsFrom_pos, kept_pos: all groups.
  kept_pos_at: at group number l, in the letters of the test that is asked at a code switch:
    ∀ i (h : i < T.kept.size), 0 < T.kept[i].shape.mainRows.
Not claimed: that a record's frame holds reqGroups of a plan's shape.
-/
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)

/-- Every message that is alive has a main row. -/
def AlivePos (alive : List ReqAlive) : Prop := ∀ a ∈ alive, 0 < a.shape.mainRows

theorem links_ok {s : ReqShape} (h : reqShapeOk s = true) : ∀ L ∈ s.link, reqLinkOk L = true := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  have a := h.1.1.1.1.1.1.2
  intro L hL
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hL
  have m : (L, i) ∈ s.link.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hi, e]
  exact (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 a (L, i) m).1

theorem life_pos {m : ReqMessage} (h : reqMessageOk m = true) (hl : (m.life == 0) = false) :
    0 < m.shape.mainRows := by
  unfold reqMessageOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with a | a
  · rw [hl] at a
    cases a
  · have b : m.shape.mainRows ≠ 0 := by simpa using a.1.1
    omega

theorem groupAt_pos {s : ReqShape} (hs : ∀ L ∈ s.link, reqLinkOk L = true) (l : Nat)
    {alive : List ReqAlive} (ha : AlivePos alive) :
    (∀ k ∈ (reqGroupAt s l alive).1.target.kept.toList, 0 < k.shape.mainRows) ∧
      AlivePos (reqGroupAt s l alive).2 := by
  unfold reqGroupAt
  dsimp only
  refine ⟨fun k hk => ?_, fun a hm => ?_⟩
  · obtain ⟨a, h1, rfl⟩ := List.mem_map.1 hk
    exact ha a h1
  · rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨b, h1, rfl⟩ := List.mem_map.1 hm
      exact ha b (List.mem_filter.1 h1).1
    · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hm
      have hmem : x.1 ∈ (s.link[l]?.map (·.messages)).getD [] := by
        have := List.mem_zipIdx_iff_getElem?.1 hx
        exact List.mem_of_getElem? this
      cases hL : s.link[l]? with
      | none =>
        rw [hL] at hmem
        cases hmem
      | some L =>
        rw [hL] at hmem
        have hok := hs L (List.mem_of_getElem? hL)
        unfold reqLinkOk at hok
        simp only [Bool.and_eq_true] at hok
        have hm1 := List.all_eq_true.1 hok.2 x.1 hmem
        by_cases h0 : (x.1.life == 0) = true
        · rw [if_pos h0] at e
          cases e
        · rw [if_neg h0] at e
          obtain rfl := Option.some.inj e
          exact life_pos hm1 (by simpa using h0)

theorem groupsFrom_pos {s : ReqShape} (hs : ∀ L ∈ s.link, reqLinkOk L = true) :
    ∀ (count l : Nat) (alive : List ReqAlive), AlivePos alive →
      ∀ G ∈ reqGroupsFrom s count l alive, ∀ k ∈ G.target.kept.toList, 0 < k.shape.mainRows
  | 0, _, _, _, G, hG => by cases hG
  | count + 1, l, alive, ha, G, hG => by
    unfold reqGroupsFrom at hG
    rcases List.mem_cons.1 hG with rfl | hG
    · exact (groupAt_pos hs l ha).1
    · exact groupsFrom_pos hs count (l + 1) _ (groupAt_pos hs l ha).2 G hG

/-- **In every group of a lawful shape.** -/
theorem kept_pos {s : ReqShape} (h : reqShapeOk s = true) :
    ∀ G ∈ (reqGroups s).toList, ∀ k ∈ G.target.kept.toList, 0 < k.shape.mainRows := by
  rw [reqGroups_eq]
  exact groupsFrom_pos (links_ok h) _ 0 [] fun _ hm => by cases hm

/-- At group number l, in the letters of the test at a code switch. -/
theorem kept_pos_at {s : ReqShape} (h : reqShapeOk s = true) {l : Nat} {G : ReqGroup}
    (hG : (reqGroups s)[l]? = some G) :
    ∀ i (hi : i < G.target.kept.size), 0 < G.target.kept[i].shape.mainRows := fun _ hi =>
  kept_pos h G (Array.mem_toList_iff.2 (Array.mem_of_getElem? hG)) _
    (Array.mem_toList_iff.2 (Array.getElem_mem hi))

/-- From the test that ReqFrame.start puts. -/
theorem kept_pos_ok {codes : Codes} {s : ReqShape} (h : reqOk codes s = true) {l : Nat}
    {G : ReqGroup} (hG : (reqGroups s)[l]? = some G) :
    ∀ i (hi : i < G.target.kept.size), 0 < G.target.kept[i].shape.mainRows := by
  unfold reqOk at h
  simp only [Bool.and_eq_true] at h
  exact kept_pos_at h.1 hG

#print axioms kept_pos
#print axioms kept_pos_at
#print axioms kept_pos_ok

end Meaning.K2
