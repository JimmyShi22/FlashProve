-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SampledAtPlan.lean: the kind "the code switch" (K2): AT EVERY
PLACE OF THE KIND's LOT, UNDER THE REQUEST's OWN PUBLIC TEST ON ITS SHAPE (`reqShapeOk`,
OnBytes/Iop/Req.lean), EVERY MESSAGE OF THE SWITCH's SENDING THAT HAS A MAIN ROW IS SAMPLED
(`NoWord`, Honest/K2/Law/Counts.lean). One definition; statements with their proofs.

Why the request's test. The test on a switch's own sizes (`switchTargetCheck`, OnBytes/Iop/Cs.lean)
asks an answer of the carrying message; of a kept copy it asks its member's number of answers, and
not that there is one. The test on the request's shape asks the request's number of answers, at
least 1, of every message of every link; a kept copy bears the shape of such a message.

  `AliveSampled`   every message that is alive is sampled
  `messages_sampled`   under the test: the request has an answer; so has every message of every
                 link. (`answers_of_shape`, Johnson/Goal/Meaning/LaidInside.lean, says the second by
                 the message's number; it is not called, for that file's imports)
  `groupAt_sampled`, `groupsFrom_sampled`, `group_sampled`   a group's target: its carrying message
                 has no main row or is sampled; its kept members are sampled. After the pattern of
                 Johnson/Goal/Meaning/KeptRowsPos.lean, which has the like for "has a main row"
  `noWord_of_mem`   `NoWord` from the sending's members
  `noWord_request`   in the request's own terms: what the switch into group l announces
  `noWord_places`   AT EVERY PLACE OF THE KIND's LOT (`switchPlaces`, Honest/K2/Half.lean)

Limits. It is THE REQUEST's test, not the switch's, and here it is a premise: who pays it wherever
the proof file's description is returned: Honest/K2/Law/SampledOpen.lean. Nothing on the shared
sending's own public test at these places. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)

/-- Every message that is alive is sampled. -/
def AliveSampled (alive : List ReqAlive) : Prop := ∀ a ∈ alive, 1 ≤ a.shape.answers

/-- Under the test on a request's shape: the request has an answer, and so has every message of
every link. -/
theorem messages_sampled {s : ReqShape} (h : reqShapeOk s = true) :
    1 ≤ s.answers ∧ ∀ L ∈ s.link, ∀ m ∈ L.messages, 1 ≤ m.shape.answers := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  have c2 : 1 ≤ s.answers := of_decide_eq_true h.1.1.1.1.1.1.1.2
  refine ⟨c2, fun L hL m hm => ?_⟩
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hL
  have mem : (L, i) ∈ s.link.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hi, e]
  have c3 := List.all_eq_true.1 h.1.1.1.1.1.1.2 (L, i) mem
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at c3
  rw [(c3.2 m hm).1.1.1]
  exact c2

/-- One group: its target's carrying message has no main row or is sampled; its kept members are
sampled; so are the messages that are alive behind it. -/
theorem groupAt_sampled {s : ReqShape} (h1 : 1 ≤ s.answers)
    (hs : ∀ L ∈ s.link, ∀ m ∈ L.messages, 1 ≤ m.shape.answers) (l : Nat) {alive : List ReqAlive}
    (ha : AliveSampled alive) :
    ((reqGroupAt s l alive).1.target.shape.mainRows = 0 ∨
        1 ≤ (reqGroupAt s l alive).1.target.shape.answers) ∧
      (∀ k ∈ (reqGroupAt s l alive).1.target.kept.toList, 1 ≤ k.shape.answers) ∧
      AliveSampled (reqGroupAt s l alive).2 := by
  unfold reqGroupAt
  dsimp only
  refine ⟨?_, fun k hk => ?_, fun a hm => ?_⟩
  · by_cases h0 : (l == 0) = true
    · rw [if_pos h0]
      exact Or.inl rfl
    · rw [if_neg h0]
      exact Or.inr h1
  · obtain ⟨a, h2, rfl⟩ := List.mem_map.1 hk
    exact ha a h2
  · rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨b, h2, rfl⟩ := List.mem_map.1 hm
      exact ha b (List.mem_filter.1 h2).1
    · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hm
      have hmem : x.1 ∈ (s.link[l]?.map (·.messages)).getD [] :=
        List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)
      cases hL : s.link[l]? with
      | none =>
        rw [hL] at hmem
        cases hmem
      | some L =>
        rw [hL] at hmem
        have hm1 := hs L (List.mem_of_getElem? hL) x.1 hmem
        by_cases h0 : (x.1.life == 0) = true
        · rw [if_pos h0] at e
          cases e
        · rw [if_neg h0] at e
          obtain rfl := Option.some.inj e
          exact hm1

theorem groupsFrom_sampled {s : ReqShape} (h1 : 1 ≤ s.answers)
    (hs : ∀ L ∈ s.link, ∀ m ∈ L.messages, 1 ≤ m.shape.answers) :
    ∀ (count l : Nat) (alive : List ReqAlive), AliveSampled alive →
      ∀ G ∈ reqGroupsFrom s count l alive,
        (G.target.shape.mainRows = 0 ∨ 1 ≤ G.target.shape.answers) ∧
          ∀ k ∈ G.target.kept.toList, 1 ≤ k.shape.answers
  | 0, _, _, _, G, hG => by cases hG
  | count + 1, l, alive, ha, G, hG => by
    unfold reqGroupsFrom at hG
    rcases List.mem_cons.1 hG with rfl | hG
    · exact ⟨(groupAt_sampled h1 hs l ha).1, (groupAt_sampled h1 hs l ha).2.1⟩
    · exact groupsFrom_sampled h1 hs count (l + 1) _ (groupAt_sampled h1 hs l ha).2.2 G hG

/-- At group number l, whatever l: beyond the groups stands the empty group. -/
theorem group_sampled {s : ReqShape} (h : reqShapeOk s = true) (l : Nat) :
    (((reqGroups s).getD l {}).target.shape.mainRows = 0 ∨
        1 ≤ ((reqGroups s).getD l {}).target.shape.answers) ∧
      ∀ k ∈ ((reqGroups s).getD l {}).target.kept.toList, 1 ≤ k.shape.answers := by
  rw [Array.getD_eq_getD_getElem?]
  cases hG : (reqGroups s)[l]? with
  | none => exact ⟨Or.inl rfl, fun k hk => by cases hk⟩
  | some G =>
    have hm : G ∈ reqGroupsFrom s (s.link.length + 1) 0 [] := by
      have := Array.mem_toList_iff.2 (Array.mem_of_getElem? hG)
      rwa [reqGroups_eq] at this
    exact groupsFrom_sampled (messages_sampled h).1 (messages_sampled h).2 _ 0 []
      (fun _ hx => by cases hx) G hm

/-- `NoWord`, from the sending's members. -/
theorem noWord_of_mem {sent : Array OracleNotice}
    (h : ∀ n ∈ sent.toList, n.shape.mainRows = 0 ∨ n.shape.answers ≠ 0) : NoWord sent := by
  intro k hk
  refine h _ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
  simp

/-- **In the request's own terms**: what the switch into group l announces: the carrying message,
the kept copies, link l's own messages of moment 0, a fold's fresh mask. F: any fold's shape. -/
theorem noWord_request {s : ReqShape} (h : reqShapeOk s = true) (l : Nat) (F : FoldShape) :
    NoWord (Tw.K2.switchNotices ((reqGroups s).getD l {}).target
      (ReqFrame.notices (({ shape := s, groups := reqGroups s, link := l } : ReqFrame).atMoment 0)
        ++ #[foldMaskNotice F])) := by
  obtain ⟨hT, hK⟩ := group_sampled h l
  refine noWord_of_mem fun n hn => ?_
  unfold Tw.K2.switchNotices at hn
  simp only [Array.toList_append, List.mem_append, Array.toList_map, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with (rfl | ⟨k, hk, rfl⟩) | hn | rfl
  · rcases hT with e | e
    · exact Or.inl e
    · exact Or.inr (Nat.ne_of_gt e)
  · exact Or.inr (Nat.ne_of_gt (hK k hk))
  · unfold ReqFrame.notices at hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    have hm' := (List.mem_filter.1 hm).1
    cases hL : s.link[l]? with
    | none =>
      have e : (((s.link[l]?).map (·.messages)).getD []) = [] := by rw [hL]; rfl
      exact absurd (e ▸ hm') (List.not_mem_nil)
    | some L =>
      have e : (((s.link[l]?).map (·.messages)).getD []) = L.messages := by rw [hL]; rfl
      exact Or.inr (Nat.ne_of_gt
        ((messages_sampled h).2 L (List.mem_of_getElem? hL) m (e ▸ hm')))
  · exact Or.inl rfl

/-- **At every place of the kind's lot.** hok: the request's own public test on its shape, at the
planner's sizes that the lot reads. -/
theorem noWord_places {Z : Pub} {G : Ground}
    (hok : ∀ P, P1K2.prepOf Z G = some P → reqShapeOk P.z.request = true) :
    ∀ p ∈ switchPlaces Z G, NoWord (switchSent p.sizes p.others) := by
  intro p hp
  unfold switchPlaces at hp
  cases hP : P1K2.prepOf Z G with
  | none =>
    rw [hP] at hp
    cases hp
  | some P =>
    cases hS : spotsOf Z.cuts with
    | none =>
      rw [hP, hS] at hp
      cases hp
    | some sps =>
      rw [hP, hS] at hp
      obtain ⟨sp, _, rfl⟩ := List.mem_map.1 hp
      exact noWord_request (hok P hP) _ _

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.messages_sampled
#print axioms ProofFile.Honest.K2.groupAt_sampled
#print axioms ProofFile.Honest.K2.groupsFrom_sampled
#print axioms ProofFile.Honest.K2.group_sampled
#print axioms ProofFile.Honest.K2.noWord_of_mem
#print axioms ProofFile.Honest.K2.noWord_request
#print axioms ProofFile.Honest.K2.noWord_places
