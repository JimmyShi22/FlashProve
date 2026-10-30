-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TargetPlan.lean: FOUR CLAUSES OF `FrontCore` (Returns/SentFront.lean)
THAT READ THE SWITCH's TARGET ALONE, FOR EVERY LAWFUL SHAPE OF A REQUEST, AT EVERY GROUP BUT THE
FIRST: restMain · keptAnswers · groupCode · copiesCode. No state, no plan's numbers, no written
value, no size: the program's text that makes a request's groups (`reqGroups`, OnBytes/Iop/Req.lean)
and its test on the shape (`reqShapeOk`). Statements with their proofs: one recursion, unfoldings.

  `AliveFit s alive` every message that is alive has a main row, the shape's main code and the
                    shape's number of answers
  `messages_ok`, `answers_pos` what `reqShapeOk` says of a segment's message; the shape counts at
                    least one answer
  `groupAt_fit`, `groupsFrom_fit` one group; the groups from number l on, by their place in the
                    list. THE LIBRARY's `groupAt_pos`, `groupsFrom_pos`
                    (Johnson/Goal/Meaning/KeptRowsPos.lean) carry "has a main row" alone, by
                    membership; their lines stand here again with two clauses more and the group's
                    number
  `target_fit` THE TOP: `reqShapeOk s = true` · `(reqGroups s)[l]? = some G` ⊢ the rest lies in main
                    rows · if l ≠ 0 the target's main code is the shape's · each kept copy has the
                    shape's main code and counts an answer
  `front_target_fit` so, at any front whose target is such a group's and any code equal to the
                    shape's: the four clauses, each in `FrontCore`'s own letters

By, all the library's: `reqGroups_eq` (OnBytes/Iop/Req.lean) · `links_ok`, `life_pos`
(Johnson/Goal/Meaning/KeptRowsPos.lean). Near relatives, not called: `shapeOk_atStart`
(Johnson/Desc/K1/Law/FirstMakeFacts.lean): its first clause is `answers_pos` · `kept_pos`
(Johnson/Goal/Meaning/KeptRowsPos.lean): `FrontCore.keptPos` by the like road · this folder's
`PublicFits` (Returns/PinPublic.lean): restMain and keptAnswers at the 25 written fronts, by Lean's
kernel, and from there under three tests on the public part: here no test is asked.

Limits. The first group (l = 0) has the blank target: nothing is said of its main code. Nothing on
the target's cuts, bits or classes of leaves. That a front's target is a group's, and that the
frame's shape is lawful, are premises here: at a reached state Returns/LinkReached.lean and
Returns/ArmsPlan.lean show how they are had. Nothing on any property.


-/
import Johnson.Goal.Meaning.KeptRowsPos
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)
open Meaning.K2 (links_ok life_pos)
open _root_.Tw.K2 (Front)

/-- Every message that is alive has a main row, the shape's main code and its number of answers. -/
def AliveFit (s : ReqShape) (alive : List ReqAlive) : Prop :=
  ∀ a ∈ alive, 0 < a.shape.mainRows ∧ a.shape.code = s.code ∧ a.shape.answers = s.answers

/-- What the test on the shape says of a segment's message. -/
theorem messages_ok {s : ReqShape} (h : reqShapeOk s = true) :
    ∀ L ∈ s.link, ∀ m ∈ L.messages, m.shape.answers = s.answers ∧
      (m.shape.mainRows = 0 ∨ m.shape.code = s.code) := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  have a := h.1.1.1.1.1.1.2
  intro L hL m hm
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hL
  have hz : (L, i) ∈ s.link.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hi, e]
  have b := (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 a (L, i) hz).2
  have c := List.all_eq_true.1 b m hm
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at c
  exact ⟨c.1.1.1, c.1.1.2⟩

theorem answers_pos {s : ReqShape} (h : reqShapeOk s = true) : s.answers ≠ 0 := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have a := h.1.1.1.1.1.1.1.2
  omega

theorem groupAt_fit {s : ReqShape} (hs : reqShapeOk s = true) (l : Nat)
    {alive : List ReqAlive} (ha : AliveFit s alive) :
    (reqGroupAt s l alive).1.target.rest.part = .main ∧
      (l ≠ 0 → (reqGroupAt s l alive).1.target.shape.code = s.code) ∧
      (∀ k ∈ (reqGroupAt s l alive).1.target.kept.toList,
        k.shape.code = s.code ∧ k.shape.answers = s.answers) ∧
      AliveFit s (reqGroupAt s l alive).2 := by
  unfold reqGroupAt
  dsimp only
  refine ⟨rfl, fun hl => ?_, fun k hk => ?_, fun a hm => ?_⟩
  · rw [if_neg (by simpa using hl)]
  · obtain ⟨a, h1, rfl⟩ := List.mem_map.1 hk
    exact (ha a h1).2
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
        have hLm := List.mem_of_getElem? hL
        have hok := links_ok hs L hLm
        unfold reqLinkOk at hok
        simp only [Bool.and_eq_true] at hok
        have hm1 := List.all_eq_true.1 hok.2 x.1 hmem
        obtain ⟨q1, q2⟩ := messages_ok hs L hLm x.1 hmem
        by_cases h0 : (x.1.life == 0) = true
        · rw [if_pos h0] at e
          cases e
        · rw [if_neg h0] at e
          obtain rfl := Option.some.inj e
          have hp := life_pos hm1 (by simpa using h0)
          exact ⟨hp, q2.resolve_left (by omega), q1⟩

theorem groupsFrom_fit {s : ReqShape} (hs : reqShapeOk s = true) :
    ∀ (count l : Nat) (alive : List ReqAlive), AliveFit s alive →
      ∀ (i : Nat) (G : ReqGroup), (reqGroupsFrom s count l alive)[i]? = some G →
        G.target.rest.part = .main ∧ (l + i ≠ 0 → G.target.shape.code = s.code) ∧
          ∀ k ∈ G.target.kept.toList, k.shape.code = s.code ∧ k.shape.answers = s.answers
  | 0, _, _, _, i, G, hG => by
    unfold reqGroupsFrom at hG
    cases hG
  | count + 1, l, alive, ha, i, G, hG => by
    unfold reqGroupsFrom at hG
    obtain ⟨g1, g2, g3, g4⟩ := groupAt_fit hs l ha
    cases i with
    | zero =>
      obtain rfl : (reqGroupAt s l alive).1 = G := Option.some.inj hG
      exact ⟨g1, g2, g3⟩
    | succ j =>
      have hG' : (reqGroupsFrom s count (l + 1) (reqGroupAt s l alive).2)[j]? = some G := hG
      obtain ⟨r1, r2, r3⟩ := groupsFrom_fit hs count (l + 1) _ g4 j G hG'
      exact ⟨r1, fun _ => r2 (by omega), r3⟩

/-- **At every group of a lawful shape.** -/
theorem target_fit {s : ReqShape} (h : reqShapeOk s = true) {l : Nat} {G : ReqGroup}
    (hG : (reqGroups s)[l]? = some G) :
    G.target.rest.part = .main ∧ (l ≠ 0 → G.target.shape.code = s.code) ∧
      ∀ k ∈ G.target.kept.toList, k.shape.code = s.code ∧ k.shape.answers ≠ 0 := by
  rw [reqGroups_eq] at hG
  have hG' : (reqGroupsFrom s (s.link.length + 1) 0 [])[l]? = some G := by simpa using hG
  obtain ⟨r1, r2, r3⟩ := groupsFrom_fit h _ 0 [] (fun _ hm => by cases hm) l G hG'
  refine ⟨r1, fun hl => r2 (by omega), fun k hk => ⟨(r3 k hk).1, ?_⟩⟩
  rw [(r3 k hk).2]
  exact answers_pos h

/-- **The four clauses of `FrontCore`, at a front whose target is such a group's.** -/
theorem front_target_fit {s : ReqShape} (h : reqShapeOk s = true) {l : Nat} {G : ReqGroup}
    (hG : (reqGroups s)[l]? = some G) (hl : l ≠ 0) {x : Front} (hT : x.T = G.target) {code : Nat}
    (hc : code = s.code) :
    x.T.rest.part = .main ∧ (∀ k ∈ x.T.kept.toList, k.shape.answers ≠ 0) ∧
      x.T.shape.code = code ∧ ∀ k ∈ x.T.kept.toList, k.shape.code = code := by
  obtain ⟨r1, r2, r3⟩ := target_fit h hG
  rw [hT, hc]
  exact ⟨r1, fun k hk => (r3 k hk).2, r2 hl, fun k hk => (r3 k hk).1⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.messages_ok
#print axioms VerifiableInference.Desc.K2.Honest.Returns.answers_pos
#print axioms VerifiableInference.Desc.K2.Honest.Returns.groupAt_fit
#print axioms VerifiableInference.Desc.K2.Honest.Returns.groupsFrom_fit
#print axioms VerifiableInference.Desc.K2.Honest.Returns.target_fit
#print axioms VerifiableInference.Desc.K2.Honest.Returns.front_target_fit
