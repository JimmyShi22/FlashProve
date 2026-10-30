-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05KeptSame.lean: AT EVERY REQUEST's SHAPE AND EVERY LINK a kept oracle
message has the shape of the message whose rows it took: the field keptSame of AttReadsOK
(Johnson/Desc/First/Look/K3CallerAtt.lean) and of SymsOK (Johnson/Desc/First/Att/K05AddrTieOf.lean)
is a law of the programs' plain function reqGroupAt (OnBytes/Iop/Req.lean): no test is needed.

How. reqGroupAt carries a list "alive" of the messages that later links still read, each with its
shape and with "born": the link and the number under which it was first sent. It makes a group's
kept targets and its list "born" out of that one list. That every member of "alive" has the shape of
the message at its "born" holds of the empty list and is kept by every step.

Main names:
  `AliveOk s alive`: every member of alive has the shape of the shape's message at its "born".
  `aliveOk_step`: reqGroupAt keeps it.
  `KeptGroupOk s g`: number by number, the group's kept target has the shape of the message at the
    group's "born".
  `groupAt_ok`, `groupsFrom_ok`, `groups_ok`.
  `kept_same`: **the field keptSame, for every D and i.**
General in the sort of link, though the file stands among the files of kind K5.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First.Look (Sent keptAt bornAt messagesAt)

/-- The shape of the message that the shape s has at (link, number). -/
def shapeAtBorn (s : ReqShape) (b : ℕ × ℕ) : Option OracleShape :=
  ((((s.link[b.1]?).map (·.messages)).getD [])[b.2]?).map (·.shape)

/-- Every member of alive has the shape of the message at its "born". -/
def AliveOk (s : ReqShape) (alive : List ReqAlive) : Prop :=
  ∀ a ∈ alive, shapeAtBorn s a.born = some a.shape

/-- reqGroupAt keeps it. -/
theorem aliveOk_step (s : ReqShape) (l : ℕ) (alive : List ReqAlive) (h : AliveOk s alive) :
    AliveOk s (reqGroupAt s l alive).2 := by
  intro a ha
  simp only [reqGroupAt, List.mem_append, List.mem_map, List.mem_filter, List.mem_filterMap] at ha
  rcases ha with ⟨a', ⟨ha', _⟩, rfl⟩ | ⟨x, hx, hs⟩
  · exact h a' ha'
  · by_cases h0 : (x.1.life == 0) = true
    · rw [if_pos h0] at hs
      cases hs
    · rw [if_neg h0] at hs
      obtain rfl := Option.some.inj hs
      have hg := List.mem_zipIdx_iff_getElem?.1 (show (x.1, x.2) ∈ _ from hx)
      show ((((s.link[l]?).map (·.messages)).getD [])[x.2]?).map (·.shape) = some x.1.shape
      rw [hg]
      rfl

/-- Number by number, the kept target has the shape of the message at "born". -/
def KeptGroupOk (s : ReqShape) (g : ReqGroup) : Prop :=
  ∀ (k : ℕ) (t : KeptTarget), g.target.kept[k]? = some t →
    shapeAtBorn s (g.born.getD k (0, 0)) = some t.shape

theorem groupAt_ok (s : ReqShape) (l : ℕ) (alive : List ReqAlive) (h : AliveOk s alive) :
    KeptGroupOk s (reqGroupAt s l alive).1 := by
  intro k t ht
  simp only [reqGroupAt, List.getElem?_toArray, List.getElem?_map] at ht
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ht
  have hb : (reqGroupAt s l alive).1.born.getD k (0, 0) = a.born := by
    simp only [reqGroupAt]
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, ha]
    rfl
  rw [hb]
  exact h a (List.mem_of_getElem? ha)

theorem groupsFrom_ok (s : ReqShape) : ∀ (count l : ℕ) (alive : List ReqAlive), AliveOk s alive →
    ∀ g ∈ reqGroupsFrom s count l alive, KeptGroupOk s g
  | 0, _, _, _, g, hg => by cases hg
  | count + 1, l, alive, h, g, hg => by
    simp only [reqGroupsFrom, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact groupAt_ok s l alive h
    · exact groupsFrom_ok s count (l + 1) _ (aliveOk_step s l alive h) g hg

theorem groups_ok (s : ReqShape) (i : ℕ) (g : ReqGroup) (h : (reqGroups s)[i]? = some g) :
    KeptGroupOk s g := by
  rw [reqGroups_eq] at h
  have hm : g ∈ (reqGroupsFrom s (s.link.length + 1) 0 []).toArray := Array.mem_of_getElem? h
  have h0 : AliveOk s [] := fun a ha => absurd ha List.not_mem_nil
  exact groupsFrom_ok s _ _ [] h0 g (by simpa using hm)

/-- **A kept message has the shape of the message whose rows it took: at every shape and link.** -/
theorem kept_same (D : Sent) (i : ℕ) (k : ℕ) (hk : k < (keptAt D i).length) :
    (((messagesAt D ((bornAt D i).getD k (0, 0)).1)[((bornAt D i).getD k (0, 0)).2]?).map
      (·.shape)) = some ((keptAt D i).get ⟨k, hk⟩).shape := by
  have hget : (keptAt D i)[k]? = some ((keptAt D i).get ⟨k, hk⟩) := List.getElem?_eq_getElem hk
  generalize (keptAt D i).get ⟨k, hk⟩ = t at hget ⊢
  unfold keptAt at hget
  unfold bornAt
  cases h : (reqGroups D.shape)[i]? with
  | none =>
    rw [h] at hget
    simp at hget
  | some g =>
    rw [h] at hget
    have h2 : g.target.kept[k]? = some t := by
      have : (Params.keptOf g)[k]? = some t := hget
      unfold Params.keptOf at this
      rw [Array.getElem?_toList] at this
      exact this
    exact groups_ok D.shape i g h k t h2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.aliveOk_step
#print axioms VerifiableInference.Desc.First.Att.P.groupAt_ok
#print axioms VerifiableInference.Desc.First.Att.P.kept_same
