-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TreesReq.lean: parts for the bound: a list of notices that all have the class of
leaves 0 and, where they have main rows, one code, followed by notices of one class without main
rows, has at most two trees. The lists that the frame of a chain of links sends are of this form.

The frame of a chain of links (reqPlanFrom, reqMoments, OnBytes/Params/DeriveReq.lean) sends, in one
prover's message: the carrying message of the switch into the group, the kept messages, the link's
own messages of one moment, the fresh mask of the group's fold, and at the first link what rides at
the start. How many these are hangs on the layout file. Their classes of leaves and codes do not.

Main names.
  TreeNoticeCap c n: the notice n has the class of leaves 0 and, if it has main rows, the code c.
  TreeLinkCap c L, TreeGroupCap c g: so for a link's messages; for a group's carrying and kept
    messages.
  TreeRiderCap l: the notices of l have one class of leaves and no main rows.
  TreesCap codes sent: the number of trees of the message sent, where there is one, is at most 2.
  treesCap_notices: notices with TreeNoticeCap, followed by riders with TreeRiderCap, have TreesCap.
  treeNoticeCap_mask: the fresh mask of a fold, as the frame announces it.
  groups_all: what holds of every link's messages, of the carrying message and of the empty shape
    holds of every group's carrying and kept messages: for a property P of notices as a letter.
  treeGroupCap_groups: so all groups of a shape whose links have TreeLinkCap have TreeGroupCap.
  treesCap_moment: the message of a later moment, as reqMoments writes it.
  treeNoticeCap_members: the members of a group's first message, as reqPlanFrom writes them.

What this file does not claim. That the planner's own shapes have TreeLinkCap and TreeRiderCap. That
reqPlanFrom and reqMoments send these lists: treesCap_moment and treeNoticeCap_members are stated at
the lists as written there; whoever unfolds the routines joins them.

The program does not import this file.


-/
import OnBytes.Params.Fit.TreesSites
import OnBytes.Params.DeriveReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes

/-- The class of leaves 0 and, where there are main rows, the code c. -/
def TreeNoticeCap (c : Nat) (n : OracleNotice) : Prop :=
  n.leafClass = 0 ∧ (n.shape.mainRows ≠ 0 → n.shape.code = c)

/-- So for all oracle messages of a link. -/
def TreeLinkCap (c : Nat) (L : ReqLink) : Prop :=
  ∀ m ∈ L.messages, TreeNoticeCap c ⟨m.shape, m.leafClass⟩

/-- So for the carrying message and the kept messages of a group. -/
def TreeGroupCap (c : Nat) (g : ReqGroup) : Prop :=
  TreeNoticeCap c ⟨g.target.shape, g.target.leafClass⟩ ∧
    ∀ k ∈ keptOf g, TreeNoticeCap c ⟨k.shape, k.leafClass⟩

/-- One class of leaves, and no main rows. -/
def TreeRiderCap (l : List OracleNotice) : Prop :=
  ∃ c, ∀ n ∈ l, n.leafClass = c ∧ n.shape.mainRows = 0

/-- The number of trees of a prover's message, where there is one, is at most 2. -/
def TreesCap (codes : Codes) (sent : List OracleNotice) : Prop :=
  ∀ r, treesOf codes sent.toArray = some r → r ≤ 2

/-- No rider. -/
theorem treeRiderCap_nil : TreeRiderCap [] := ⟨0, fun _ h => absurd h List.not_mem_nil⟩

/-- Notices of the links' class and code, followed by riders. -/
theorem treesCap_notices (codes : Codes) {c : Nat} {sent riders : List OracleNotice}
    (h1 : ∀ n ∈ sent, TreeNoticeCap c n) (h2 : TreeRiderCap riders) :
    TreesCap codes (sent ++ riders) := by
  obtain ⟨b, hb⟩ := h2
  intro r h
  refine treesOf_two_mem (a := 0) (b := b) (L := (codes.base.getD c default).logN) h
    (fun n hn => ?_) fun n hn hm => ?_
  · rcases List.mem_append.1 (show n ∈ sent ++ riders from hn) with q | q
    · exact Or.inl (h1 n q).1
    · exact Or.inr (hb n q).1
  · rcases List.mem_append.1 (show n ∈ sent ++ riders from hn) with q | q
    · rw [(h1 n q).2 hm]
    · exact absurd (hb n q).2 hm

/-- The fresh mask of a fold, as the frame announces it. -/
theorem treeNoticeCap_mask (c : Nat) (s : IoppStage) :
    TreeNoticeCap c (foldMaskNotice (ioppFoldShape s {})) :=
  ⟨rfl, fun q => absurd rfl q⟩

/-- The carrying message of the switch into the group number l. -/
theorem reqGroupAt_shape (s : ReqShape) (l : Nat) (alive : List ReqAlive) :
    (reqGroupAt s l alive).1.target.shape =
      if l == 0 then {}
      else { code := s.code, mainRows := 2, mainDeg := 3, answers := s.answers } := rfl

/-- Its class of leaves. -/
theorem reqGroupAt_class (s : ReqShape) (l : Nat) (alive : List ReqAlive) :
    (reqGroupAt s l alive).1.target.leafClass = 0 := rfl

/-- The kept messages of that switch. -/
theorem reqGroupAt_kept (s : ReqShape) (l : Nat) (alive : List ReqAlive) :
    keptOf (reqGroupAt s l alive).1 = alive.map fun a =>
      ({ shape := a.shape, leafClass := a.leafClass,
         keptAgain := decide (1 < a.left) } : KeptTarget) := rfl

/-- The messages that are alive after the group. -/
theorem reqGroupAt_alive (s : ReqShape) (l : Nat) (alive : List ReqAlive) :
    (reqGroupAt s l alive).2 =
      ((alive.filter fun a => decide (1 < a.left)).map fun a => { a with left := a.left - 1 }) ++
        ((s.link[l]?.map (·.messages)).getD []).zipIdx.filterMap fun x =>
          if x.1.life == 0 then none
          else some ({ shape := x.1.shape, leafClass := x.1.leafClass, left := x.1.life,
                       born := (l, x.2) } : ReqAlive) := rfl

section Groups

variable {s : ReqShape} (P : OracleNotice → Prop)

/-- One group, and the messages that are alive after it, for a property P of notices. -/
theorem group_at (hm : ∀ L ∈ s.link, ∀ m ∈ L.messages, P ⟨m.shape, m.leafClass⟩)
    (hc : P ⟨{ code := s.code, mainRows := 2, mainDeg := 3, answers := s.answers }, 0⟩)
    (h0 : P ⟨{}, 0⟩) (l : Nat) {alive : List ReqAlive}
    (ha : ∀ a ∈ alive, P ⟨a.shape, a.leafClass⟩) :
    (P ⟨(reqGroupAt s l alive).1.target.shape, (reqGroupAt s l alive).1.target.leafClass⟩ ∧
      ∀ k ∈ keptOf (reqGroupAt s l alive).1, P ⟨k.shape, k.leafClass⟩) ∧
      ∀ a ∈ (reqGroupAt s l alive).2, P ⟨a.shape, a.leafClass⟩ := by
  refine ⟨⟨?_, fun k hk => ?_⟩, fun a h => ?_⟩
  · rw [reqGroupAt_shape, reqGroupAt_class]
    split
    · exact h0
    · exact hc
  · rw [reqGroupAt_kept] at hk
    obtain ⟨a, haa, e⟩ := List.mem_map.1 hk
    rw [← e]
    exact ha a haa
  · rw [reqGroupAt_alive] at h
    rcases List.mem_append.1 h with q | q
    · obtain ⟨a', ha', e⟩ := List.mem_map.1 q
      rw [← e]
      exact ha a' (List.mem_filter.1 ha').1
    · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 q
      split at e
      · cases e
      · rw [← Option.some.inj e]
        have hx1 : x.1 ∈ (s.link[l]?.map (·.messages)).getD [] :=
          List.fst_mem_of_mem_zipIdx hx
        cases hl : s.link[l]? with
        | none =>
          rw [hl] at hx1
          exact absurd hx1 List.not_mem_nil
        | some L =>
          rw [hl] at hx1
          exact hm L (List.mem_of_getElem? hl) x.1 hx1

/-- The groups from number l on. -/
theorem groups_from (hm : ∀ L ∈ s.link, ∀ m ∈ L.messages, P ⟨m.shape, m.leafClass⟩)
    (hc : P ⟨{ code := s.code, mainRows := 2, mainDeg := 3, answers := s.answers }, 0⟩)
    (h0 : P ⟨{}, 0⟩) :
    ∀ (count l : Nat) (alive : List ReqAlive), (∀ a ∈ alive, P ⟨a.shape, a.leafClass⟩) →
      ∀ g ∈ reqGroupsFrom s count l alive,
        P ⟨g.target.shape, g.target.leafClass⟩ ∧
          ∀ k ∈ keptOf g, P ⟨k.shape, k.leafClass⟩
  | 0, _, _, _, g, hg => by
    unfold reqGroupsFrom at hg
    exact absurd hg List.not_mem_nil
  | count + 1, l, alive, ha, g, hg => by
    unfold reqGroupsFrom at hg
    rcases List.mem_cons.1 hg with e | q
    · rw [e]
      exact (group_at P hm hc h0 l ha).1
    · exact groups_from hm hc h0 count (l + 1) _ (group_at P hm hc h0 l ha).2 g q

/-- **What holds of every link's oracle messages, of the carrying message and of the empty shape
holds of every group's carrying message and kept messages.** -/
theorem groups_all (hm : ∀ L ∈ s.link, ∀ m ∈ L.messages, P ⟨m.shape, m.leafClass⟩)
    (hc : P ⟨{ code := s.code, mainRows := 2, mainDeg := 3, answers := s.answers }, 0⟩)
    (h0 : P ⟨{}, 0⟩) :
    ∀ g ∈ (reqGroups s).toList,
      P ⟨g.target.shape, g.target.leafClass⟩ ∧
        ∀ k ∈ keptOf g, P ⟨k.shape, k.leafClass⟩ := by
  rw [reqGroups_eq]
  exact groups_from P hm hc h0 _ 0 [] fun _ h => absurd h List.not_mem_nil

end Groups

/-- All groups of a shape whose links have the one class and code. -/
theorem treeGroupCap_groups {s : ReqShape} (hs : ∀ L ∈ s.link, TreeLinkCap s.code L) :
    ∀ g ∈ (reqGroups s).toList, TreeGroupCap s.code g :=
  groups_all (TreeNoticeCap s.code) hs ⟨rfl, fun _ => rfl⟩ ⟨rfl, fun q => absurd rfl q⟩

/-- The message of a later moment of a link, as reqMoments writes it. -/
theorem treesCap_moment (codes : Codes) {c : Nat} {msgs : List ReqMessage}
    (hm : ∀ m ∈ msgs, TreeNoticeCap c ⟨m.shape, m.leafClass⟩) (moment : Nat) :
    TreesCap codes ((msgs.filter fun m => m.moment == moment).map
      fun m => ⟨m.shape, m.leafClass⟩) := by
  have q := treesCap_notices codes (c := c) (riders := [])
    (sent := (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩)
    (fun n hn => by
      obtain ⟨m, hmm, e⟩ := List.mem_map.1 hn
      rw [← e]
      exact hm m (List.mem_filter.1 hmm).1) treeRiderCap_nil
  rwa [List.append_nil] at q

/-- The members of a group's first message, as reqPlanFrom writes them. -/
theorem treeNoticeCap_members {c : Nat} {g : ReqGroup} (hg : TreeGroupCap c g)
    {msgs : List ReqMessage}
    (hm : ∀ m ∈ msgs, TreeNoticeCap c ⟨m.shape, m.leafClass⟩) (l : Nat) (t : IoppStage) :
    ∀ n ∈ (if 0 < l then [(⟨g.target.shape, g.target.leafClass⟩ : OracleNotice)] else []) ++
      (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
      (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
      [foldMaskNotice (ioppFoldShape t {})], TreeNoticeCap c n := by
  intro n hn
  rcases List.mem_append.1 hn with hn | hn
  · rcases List.mem_append.1 hn with hn | hn
    · rcases List.mem_append.1 hn with hn | hn
      · split at hn
        · rw [List.mem_singleton.1 hn]
          exact hg.1
        · exact absurd hn List.not_mem_nil
      · obtain ⟨k, hk, e⟩ := List.mem_map.1 hn
        rw [← e]
        exact hg.2 k hk
    · obtain ⟨m, hmm, e⟩ := List.mem_map.1 hn
      rw [← e]
      exact hm m (List.mem_filter.1 hmm).1
  · rw [List.mem_singleton.1 hn]
    exact treeNoticeCap_mask c t

end OnBytes.Params
