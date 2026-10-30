-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TreesFrame.lean: all oracle messages of the links that are made from a layout
file lie in the class of leaves 0.

The links of a request, with their oracle messages, are made from the arrays that the sub-proofs
declare and from the layout file (Plan.reqFrame, OnBytes/Plan/ReqFrame.lean). Each oracle message is
written at one place, where a group's line is taken in (Plan.takeGroup), with leafClass := 0.

Main names.
  mem_modifyL: a member of a list of which one member was changed.
  TreeSentCap: all oracle messages so far lie in the class 0.
  takeGroup_class: taking a group's line in keeps TreeSentCap.
  optLoop_keeps: a property that each step of a loop in Option keeps.
  reqFrame_class: the links that reqFrame returns have TreeClassCap (TreesSized.lean).

What this file does not claim. That reqFrame returns. Nothing on the layout of the arrays.

The program does not import this file.


-/
import OnBytes.Params.Fit.TreesSized
import OnBytes.Plan.ReqFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes OnBytes.Plan
open OnBytes.Model.Stages (FrameLink)

/-- A member of a list of which one member was changed. -/
theorem mem_modifyL {α : Type} (f : α → α) :
    ∀ (l : List α) (i : Nat) (x : α), x ∈ l.modify i f → x ∈ l ∨ ∃ y ∈ l, x = f y
  | [], _, x, h => by simp at h
  | y :: l, 0, x, h => by
    rw [List.modify_zero_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr ⟨y, List.mem_cons_self, rfl⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
  | y :: l, i + 1, x, h => by
    rw [List.modify_succ_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases mem_modifyL f l i x h with h | ⟨z, hz, rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, rfl⟩

/-- All oracle messages so far lie in the class of leaves 0. -/
def TreeSentCap (sent : Array (Array ReqMessage)) : Prop :=
  ∀ A ∈ sent.toList, ∀ m ∈ A.toList, m.leafClass = 0

/-- One more oracle message of the class 0 in one link. -/
theorem TreeSentCap.push {sent : Array (Array ReqMessage)} (h : TreeSentCap sent) (i : Nat)
    {m : ReqMessage} (hm : m.leafClass = 0) : TreeSentCap (sent.modify i (·.push m)) := by
  intro A hA k hk
  have hA' : A ∈ sent.toList.modify i (·.push m) := by simpa [Array.toList_modify] using hA
  rcases mem_modifyL _ _ _ _ hA' with q | ⟨B, hB, e⟩
  · exact h A q k hk
  · rw [e, Array.toList_push] at hk
    rcases List.mem_append.1 hk with q | q
    · exact h B hB k q
    · rw [List.mem_singleton.1 q]
      exact hm

/-- Taking a group's line in. -/
theorem takeGroup_class {links : Array FrameLink} {answers : Nat} {s s' : GroupsSoFar}
    {g : LayoutGroup} (h : takeGroup links answers s g = some s') (hs : TreeSentCap s.sent) :
    TreeSentCap s'.sent := by
  unfold takeGroup at h
  obtain ⟨l, _, h⟩ := opt_bind h
  replace h := opt_guard h
  extract_lets count lastMoment at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  rw [← Option.some.inj h]
  exact hs.push g.link rfl

/-- A property that each step of a loop in Option keeps. -/
theorem optLoop_keeps {α β : Type} {Pr : β → Prop} (step : β → α → Option β)
    (h : ∀ b a b', step b a = some b' → Pr b → Pr b') :
    ∀ (l : List α) (b b' : β), l.foldlM step b = some b' → Pr b → Pr b'
  | [], b, b', e, hb => by
    rw [List.foldlM_nil] at e
    rw [← Option.some.inj e]
    exact hb
  | a :: l, b, b', e, hb => by
    rw [List.foldlM_cons] at e
    obtain ⟨c, hc, e2⟩ := opt_bind e
    exact optLoop_keeps step h l c b' e2 (h b a c hc hb)

/-- **The links that are made from a layout file lie in the class of leaves 0.** -/
theorem reqFrame_class {links : Array FrameLink} {file : LayoutLines} {answers : Nat}
    {R : List ReqLink} {lay : ReqLayout} (h : reqFrame links file answers = some (R, lay)) :
    TreeClassCap R := by
  unfold reqFrame at h
  obtain ⟨G, hG, h⟩ := opt_bind h
  obtain ⟨B, _, h⟩ := opt_bind h
  replace h := opt_guard h
  have e := Option.some.inj h
  have e1 : G.sent.toList.map (fun m => (⟨0, m.toList⟩ : ReqLink)) = R :=
    congrArg Prod.fst e
  have hS : TreeSentCap G.sent :=
    optLoop_keeps (Pr := fun s : GroupsSoFar => TreeSentCap s.sent) _
      (fun _ _ _ q hq => takeGroup_class q hq) _ _ _ hG (by
        intro A hA m hm
        have hA' : A ∈ links.toList.map fun _ => (#[] : Array ReqMessage) := by
          simpa using hA
        obtain ⟨_, _, e0⟩ := List.mem_map.1 hA'
        rw [← e0] at hm
        exact absurd (show m ∈ [] from hm) List.not_mem_nil)
  intro L hL m hm
  rw [← e1] at hL
  obtain ⟨A, hA, e2⟩ := List.mem_map.1 hL
  rw [← e2] at hm
  exact hS A hA m hm

end OnBytes.Params
