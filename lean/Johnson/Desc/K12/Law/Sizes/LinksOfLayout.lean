-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/LinksOfLayout.lean: the links of a request that Plan.reqFrame returns are
a function of the number of declared links, the number of answers and the layout file's group lines
alone.

Plan.reqFrame (OnBytes/Plan/ReqFrame.lean) makes a request's links, each with its oracle messages,
from the arrays that the sub-proofs declare and the lines of a layout file. It reads the declared
arrays in its tests and for the layout of the arrays. The oracle messages themselves are made of the
group lines: each line adds one message to its link. Here that is proved, from a run that returns.
Main names:
  `messageOf`, `pushGroup`, `linksOfGroups`: the message of a group's line; one line taken in,
    without the tests; the links of a list of lines.
  `takeGroup_sent`, `groups_sent`: one step and the whole loop of reqFrame's first fold.
  `reqFrame_links`: THE STATEMENT. `linksOfGroups_length`: as many links as were declared.
  `shapesWith_count`: the test of Model.Verify.shapesWith on the number of links.
Limits: one direction: from a reqFrame that returns. Nothing on the layout of the arrays. Nothing on
soundness. Nothing on hiding.
-/
import OnBytes.Plan.ReqFrame
import OnBytes.Params.ConfigureLaws
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Plan OnBytes.Params
open OnBytes.Model.Stages (FrameLink)

/-- The oracle message that a group's line makes. count: the messages that its link has so far. -/
def messageOf (answers count : Nat) (g : LayoutGroup) : ReqMessage :=
  { shape :=
      { code := 0, mainRows := g.rows, mainDeg := if g.cls == 87 then 3 else 1,
        maskRows := if count == 0 then 1 else 0, maskCode := 0, answers := answers }
    leafClass := 0
    moment := g.moment
    life := g.life }

/-- One group's line taken in, without the tests. -/
def pushGroup (answers : Nat) (sent : Array (Array ReqMessage)) (g : LayoutGroup) :
    Array (Array ReqMessage) :=
  sent.modify g.link (·.push (messageOf answers (sent.getD g.link #[]).size g))

/-- The links of n declared links and a list of group lines. -/
def linksOfGroups (n answers : Nat) (gs : List LayoutGroup) : List ReqLink :=
  (gs.foldl (pushGroup answers) (Array.replicate n #[])).toList.map fun m => ⟨0, m.toList⟩

/-- One step of reqFrame's first fold, where it returns. -/
theorem takeGroup_sent {links : Array FrameLink} {answers : Nat} {s s' : GroupsSoFar}
    {g : LayoutGroup} (h : takeGroup links answers s g = some s') :
    s'.sent = pushGroup answers s.sent g := by
  unfold takeGroup at h
  obtain ⟨l, _, h⟩ := opt_bind h
  replace h := opt_guard h
  extract_lets count lastMoment at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  rw [← Option.some.inj h]
  rfl

/-- The whole fold. -/
theorem groups_sent {links : Array FrameLink} {answers : Nat} :
    ∀ (gs : List LayoutGroup) (s s' : GroupsSoFar),
      gs.foldlM (takeGroup links answers) s = some s' →
        s'.sent = gs.foldl (pushGroup answers) s.sent
  | [], s, s', e => by
    rw [List.foldlM_nil] at e
    rw [← Option.some.inj e]
    rfl
  | g :: gs, s, s', e => by
    rw [List.foldlM_cons] at e
    obtain ⟨c, hc, e2⟩ := opt_bind e
    rw [groups_sent gs c s' e2, takeGroup_sent hc]
    rfl

/-- **The links that reqFrame returns are those of the group lines.** -/
theorem reqFrame_links {links : Array FrameLink} {file : LayoutLines} {answers : Nat}
    {rl : List ReqLink} {lay : ReqLayout} (h : reqFrame links file answers = some (rl, lay)) :
    rl = linksOfGroups links.size answers file.groups := by
  unfold reqFrame at h
  obtain ⟨G, hG, h⟩ := opt_bind h
  obtain ⟨B, _, h⟩ := opt_bind h
  replace h := opt_guard h
  have e := (Prod.mk.inj (Option.some.inj h)).1
  rw [← e, groups_sent _ _ _ hG]
  unfold linksOfGroups
  have e0 : (links.map fun _ => (#[] : Array ReqMessage)) = Array.replicate links.size #[] := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  rw [e0]

/-- Taking a line in keeps the number of links. -/
theorem pushGroups_size (answers : Nat) :
    ∀ (gs : List LayoutGroup) (a : Array (Array ReqMessage)),
      (gs.foldl (pushGroup answers) a).size = a.size
  | [], _ => rfl
  | g :: gs, a => by
    rw [List.foldl_cons, pushGroups_size answers gs]
    simp [pushGroup]

/-- There are as many links as were declared. -/
theorem linksOfGroups_length (n answers : Nat) (gs : List LayoutGroup) :
    (linksOfGroups n answers gs).length = n := by
  unfold linksOfGroups
  rw [List.length_map, Array.length_toList, pushGroups_size]
  simp

/-- A step that refuses under a condition has returned: the condition failed. -/
theorem exc_guard_not {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    {b : β}
    (h : (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) = .ok b) :
    ¬ c ∧ next PUnit.unit = .ok b := by
  split at h
  · cases h
  · exact ⟨‹_›, h⟩

/-- The test of shapesWith on the number of links, and the sub-proofs' record. -/
theorem shapesWith_count {X : Model.Verify.Public} {links : List ReqLink} {layout : ReqLayout}
    {ids : List Nat} {s : Shapes} (h : Model.Verify.shapesWith X links layout ids = .ok s) :
    links.length = (if X.p4 then 2 else 1) * X.NGr + 1 ∧
      s.sub = Model.Verify.subproofsWith X links := by
  unfold Model.Verify.shapesWith at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨hn, h⟩ := exc_guard_not h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  exact ⟨by simpa using hn, rfl⟩

end H2K.Sizes

#print axioms H2K.Sizes.reqFrame_links
#print axioms H2K.Sizes.linksOfGroups_length
#print axioms H2K.Sizes.shapesWith_count
