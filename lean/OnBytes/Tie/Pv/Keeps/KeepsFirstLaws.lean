-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsFirstLaws.lean: what the first call of a link of a request's chain keeps
of the state with which it is called. Statements and proofs, beside
OnBytes/Tie/Pv/Keeps/KeepsFirst.lean.

What it is for. `FirstParts` has the frame g behind `ReqFrame.beginLink` as a letter. Every use
needs to know what g has of the frame f before it: the number of the link, so that "the first link"
means one thing in all clauses; and above all g.rows = f.rows: the code switch starts from what the
closing of the link before has returned.

Main names:
  `beginLink_same`: a success of `beginLink` turns the group, the moment and the list of the link's
    own oracle messages alone; the group is the one that `Blk.newGroup` has returned.
  `FirstParts.begin_same`: the same for the g of `FirstParts`; `FirstParts.link_eq`,
    `FirstParts.rows_eq`.
  `FirstParts.switch_rows`: at a later link the code switch is called on f.rows.
  `FirstParts.send_zero`: at the first link a sending is called.
  `check_first_test`: `ChainCheck.first` succeeds only where no link is under way and the number of
    the link is below the number of links.
Limits: one direction: from the calls' success.
-/
import OnBytes.Tie.Pv.Keeps.KeepsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5

open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- beginLink turns the group, the moment and the link's own list alone. -/
theorem beginLink_same (f : ReqFrame) {c : Ctx} {g : ReqFrame} {c' : Ctx}
    (h : f.beginLink c = .ok (g, c')) :
    ∃ n, Blk.newGroup f.shape.code f.shape.maskCode c = .ok (n, c') ∧
      g = { f with group := n, moment := 1, own := #[] } := by
  have hr : Runs f.beginLink c g c' := h
  unfold ReqFrame.beginLink at hr
  obtain ⟨n, c1, h1, h2⟩ := HasRuns.runs_bind hr
  obtain ⟨e1, e2⟩ := runs_pure' h2
  subst e2
  exact ⟨n, h1, e1⟩

variable {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
  {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
  {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}

theorem FirstParts.begin_same
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) :
    ∃ n, Blk.newGroup f.shape.code f.shape.maskCode c = .ok (n, c4) ∧
      g = { f with group := n, moment := 1, own := #[] } :=
  beginLink_same f P.begin

theorem FirstParts.link_eq
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) : g.link = f.link := by
  obtain ⟨n, -, e⟩ := P.begin_same
  rw [e]

theorem FirstParts.rows_eq
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) : g.rows = f.rows := by
  obtain ⟨n, -, e⟩ := P.begin_same
  rw [e]

/-- At a later link the code switch is called on what the last closing has returned. -/
theorem FirstParts.switch_rows
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (h : ¬(f.link == 0) = true) : ∃ s : Switched,
      csSigmaVerify f.rows G.target g.group (firstOthers f) c6 = .ok (s, c7) ∧
        kept = s.kept ∧ ids = s.others := by
  have h' : ¬(g.link == 0) = true := by rw [P.link_eq]; exact h
  obtain ⟨s, a, b⟩ := P.switch h'
  exact ⟨s, P.rows_eq ▸ a, b⟩

/-- At the first link a sending is called. -/
theorem FirstParts.send_zero
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (h : (f.link == 0) = true) : sendVerify (firstOthers f) true c6 = .ok (ids, c7) :=
  (P.sendFirst (by rw [P.link_eq]; exact h)).1

/-- The one test of ChainCheck.first. -/
theorem check_first_test (k : ChainCheck) {c : Ctx} {chk : ChainCheck} {cOut : Ctx}
    (h0 : k.first c = .ok (chk, cOut)) : (!k.inLink && decide (k.link < k.links)) = true := by
  have hr : Runs k.first c chk cOut := h0
  unfold ChainCheck.first at hr
  obtain ⟨_, c1, h1, -⟩ := HasRuns.runs_bind hr
  exact (runs_must h1).1

#print axioms beginLink_same
#print axioms FirstParts.switch_rows
#print axioms check_first_test

end OnBytes.L5
