-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsCloses.lean: kind K5: which list the quiet step behind an
attention segment's sending of its reads closes, and what the first chain's record says of that list
behind the step. For the text readsAtSO (Johnson/Desc/First/Att/ReadsO.lean), in the letters of the
smallness test's own close (Johnson/Desc/First/K8/Order.lean).

Why: the smallness test's claims take their list of tables from the record (S.funs?,
Johnson/Desc/First/State.lean) and hold it against the closed list in the test's own record (S.tl?).
At an attention segment S.funs? reads the field t, which this step itself lays: the step does not
read S.funs?. It makes the tables of what the kind heard and what the lookup left, closes the list
at them, and lays both.

Main names:
  `closeStep_tl`: what L3.closeStep (Johnson/Top/H0/L3/Frame.lean) returns differs from what it was
    given in the field tl alone.
  `ClosesIs A s s'`: s stands in an attention segment a; hh is what K5 heard and g what the lookup
    left; p is ptsFrom of these and the ledger a.F; t is tablesP's return at p and at lookOfO of g;
    close at a.tl and (tabsBack t).funs returns tl'; and behind the step S.tl? is tl' and S.funs? is
    (tabsBack t).funs.
  `reads_closes`: readsAtSO A s = .ok s' → ClosesIs A s s'. By `reads_next_o`
    (Johnson/Desc/First/Att/Claims/ReadsNextO.lean) and `close_ok_iff`, `lookOfO_eq`.
  `reads_closes_record`: so behind the step the test's record is closed and S.funs? is that
    record's own list.
  `closes_one`: ClosesIs A s fixes S.funs? and S.tl? behind the step: two next states that both meet
    it agree in these two.
Used: plain records and functions into Option and Except; close is opened in
`reads_closes_record` (two lines of that text). No routine in a context.
Limits: that the step ever returns is not shown in this file or in what it imports. Nothing is said
here of what t.funs holds (which tables, in which order, with which weights). Nothing is said of
later steps: that S.funs? and S.tl? still stand so when the smallness test's claims read them is not
shown.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsNextO

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att

theorem closeStep_tl {funs : Array HFun} {x c : L3.St Unit} (h : L3.closeStep funs x = .ok c) :
    c = { x with tl := c.tl } := by
  unfold L3.closeStep at h
  split at h
  · cases h; rfl
  · cases h

/-- **Which list is closed, and what the record says of it behind the step.** -/
def ClosesIs (A : Plan) (s s' : S) : Prop :=
  ∃ (a : AttOwn) (hh : P.Heard) (g : Forest.Heard) (p : P.Pts) (t : P.TablesP) (tl' : HTailF2),
    s.here = .att a ∧ s.heard5? = some hh ∧ a.g = some g ∧
    P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p ∧
    P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = some t ∧
    K8.Order.close a.tl (tabsBack t).funs = .ok tl' ∧
    s'.tl? = some tl' ∧ s'.funs? = some (tabsBack t).funs

theorem reads_closes (A : Plan) (s s' : S) (h : readsAtSO A s = .ok s') : ClosesIs A s s' := by
  obtain ⟨a, hh, g, p, t, c, h1, h2, h3, h4, h5, h6, rfl⟩ := reads_next_o A s s' h
  have hc : K8.Order.close a.tl (tabsBack t).funs = .ok c.tl := by
    refine (close_ok_iff a.tl c.tl (tabsBack t).funs a.L a.F).2 ?_
    rw [h6]
    exact congrArg Except.ok (closeStep_tl h6)
  refine ⟨a, hh, g, p, t, c.tl, h1, h2, h3, h4, ?_, hc, rfl, rfl⟩
  rw [P.lookOfO_eq]
  exact h5

/-- Behind the step the smallness test's record is closed, and S.funs? is that record's list. -/
theorem reads_closes_record (A : Plan) (s s' : S) (h : readsAtSO A s = .ok s') :
    ∃ tl', s'.tl? = some tl' ∧ tl'.funClosed = true ∧ s'.funs? = some tl'.funs := by
  obtain ⟨a, _, _, _, t, tl', _, _, _, _, _, hc, h7, h8⟩ := reads_closes A s s' h
  unfold K8.Order.close at hc
  split at hc
  · cases hc
  · cases hc
    exact ⟨_, h7, rfl, h8⟩

/-- ClosesIs A s fixes what S.funs? and S.tl? say behind the step. -/
theorem closes_one {A : Plan} {s s₁ s₂ : S} (h₁ : ClosesIs A s s₁) (h₂ : ClosesIs A s s₂) :
    s₁.funs? = s₂.funs? ∧ s₁.tl? = s₂.tl? := by
  obtain ⟨a, hh, g, p, t, tl, e1, e2, e3, e4, e5, e6, e7, e8⟩ := h₁
  obtain ⟨a', hh', g', p', t', tl', f1, f2, f3, f4, f5, f6, f7, f8⟩ := h₂
  rw [e1] at f1; cases f1
  rw [e2] at f2; cases f2
  rw [e3] at f3; cases f3
  rw [e4] at f4; cases f4
  rw [e5] at f5; cases f5
  rw [e6] at f6; cases f6
  exact ⟨by rw [e8, f8], by rw [e7, f7]⟩

end K5Law

#print axioms K5Law.reads_closes
#print axioms K5Law.reads_closes_record
#print axioms K5Law.closes_one
