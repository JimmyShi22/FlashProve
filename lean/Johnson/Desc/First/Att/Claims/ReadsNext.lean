-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsNext.lean: kind K5: the state behind the step that makes an
attention segment's tables and closes the list, whole, for both texts of the step: readsAtS
(Johnson/Desc/First/Att/ReadsBlock.lean: the tables by Tab.tables from the four records) and
readsAtSH (Johnson/Desc/First/Att/ReadsH.lean: by tablesP from what the kind itself heard).

Main names:
  `NextIs P s s'`, `reads_next`: readsAtS P s = .ok s' → the next state is { s with here := .att { a
    with t := some ‹the tables›, tl := ‹the closed record› } }: every other field
    unturned; the tables are Tab.tables of the four; the closed record is that of L3.closeStep at
    the tables' list.
  `NextIsH A s s'`, `reads_next_h`: the like for readsAtSH: the points are those of ptsFrom at what
    was heard, the tables tabsBack of those of tablesP.
  `next_slot`, `next_slot_h`: so a'.F = a.F:
    the step leaves the ledger.
  `plantStepE`, `plantAtS`, `closeStep_closed`, `plant_fails`: a step whose text lays the record as
    it came, unclosed (its text stands in this file, one name turned), fails the law wherever it
    returns.
Used: plain records; L3.closeStep and L3.drawFront (Johnson/Top/H0/L3/Frame.lean: plain functions on
records into Except: named, not opened). No routine in a context and no theorem on a run.
Not claimed: anything on later steps.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsLays
import Johnson.Desc.First.Att.ReadsH

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att

/-- **The state behind the step that makes the tables and closes the list, whole.** -/
def NextIs (P : Plan) (s s' : S) : Prop :=
  ∃ (a : AttOwn) (f : Four) (c : L3.St Unit), s.here = .att a ∧ a.g = some f.g ∧ a.planes = some f.planes ∧
    a.scores = some f.scores ∧ Tab.tables P.S P.mats P.nW f.g f.planes f.scores a.d a.x = some f.t ∧
    L3.closeStep f.t.funs ({ L := a.L, F := a.F, tl := a.tl, w := () } : L3.St Unit) = .ok c ∧
    s' = { s with here := .att { a with t := some f.t, tl := c.tl } }

theorem reads_next (P : Plan) (s s' : S) (h : readsAtS P s = .ok s') : NextIs P s s' := by
  unfold readsAtS at h
  cases hh : s.here with
  | att a =>
    simp only [hh] at h
    cases hg : a.g with
    | none => simp only [hg] at h; cases h
    | some g =>
      cases hp : a.planes with
      | none => simp only [hg, hp] at h; cases h
      | some planes =>
        cases hsc : a.scores with
        | none => simp only [hg, hp, hsc] at h; cases h
        | some scores =>
          simp only [hg, hp, hsc] at h
          cases hr : readsStepE P a.tl ⟨g, planes, scores, a.d, a.x⟩ a.L s.st a.F with
          | error e => rw [hr] at h; cases h
          | ok r =>
            rw [hr] at h
            have e : s' = { s with here := .att { a with t := some r.1, tl := r.2.1 } } := by
              cases h
              rw [hg, hp, hsc]
            subst e
            unfold readsStepE at hr
            obtain ⟨_, _, hr⟩ := except_bind_ok hr
            obtain ⟨t, ht, hr⟩ := except_bind_ok hr
            obtain ⟨c, hc, hr⟩ := except_bind_ok hr
            obtain ⟨_, _, hr⟩ := except_bind_ok hr
            have er : r = (t, c.tl, a.F.next) := by cases hr; rfl
            subst er
            refine ⟨a, ⟨g, planes, scores, t⟩, c, hh, hg, hp, hsc, ?_, hc, rfl⟩
            show Tab.tables P.S P.mats P.nW g planes scores a.d a.x = some t
            cases hT : Tab.tables P.S P.mats P.nW g planes scores a.d a.x with
            | none => rw [hT] at ht; cases ht
            | some t' => rw [hT] at ht; cases ht; rfl
  | _ => simp only [hh] at h; cases h

/-! ### a step that lays the record as it came, unclosed, fails that law -/

/-- The step's text, with one name turned: the record handed on is the one that came in, not the
closed one. -/
def plantStepE (P : Plan) (tl : HTailF2) (f : Attention.First) (L : LinkCtx) (S : Statement) (F : Fork) :
    Except String (Attention.Tables × HTailF2 × Nat) := do
  need "A.reads.open" tl.funOpen
  let t ← named "A.reads.tables" (Tab.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x)
  let s ← L3.closeStep t.funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit)
  L3.drawFront s.tl L S
  pure (t, tl, F.next)

def plantAtS (P : Plan) (s : S) : Except String S :=
  match s.here with
  | .att a =>
    match a.g, a.planes, a.scores with
    | some g, some planes, some scores =>
      (plantStepE P a.tl ⟨g, planes, scores, a.d, a.x⟩ a.L s.st a.F).map fun r =>
        { s with here := .att { a with t := some r.1, tl := r.2.1 } }
    | _, _, _ => .error "A.reads.heard"
  | _ => .error "A.reads.here"

/-- What L3.closeStep returns is closed; it returns only at an open record. -/
theorem closeStep_closed {funs : Array HFun} {x c : L3.St Unit} (h : L3.closeStep funs x = .ok c) :
    c.tl.funClosed = true ∧ x.tl.funClosed = false := by
  unfold L3.closeStep HTailF2.closeFuns at h
  cases hx : x.tl.funClosed with
  | true => simp [hx] at h
  | false =>
    simp only [hx, Bool.false_eq_true, if_false] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem plant_fails (P : Plan) (s s' : S) (h : plantAtS P s = .ok s') : ¬ NextIs P s s' := by
  rintro ⟨a2, f, c2, h2, _, _, _, _, hc2, e2⟩
  unfold plantAtS at h
  simp only [h2] at h
  cases hg : a2.g with
  | none => simp only [hg] at h; cases h
  | some g =>
    cases hp : a2.planes with
    | none => simp only [hg, hp] at h; cases h
    | some planes =>
      cases hsc : a2.scores with
      | none => simp only [hg, hp, hsc] at h; cases h
      | some scores =>
        simp only [hg, hp, hsc] at h
        cases hr : plantStepE P a2.tl ⟨g, planes, scores, a2.d, a2.x⟩ a2.L s.st a2.F with
        | error e => rw [hr] at h; cases h
        | ok r =>
          rw [hr] at h
          unfold plantStepE at hr
          obtain ⟨_, _, hr⟩ := except_bind_ok hr
          obtain ⟨t, _, hr⟩ := except_bind_ok hr
          obtain ⟨c, _, hr⟩ := except_bind_ok hr
          obtain ⟨_, _, hr⟩ := except_bind_ok hr
          have er : r = (t, a2.tl, a2.F.next) := by cases hr; rfl
          subst er
          have e1 : (match s'.here with | .att a => a.tl.funClosed | _ => false) = a2.tl.funClosed := by
            cases h; rfl
          have e3 : (match s'.here with | .att a => a.tl.funClosed | _ => false) = c2.tl.funClosed := by
            rw [e2]
          have k := closeStep_closed hc2
          rw [e3, k.1] at e1
          exact Bool.noConfusion (e1.trans k.2)

/-! ### the step that makes the tables of what was heard -/

theorem named_ok {α : Type} {n : String} {x : Option α} {v : α} (h : named n x = .ok v) : x = some v := by
  cases x with
  | none => cases h
  | some a => cases h; rfl

/-- **The state behind the step that makes the tables of what K5 itself heard and closes the list, whole.** -/
def NextIsH (A : Plan) (s s' : S) : Prop :=
  ∃ (a : AttOwn) (hh : P.Heard) (g : Forest.Heard) (p : P.Pts) (t : P.TablesP) (c : L3.St Unit),
    s.here = .att a ∧ s.heard5? = some hh ∧ a.g = some g ∧
    P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p ∧
    P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW (P.lookOf (P.parCOf A).geo.lmb g) p = some t ∧
    L3.closeStep (tabsBack t).funs ({ L := a.L, F := a.F, tl := a.tl, w := () } : L3.St Unit) = .ok c ∧
    s' = { s with here := .att { a with t := some (tabsBack t), tl := c.tl } }

theorem reads_next_h (A : Plan) (s s' : S) (h : readsAtSH A s = .ok s') : NextIsH A s s' := by
  unfold readsAtSH at h
  cases hh : s.here with
  | att a =>
    simp only [hh] at h
    obtain ⟨h5, e5, h⟩ := except_bind_ok h
    obtain ⟨g, eg, h⟩ := except_bind_ok h
    obtain ⟨r, hr, h⟩ := except_bind_ok h
    have e : s' = { s with here := .att { a with t := some r.1, tl := r.2.1 } } := by
      cases h; rfl
    subst e
    unfold readsStepH at hr
    obtain ⟨_, _, hr⟩ := except_bind_ok hr
    obtain ⟨p, hp, hr⟩ := except_bind_ok hr
    obtain ⟨t, ht, hr⟩ := except_bind_ok hr
    obtain ⟨c, hc, hr⟩ := except_bind_ok hr
    obtain ⟨_, _, hr⟩ := except_bind_ok hr
    have er : r = (tabsBack t, c.tl, a.F.next) := by cases hr; rfl
    subst er
    exact ⟨a, h5, g, p, t, c, hh, named_ok e5, named_ok eg, named_ok hp, named_ok ht, hc, rfl⟩
  | _ => simp only [hh] at h; cases h

/-- What both laws say of the number laid and of the ledger. -/
theorem next_slot {P : Plan} {s s' : S} (h : NextIs P s s') :
    ∃ a a', s.here = .att a ∧ s'.here = .att a' ∧ a'.F = a.F := by
  obtain ⟨a, _, _, h1, _, _, _, _, _, rfl⟩ := h
  exact ⟨a, _, h1, rfl, rfl⟩

theorem next_slot_h {A : Plan} {s s' : S} (h : NextIsH A s s') :
    ∃ a a', s.here = .att a ∧ s'.here = .att a' ∧ a'.F = a.F := by
  obtain ⟨a, _, _, _, _, _, h1, _, _, _, _, _, rfl⟩ := h
  exact ⟨a, _, h1, rfl, rfl⟩

end K5Law
