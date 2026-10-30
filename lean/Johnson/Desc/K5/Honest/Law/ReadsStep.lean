-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsStep.lean: the quiet step behind an attention segment's sending of
its reads (`readsAtSO`, Johnson/Desc/First/Att/ReadsO.lean), opened: it says yes with the state s'
behind it if and only if nine plain clauses hold.

Main names:
  `Step.need_ok`, `Step.named_ok`, `Step.bind_ok`: a named test goes on just where its Boolean is
    true; a named value just where the value is there; one step after another just where both
    return.
  `close_ok`, `front_ok`: the same for the two texts of the smallness test that the step calls
    (`close`, `front`, Johnson/Desc/First/K8/Order.lean).
  `StepIs A s s'`: the nine clauses: an attention segment is open; what the segment's own rounds
    heard is laid; what the lookup returned is laid; the list of tables is open; the points are
    made; the tables are made; there is one shape a matrix; the guard of order says yes at the
    closed list; and s' is s with the tables laid and the list closed over them.
  `readsAtSO_iff`: `readsAtSO A s = .ok s' ↔ StepIs A s s'`.

Limits. The equivalence unfolds a text; it says nothing on whether the clauses are ever met.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.ReadsO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.First (S K8.Order.close K8.Order.front K8.Order.orderOk)
open VerifiableInference.Desc.First.Att

namespace Step

/-- A named test goes on just where its Boolean is true. -/
theorem need_ok (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true := by
  unfold need
  cases b <;> simp

/-- A named value is returned just where it is there. -/
theorem named_ok {α : Type} (n : String) (x : Option α) (v : α) :
    named n x = .ok v ↔ x = some v := by
  cases x <;> simp [named]

/-- One step after another returns just where both do. -/
theorem bind_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, k⟩ => by cases h; exact k⟩

end Step

open Step

/-- The closing of the list of tables returns just where the list is open, and lays the mark and
the list. -/
theorem close_ok (tl tl' : HTailF2) (funs : Array HFun) :
    K8.Order.close tl funs = .ok tl' ↔
      tl.funClosed = false ∧ tl' = { tl with funClosed := true, funs := funs } := by
  unfold K8.Order.close
  cases h : tl.funClosed
  · simp [eq_comm]
  · simp

/-- The test in front of the draw says yes just where the list is closed, there is one shape a
matrix, and the guard of order says yes. -/
theorem front_ok (tl : HTailF2) (L : LinkCtx) (St : Statement) (u : Unit) :
    K8.Order.front tl L St = .ok u ↔
      tl.funClosed = true ∧ tl.shp.size = tl.NM ∧ K8.Order.orderOk tl L St = true := by
  unfold K8.Order.front
  cases h1 : tl.funClosed
  · simp
  · by_cases h2 : tl.shp.size = tl.NM
    · cases h3 : K8.Order.orderOk tl L St <;> simp [h2]
    · simp [h2]

/-- What the quiet step's yes means, clause by clause. -/
def StepIs (A : Attention.Plan) (s s' : S) : Prop :=
  ∃ (a : VerifiableInference.Desc.First.AttOwn) (hh : P.Heard) (g : Forest.Heard) (p : P.Pts)
    (t : P.TablesP),
    s.here = .att a ∧ s.heard5? = some hh ∧ a.g = some g ∧ a.tl.funClosed = false ∧
    P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p ∧
    P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = some t ∧
    a.tl.shp.size = a.tl.NM ∧
    K8.Order.orderOk { a.tl with funClosed := true, funs := (tabsBack t).funs } a.L s.st = true ∧
    s' = { s with here := .att { a with
      t := some (tabsBack t), tl := { a.tl with funClosed := true, funs := (tabsBack t).funs } } }

/-- **The quiet step says yes, with s' behind it, just where the nine clauses hold.** No
premise. -/
theorem readsAtSO_iff (A : Attention.Plan) (s s' : S) :
    readsAtSO A s = .ok s' ↔ StepIs A s s' := by
  unfold readsAtSO StepIs
  cases hh : s.here with
  | att a =>
    simp only [bind_ok, named_ok, readsStepO, need_ok, close_ok, front_ok, pure, Except.pure,
      Except.ok.injEq, Bool.not_eq_true']
    constructor
    · rintro ⟨h5, e5, g, eg, r, ⟨_, ho, p, ep, t, et, tl', ⟨_, rfl⟩, _, ⟨_, hs, hord⟩, rfl⟩, rfl⟩
      exact ⟨a, h5, g, p, t, rfl, e5, eg, ho, ep, et, hs, hord, rfl⟩
    · rintro ⟨a', h5, g, p, t, ea, e5, eg, ho, ep, et, hs, hord, rfl⟩
      cases ea
      exact ⟨h5, e5, g, eg, _, ⟨(), ho, p, ep, t, et, _, ⟨ho, rfl⟩, (), ⟨rfl, hs, hord⟩, rfl⟩, rfl⟩
  | _ =>
    constructor
    · intro h; cases h
    · rintro ⟨a, _, _, _, _, ea, _⟩; cases ea

end H2K5.Honest

#print axioms H2K5.Honest.Step.need_ok
#print axioms H2K5.Honest.Step.named_ok
#print axioms H2K5.Honest.Step.bind_ok
#print axioms H2K5.Honest.close_ok
#print axioms H2K5.Honest.front_ok
#print axioms H2K5.Honest.readsAtSO_iff
