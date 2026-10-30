-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/ClosedPlace.lean: the closed record of a smallness test (`closedAt`,
ClosedRec.lean) at a link of a written chain: the list of the tables' shapes is no letter.

In ClosedRec.lean the list sh of the tables' shapes is a letter, and the Bool `closedTest` does not
tell the shapes of the verifier's own tables from others. OnBytes/Tie/Pv/Plan/PlaceTabs.lean has,
for a link n of a chain c, the tables that the verifier's own routines lay out in a dry run
(`Plan.funsOf c n`) and the record whose list the verifier closes (`Plan.openOf n`). Here sh is the
list of the shapes of these tables, and the closed record at the link is a definition.

Main names (namespace OnBytes.Tie.Pv.Tail.Closed):
  `shAt c n`: the shapes of the tables of `Plan.funsOf c n`; the empty list where that dry run
    fails. `shAt_ok`.
  `recAt c n`: `closedAt (Plan.openOf n) (shAt c n)`: the record at which `tail_link_closed`
    (ClosedLink.lean) and `tail_link_at` (ClosedLay.lean) are meant at link n: they are called at
    tl₀ := Plan.openOf n and sh := shAt c n.
  `recAt_closed`: where `closeFuns` at the record `Plan.openOf n` and the tables of the dry run
    returns a record, `recAt c n` agrees with it but for the tables' weights and the first columns,
    which `closeFuns` leaves empty. `closedOf_ok`, `recAt_closedOf`: that record is what
    `Plan.closedOf c n` returns, so the same holds wherever `Plan.closedOf c n` returns a record.
  `TabsOK`, `tabsTest`, `tabsOK_of_test`: further clauses on a list of shapes, as one Bool: every
    table's matrix is one of the record's; its length is not 0 and divides the matrix's rows of
    cells; it ends at or before N; the number of reads is a given number.
Limits: `Plan.funsOf c n` is a computed value behind Except, by a dry run on zeros: that a table's
matrix, length and first entry hang on nothing that is drawn or sent is not proved here or there.
Where the dry run fails `shAt` is empty and `recAt` has no table. `tabsTest` is a Bool on public
numbers: that it is true at a given link is a run, no proof term; it does not tell a list from the
same list in another order.

-/
import OnBytes.Tie.Pv.Plan.PlaceTabs
import OnBytes.Tie.Pv.Tail.ClosedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Closed
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail

/-- The shapes of the tables that the verifier's own routines lay out at a link. -/
def shAt (c : Plan.Chain1) (n : Plan.LinkNums) : List Tab :=
  match Plan.funsOf c n with
  | .ok x => shapesOf x.1
  | .error _ => []

theorem shAt_ok {c : Plan.Chain1} {n : Plan.LinkNums} {x : Array HFun × Nat}
    (h : Plan.funsOf c n = .ok x) : shAt c n = shapesOf x.1 := by
  unfold shAt
  rw [h]

/-- The closed record at a link. -/
def recAt (c : Plan.Chain1) (n : Plan.LinkNums) : HTailF2 := closedAt (Plan.openOf n) (shAt c n)

/-- It agrees with the record that the verifier's own routine closes, but for the tables' weights
and the first columns. -/
theorem recAt_closed {c : Plan.Chain1} {n : Plan.LinkNums} {x : Array HFun × Nat}
    (h : Plan.funsOf c n = .ok x) {tl' : HTailF2}
    (hc : (Plan.openOf n).closeFuns x.1 = some tl') :
    recAt c n = { tl' with funs := funsOf (shapesOf x.1) fun _ => #[], cfFirst := firstCols tl' } :=
        by
  unfold recAt
  rw [shAt_ok h]
  exact closedAt_close (Plan.openOf n) tl' x.1 hc

/-- What `Plan.closedOf` returns is what the verifier's own routine returns at the tables of the dry
run. -/
theorem closedOf_ok {c : Plan.Chain1} {n : Plan.LinkNums} {tl' : HTailF2}
    (h : Plan.closedOf c n = .ok tl') :
    ∃ x, Plan.funsOf c n = .ok x ∧ (Plan.openOf n).closeFuns x.1 = some tl' := by
  unfold Plan.closedOf at h
  cases hf : Plan.funsOf c n with
  | error e =>
    rw [hf] at h
    cases h
  | ok x =>
    rw [hf] at h
    refine ⟨x, rfl, ?_⟩
    cases hc : (Plan.openOf n).closeFuns x.1 with
    | none =>
      have h' : (match (Plan.openOf n).closeFuns x.1 with
        | none => (.error "the list is closed already" : Except String HTailF2)
        | some tl => pure tl) = .ok tl' := h
      rw [hc] at h'
      cases h'
    | some tl =>
      have h' : (match (Plan.openOf n).closeFuns x.1 with
        | none => (.error "the list is closed already" : Except String HTailF2)
        | some tl => pure tl) = .ok tl' := h
      rw [hc] at h'
      exact congrArg some (Except.ok.inj h')

/-- Where `Plan.closedOf c n` returns a record, the closed record at the link agrees with it but for
the tables' weights and the first columns. -/
theorem recAt_closedOf {c : Plan.Chain1} {n : Plan.LinkNums} {tl' : HTailF2}
    (h : Plan.closedOf c n = .ok tl') :
    recAt c n = { tl' with funs := funsOf (shAt c n) fun _ => #[], cfFirst := firstCols tl' } := by
  obtain ⟨x, hx, hc⟩ := closedOf_ok h
  rw [shAt_ok hx]
  exact recAt_closed hx hc

/-- Further clauses on a list of shapes. -/
structure TabsOK (tl : HTailF2) (sh : List Tab) (N reads : ℕ) : Prop where
  mat : ∀ t ∈ sh, t.mat < tl.NM
  len : ∀ t ∈ sh, t.len ≠ 0
  dvd : ∀ t ∈ sh, (tl.mats.getD t.mat {}).m % t.len = 0
  ends : ∀ t ∈ sh, t.start + (tl.mats.getD t.mat {}).k * ((tl.mats.getD t.mat {}).m / t.len) ≤ N
  reads : readsNo tl sh = reads

/-- One Bool for them. -/
def tabsTest (tl : HTailF2) (sh : List Tab) (N reads : ℕ) : Bool :=
  (sh.all fun t => decide (t.mat < tl.NM) && decide (t.len ≠ 0) &&
    decide ((tl.mats.getD t.mat {}).m % t.len = 0) &&
    decide (t.start + (tl.mats.getD t.mat {}).k * ((tl.mats.getD t.mat {}).m / t.len) ≤ N)) &&
  decide (readsNo tl sh = reads)

theorem tabsOK_of_test {tl : HTailF2} {sh : List Tab} {N reads : ℕ}
    (h : tabsTest tl sh N reads = true) : TabsOK tl sh N reads := by
  simp only [tabsTest, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun t ht => (h.1 t ht).1.1.1, fun t ht => (h.1 t ht).1.1.2, fun t ht => (h.1 t ht).1.2,
    fun t ht => (h.1 t ht).2, h.2⟩

end OnBytes.Tie.Pv.Tail.Closed

#print axioms OnBytes.Tie.Pv.Tail.Closed.shAt_ok
#print axioms OnBytes.Tie.Pv.Tail.Closed.recAt_closed
#print axioms OnBytes.Tie.Pv.Tail.Closed.closedOf_ok
#print axioms OnBytes.Tie.Pv.Tail.Closed.recAt_closedOf
#print axioms OnBytes.Tie.Pv.Tail.Closed.tabsOK_of_test
