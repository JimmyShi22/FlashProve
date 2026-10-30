-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeavesTl.lean: kind K5: what the hearing's block at the seat seatSO
(Johnson/Desc/First/Att/SeatO.lean) writes into the first chain's record, and so what it leaves: the
smallness test's record S.tl? is as it was, and behind a yes no count of rows waits.

Main names:
  `seatSO_lay`: where seatSO.lay returns, an attention segment a is open and the record behind is
    { s with rowsOwed := none, here := .att { a with F := G, heard5 := some h } }.
  `named_some`: named n x = .ok v gives x = some v.
  `k5_lays`: so for the block's decision: there are a, h, G with that record behind.
  `k5_leaves_tl`: Block.Leaves S.tl? (Johnson/Desc/Sound/FoldHeard.lean) of attentionKind seatSO claims p.
  `k5_none_waits`: behind a yes S.noneWaits = true.
  `k5_rowsOwed`: behind a yes S.rowsOwed = none. So Block.Leaves (·.rowsOwed) is not to be had of
    this text by its make: the decision goes on where "some 0" stands in front (it asks S.noneWaits),
    and none would stand behind. That there is a yes at such a record is not shown here.
Used: plain records; the block's decision is opened down to the seat's lay; the hearing is not.
Limits: that the decision ever says yes is not shown here. Leaves runs over all records and rounds.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block named need)

/-- What the hearing's seat lays. -/
theorem seatSO_lay {s s' : First.S} {h : Heard} {G : Fork} (hl : seatSO.lay s h G = some s') :
    ∃ a, s.here = .att a ∧
      s' = { s with rowsOwed := none, here := .att { a with F := G, heard5 := some h } } := by
  have hl' : (match s.here with
      | .att a => a.g.bind fun _ =>
        (First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h).toOption
      | _ => none) = some s' := hl
  cases hh : s.here with
  | att a =>
    rw [hh] at hl'
    simp only at hl'
    cases hg : a.g with
    | none => rw [hg] at hl'; cases hl'
    | some g =>
      rw [hg] at hl'
      simp only [Option.bind_some, First.S.hear5?, First.S.hear5] at hl'
      by_cases h5 : a.heard5.isSome
      · simp only [h5, if_true, First.S.mark, First.S.unmarked] at hl'
        cases hf : s.failed <;> simp [hf, Except.toOption] at hl'
      · simp only [h5, Bool.false_eq_true, if_false, First.S.unmarked] at hl'
        cases hf : s.failed with
        | some m => simp [hf, Except.toOption] at hl'
        | none =>
          simp only [hf, Except.toOption, Option.some.injEq] at hl'
          rw [← hg] at hl'
          exact ⟨a, rfl, hl'.symm⟩
  | _ => rw [hh] at hl'; cases hl'

theorem named_some {α : Type} {n : String} {x : Option α} {v : α} (h : named n x = .ok v) :
    x = some v := by
  cases x with
  | none => cases h
  | some a => cases h; rfl

/-- What the block's decision lays. -/
theorem k5_lays {Cl : Type}
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    {s s' : First.S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (attentionKind seatSO claims p).decide s rs gs = .ok s') :
    ∃ a hh G, s.here = .att a ∧
      s' = { s with rowsOwed := none, here := .att { a with F := G, heard5 := some hh } } := by
  have h' : decide seatSO p s rs = .ok s' := h
  unfold decide at h'
  simp only [bind, Except.bind] at h'
  cases h1 : need "K5.owed" (seatSO.owed s).isNone with
  | error e => rw [h1] at h'; cases h'
  | ok _ =>
    rw [h1] at h'
    simp only at h'
    cases h2 : named "K5.ledger" (seatSO.ledger s) with
    | error e => rw [h2] at h'; cases h'
    | ok F =>
      rw [h2] at h'
      simp only at h'
      cases h3 : named "K5.hear" (hear p.own (F, rs, 0)) with
      | error e => rw [h3] at h'; cases h'
      | ok x =>
        obtain ⟨hh, G, rest, l⟩ := x
        rw [h3] at h'
        simp only at h'
        cases h4 : need "K5.left-over" rest.isEmpty with
        | error e => rw [h4] at h'; cases h'
        | ok _ =>
          rw [h4] at h'
          simp only at h'
          obtain ⟨a, e1, e2⟩ := seatSO_lay (named_some h')
          exact ⟨a, hh, G, e1, e2⟩

/-- **The hearing's block leaves the smallness test's record.** -/
theorem k5_leaves_tl {Cl : Type}
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par) :
    (attentionKind seatSO claims p).Leaves First.S.tl? := by
  intro s rs gs s' h
  obtain ⟨a, hh, G, e1, rfl⟩ := k5_lays claims p h
  simp only [First.S.tl?, e1]

/-- Behind a yes nothing is owed. -/
theorem k5_rowsOwed {Cl : Type}
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    {s s' : First.S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (attentionKind seatSO claims p).decide s rs gs = .ok s') : s'.rowsOwed = none := by
  obtain ⟨a, hh, G, _, rfl⟩ := k5_lays claims p h
  rfl

/-- Behind a yes no count of rows waits. -/
theorem k5_none_waits {Cl : Type}
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    {s s' : First.S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (attentionKind seatSO claims p).decide s rs gs = .ok s') : s'.noneWaits = true := by
  unfold First.S.noneWaits
  rw [k5_rowsOwed claims p h]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5_leaves_tl
#print axioms VerifiableInference.Desc.First.Att.P.k5_none_waits
