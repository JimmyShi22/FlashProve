-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ReadsOAgrees.lean: a yardstick beside Att/ReadsO.lean: its step says yes just
where Att/ReadsH.lean's does, with the same result; at the state likewise. The refusals' names
differ.

`step_ok_iff`: readsStepO … = .ok r ↔ readsStepH … = .ok r. `atS_ok_iff`: the like for readsAtSO
and readsAtSH. By Johnson/Desc/First/K8/OrderAgrees.lean's close_eq and front_ok_iff and
Att/LookOAgrees.lean's lookOfO_eq.
No running text imports this file.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.ReadsO
import Johnson.Desc.First.Att.ReadsH
import Johnson.Desc.First.Att.LookOAgrees
import Johnson.Desc.First.K8.OrderAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model
open VerifiableInference.Desc (named need)

theorem close_ok_iff (tl tl' : HTailF2) (funs : Array HFun) (L : LinkCtx) (F : Fork) :
    K8.Order.close tl funs = .ok tl' ↔
      L3.closeStep funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit) =
        .ok { L := L, F := F, tl := tl', w := () } := by
  have h := K8.Order.close_eq tl funs
  unfold L3.closeStep
  cases hc : K8.Order.close tl funs with
  | error e =>
    rw [hc] at h
    simp only [Except.toOption] at h
    simp [← h]
  | ok x =>
    rw [hc] at h
    simp only [Except.toOption] at h
    simp [← h]

theorem front_ok (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    K8.Order.front tl L S = .ok () ↔ L3.drawFront tl L S = .ok () := by
  have h := K8.Order.front_ok_iff tl L S
  cases h1 : K8.Order.front tl L S <;> cases h2 : L3.drawFront tl L S <;>
    simp_all [Except.isOk, Except.toBool]

theorem closeStep_of (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (F : Fork) :
    (∀ x, K8.Order.close tl funs = .ok x →
      L3.closeStep funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit) =
        .ok { L := L, F := F, tl := x, w := () }) ∧
    (∀ e, K8.Order.close tl funs = .error e →
      ∃ e', L3.closeStep funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit) =
        .error e') := by
  have h := K8.Order.close_eq tl funs
  constructor
  · intro x hx
    rw [hx] at h
    simp only [Except.toOption] at h
    unfold L3.closeStep
    simp [← h]
  · intro e he
    rw [he] at h
    simp only [Except.toOption] at h
    unfold L3.closeStep
    simp [← h]

/-- **The two steps say yes together, with one result.** -/
theorem step_ok_iff (c : P.ParC) (zk : Array (Array E)) (look : P.LookIn) (h : P.Heard)
    (tl : HTailF2) (L : LinkCtx) (S : Statement) (F : Fork) (r : Attention.Tables × HTailF2 × Nat) :
    readsStepO c zk look h tl L S F = .ok r ↔ readsStepH c zk look h tl L S F = .ok r := by
  unfold readsStepO readsStepH
  simp only [HTailF2.funOpen, bind, Except.bind, pure, Except.pure]
  cases need "A.reads.open" (!tl.funClosed) with
  | error e => simp
  | ok _ =>
    simp only []
    cases named "A.reads.points" (P.ptsFrom c.geo zk h F) with
    | error e => simp
    | ok p =>
      simp only []
      cases named "A.reads.tables" (P.tablesP c.geo c.mats c.nW look p) with
      | error e => simp
      | ok t =>
        simp only []
        obtain ⟨k1, k2⟩ := closeStep_of tl (tabsBack t).funs L F
        cases hc : K8.Order.close tl (tabsBack t).funs with
        | error e =>
          obtain ⟨e', he'⟩ := k2 e hc
          simp [he']
        | ok x =>
          rw [k1 x hc]
          have hf := front_ok x L S
          cases h1 : K8.Order.front x L S <;> cases h2 : L3.drawFront x L S <;> simp_all

/-- **At the state likewise.** -/
theorem atS_ok_iff (A : Attention.Plan) (s s' : First.S) :
    readsAtSO A s = .ok s' ↔ readsAtSH A s = .ok s' := by
  unfold readsAtSO readsAtSH
  rw [P.lookOfO_eq]
  simp only [bind, Except.bind, pure, Except.pure]
  cases s.here with
  | att a =>
    simp only []
    cases named "A.reads.heard" s.heard5? with
    | error e => simp
    | ok h =>
      simp only []
      cases named "A.reads.look" a.g with
      | error e => simp
      | ok g =>
        simp only []
        have k := step_ok_iff (P.parCOf A) g.zk (P.lookOf (P.parCOf A).geo.lmb g) h a.tl a.L s.st
          a.F
        cases h1 : readsStepO (P.parCOf A) g.zk (P.lookOf (P.parCOf A).geo.lmb g) h a.tl a.L s.st
            a.F with
        | error e =>
          cases h2 : readsStepH (P.parCOf A) g.zk (P.lookOf (P.parCOf A).geo.lmb g) h a.tl a.L s.st
              a.F with
          | error e' => simp
          | ok r => exact absurd ((k r).2 h2) (by rw [h1]; simp)
        | ok r =>
          rw [(k r).1 h1]
  | _ => simp

end VerifiableInference.Desc.First.Att
