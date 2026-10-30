-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowsCov.lean: the rows that the sumchecks of kind K5 leave name no entry
of any tree: so the
premise RowsCov of Att/Claims/Covered.lean (the rows name no entry outside the tables' part) is a
lemma.

Main names:
  `cov_nil`, `cov_onSlots`, `cov_batched`: the empty form; a form with slots added; the kind's
    batched start form.
  `cov_formOf`: a record whose start form is covered leaves a covered row (formOf: a constant,
    slots, the start form,
    the empty kept form).
  `sumAt_start`, `units_cov`: each sumcheck's start form, as it was heard: a slot, a batch of slots,
    or the constant 0.
  `rows_cov`: LeftIs i.g zk h F l, Said x h G L and PointsAre i.g zk h l i.p give RowsCov i K nW, at
    all K and nW.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Covered
import Johnson.Desc.First.Att.Claims.PointsRows
import Johnson.Desc.First.Att.K5LeftAll
import Johnson.Desc.First.Att.K5SaidAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open K5Law (Cov cov_ofConst cov_slot cov_addMul cov_sub RowsCov PointsAre)

variable {iU3 K nW : ℕ}

theorem cov_nil : Cov iU3 K nW ({} : Aff) := by
  intro e he
  simp at he

theorem cov_onSlots : ∀ (u : List E) (f : Aff) (first : ℕ), Cov iU3 K nW f →
    Cov iU3 K nW (MaskedSum.onSlots f first u)
  | [], _, _, h => h
  | x :: u, f, first, h => cov_onSlots u (Aff.addMul f (Aff.slot first) x) (first + 1) (cov_addMul h (cov_slot _) x)

theorem cov_batched (n : ℕ) (w : Array E) (first step off : ℕ) : Cov iU3 K nW (batched n w first step off) := by
  unfold batched
  generalize List.range n = l
  have : ∀ (l : List ℕ) (a : Aff), Cov iU3 K nW a → Cov iU3 K nW
      (l.foldl (fun a b => a.addMul (.slot (first + (step * b + off))) (w.getD b zeroE)) a) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons b l ih => exact fun a h => ih _ (cov_addMul h (cov_slot _) _)
  exact this l _ (cov_ofConst _)

theorem cov_formOf (hh : MaskedSum.Heard) (S0 : E) (h : Cov iU3 K nW hh.start) : Cov iU3 K nW (formOf hh S0 {}) := by
  unfold formOf
  exact cov_addMul (cov_addMul (cov_onSlots _ _ _ (cov_ofConst _)) (cov_sub (cov_ofConst _) h) _) cov_nil _

/-- A sumcheck's start form, as it was heard. -/
theorem sumAt_start {C : Aff} {st : Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH} {hh : MaskedSum.Heard}
    {G : Fork} (h : SumAt C st pre H hh G) : hh.start = C := by
  obtain ⟨_, _, _, _, _, _, sd, _⟩ := h
  exact sd.start

theorem units_cov {G : Fork} : ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E)
    (l : List (List E × OnBytes.Tie.Pv.Att.PscH)), UnitsAt ps os pre l G → ∀ o ∈ os, Cov iU3 K nW o.2.start
  | [], [], _, [], _ => fun _ ho => by cases ho
  | _ :: ps, o :: os, _, (_, _) :: l, ⟨_, _, a3, _, a5⟩ => fun o' ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · rw [sumAt_start a3]
      exact cov_slot _
    · exact units_cov ps os [] l a5 o' ho
  | [], [], _, _ :: _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim

theorem forall2_left {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs →
    ∀ a ∈ as, ∃ b ∈ bs, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 h2, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., h1⟩
    · obtain ⟨b, hb, hr⟩ := forall2_left h2 a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- **RowsCov is a lemma.** -/
theorem rows_cov {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left} {F G : Fork} {x : Params.AttentionRounds}
    {L : Lists} (li : LeftIs i.g zk h F l) (hs : Said x h G L) (H : PointsAre i.g zk h l i.p) : RowsCov i K nW := by
  obtain ⟨fu, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩, ⟨_, e5⟩, ⟨_, e6⟩⟩ := li.forms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _⟩, _⟩ := forall2_left H.units k hk
    rw [hsc]
    show Cov _ _ _ f
    rw [Array.toList_zip] at hx
    obtain ⟨S0, e0⟩ := (List.forall₂_iff_zip.1 fu).2 hx
    rw [e0]
    refine cov_formOf _ _ (units_cov _ _ _ _ hs.units o ?_)
    have h1 := (List.of_mem_zip hx).1
    rw [Array.toList_zip] at h1
    exact (List.of_mem_zip h1).2
  · rw [H.scE]
    show Cov _ _ _ l.division
    rw [e1]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sE]; exact cov_slot _)
  · rw [H.vpm]
    show Cov _ _ _ l.below
    rw [e2]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sM]; exact cov_slot _)
  · rw [H.vpd]
    show Cov _ _ _ l.on
    rw [e3]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sVD]; exact cov_slot _)
  · rw [H.scF]
    show Cov _ _ _ l.atIndex
    rw [e4]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sF]; exact cov_batched _ _ _ _ _)
  · rw [H.scd]
    show Cov _ _ _ l.key
    rw [e5]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sD]; exact cov_batched _ _ _ _ _)
  · rw [H.scH]
    show Cov _ _ _ l.cells
    rw [e6]
    exact cov_formOf _ _ (by rw [sumAt_start hs.sH]; exact cov_ofConst _)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.rows_cov
