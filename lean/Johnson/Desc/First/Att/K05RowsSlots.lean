-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowsSlots.lean: kind K5: THE ROWS THAT THE SUMCHECKS LEAVE NAME FILLED SLOTS
ALONE: the premise RowsSlots of Att/Claims/SlotsIn.lean is a lemma, at Ps := "slot j is filled in the
ledger G of which Said speaks". The slots' twin of Att/K05RowsCov.lean.

Main names:
  (PscRun.Filled G j, the library's: G's mark stands at slot j.)
  `putRun_fl`, `sumAt_coefs`, `sumAt_ends`, `sumAt_endsKey`: what Said (Att/K5SaidAll.lean) says lies
    under a run of scalars, under a sumcheck's coefficients' slots, under its end values' slots.
  `slotsIn_onSlots`, `slotsIn_batched`, `slotsIn_formOf`: a form with slots added; the kind's batched
    start form; the row of a record whose start form and coefficients' slots are such.
  `units_slots`: each unit's sumcheck: its start form, its coefficients' slots.
  `rows_slots`: **LeftIs i.g zk h F l, Said x h G L and PointsAre i.g zk h l i.p give
    RowsSlots (PscRun.Filled G) i.p.**
  `fl_bites`: a control: the form "slot j" at a slot that is free in G has not SlotsIn (PscRun.Filled G).
Premises: those three. Limits: nothing on what lies under a slot; nothing on the runs' forms. EMPTY
AT: a hearing of which Said does not hold; a record of points that pointsOf did not make.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SlotsIn
import Johnson.Desc.First.Att.K05RowsCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open K5Law (SlotsIn slotsIn_empty slotsIn_ofConst slotsIn_slot slotsIn_addMul slotsIn_sub RowsSlots
  PointsAre)

theorem putRun_fl {G : Fork} {j : ℕ} {v : List E} (h : PutRun G j v) : ∀ i, i < v.length → PscRun.Filled G (j + i) :=
  fun i hi => (h i hi).1

theorem sumAt_coefs {C : Aff} {st : Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C st pre H hh G) :
    ∀ i, i < (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length → PscRun.Filled G (hh.first + i) := by
  obtain ⟨_, _, _, _, _, _, sd, s⟩ := h
  exact fun i hi => (s _ _ _ (sd.coefs i hi)).1

theorem sumAt_ends {C : Aff} {n m : ℕ} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (products n m) pre H hh G) :
    ∀ i, i < 2 * m → PscRun.Filled G (hh.sEnd + i) := by
  obtain ⟨vs, e, _, _, _, a, sd, s⟩ := h
  have he : e.n = 2 * m := by
    unfold products at a
    injection a with _ h2
    rw [← h2]
  exact fun i hi => (s _ _ _ (sd.ends i (by rw [he]; exact hi))).1

theorem sumAt_endsKey {C : Aff} {x : Params.AttentionRounds} {pre : List E}
    {H : OnBytes.Tie.Pv.Att.PscH} {hh : MaskedSum.Heard} {G : Fork}
    (h : SumAt C (keyStage x) pre H hh G) : ∀ i, i < x.Lam + x.pairs * x.lt → PscRun.Filled G (hh.sEnd + i) := by
  obtain ⟨vs, e, _, _, _, a, sd, s⟩ := h
  have he : e.n = x.Lam + x.pairs * x.lt := by
    unfold keyStage at a
    injection a with _ h2
    rw [← h2]
  exact fun i hi => (s _ _ _ (sd.ends i (by rw [he]; exact hi))).1

variable {Ps : ℕ → Prop}

theorem slotsIn_onSlots : ∀ (u : List E) (f : Aff) (first : ℕ), SlotsIn Ps f →
    (∀ i, i < u.length → Ps (first + i)) → SlotsIn Ps (MaskedSum.onSlots f first u)
  | [], _, _, h, _ => h
  | x :: u, f, first, h, hp =>
    slotsIn_onSlots u (Aff.addMul f (Aff.slot first) x) (first + 1)
      (slotsIn_addMul x h (slotsIn_slot (hp 0 (Nat.succ_pos _))))
      fun i hi => by
        have := hp (i + 1) (Nat.succ_lt_succ hi)
        rwa [show first + (i + 1) = first + 1 + i by omega] at this

theorem slotsIn_batched (n : ℕ) (w : Array E) (first step off : ℕ)
    (hp : ∀ b, b < n → Ps (first + (step * b + off))) : SlotsIn Ps (batched n w first step off) := by
  unfold batched
  have : ∀ (l : List ℕ) (a : Aff), (∀ b ∈ l, b < n) → SlotsIn Ps a → SlotsIn Ps
      (l.foldl (fun a b => a.addMul (.slot (first + (step * b + off))) (w.getD b zeroE)) a) := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons b l ih =>
      exact fun a hl h => ih _ (fun c hc => hl c (List.mem_cons_of_mem _ hc))
        (slotsIn_addMul _ h (slotsIn_slot (hp b (hl b (List.mem_cons_self ..)))))
  exact this _ _ (fun b hb => List.mem_range.1 hb) (slotsIn_ofConst _)

theorem slotsIn_formOf (hh : MaskedSum.Heard) (S0 : E) (h : SlotsIn Ps hh.start)
    (hc : ∀ i, i < (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length → Ps (hh.first + i)) :
    SlotsIn Ps (formOf hh S0 {}) := by
  unfold formOf
  exact slotsIn_addMul _ (slotsIn_addMul _ (slotsIn_onSlots _ _ _ (slotsIn_ofConst _) hc)
    (slotsIn_sub (slotsIn_ofConst _) h)) slotsIn_empty

/-- A sumcheck seen from G whose start form names filled slots leaves such a row. -/
theorem sumAt_row {C : Aff} {st : Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C st pre H hh G) (hC : SlotsIn (PscRun.Filled G) C) (S0 : E) :
    SlotsIn (PscRun.Filled G) (formOf hh S0 {}) :=
  slotsIn_formOf hh S0 (by rw [sumAt_start h]; exact hC) (sumAt_coefs h)

theorem units_slots {G : Fork} : ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E)
    (l : List (List E × OnBytes.Tie.Pv.Att.PscH)), UnitsAt ps os pre l G → ∀ o ∈ os, ∀ S0,
      SlotsIn (PscRun.Filled G) (formOf o.2 S0 {})
  | [], [], _, [], _ => fun _ ho => by cases ho
  | _ :: ps, o :: os, _, (_, _) :: l, ⟨a1, a2, a3, _, a5⟩ => fun o' ho S0 => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact sumAt_row a3 (slotsIn_slot (putRun_fl a2 6 (by rw [a1]; omega))) S0
    · exact units_slots ps os [] l a5 o' ho S0
  | [], [], _, _ :: _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim

/-- **RowsSlots is a lemma.** -/
theorem rows_slots {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left} {F G : Fork}
    {x : Params.AttentionRounds} {L : Lists} (li : LeftIs i.g zk h F l) (hs : Said x h G L)
    (H : PointsAre i.g zk h l i.p) : RowsSlots (PscRun.Filled G) i.p := by
  obtain ⟨fu, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩, ⟨_, e5⟩, ⟨_, e6⟩⟩ := li.forms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _⟩, _⟩ := forall2_left H.units k hk
    rw [hsc]
    show SlotsIn _ f
    rw [Array.toList_zip] at hx
    obtain ⟨S0, e0⟩ := (List.forall₂_iff_zip.1 fu).2 hx
    rw [e0]
    refine units_slots _ _ _ _ hs.units o ?_ _
    have h1 := (List.of_mem_zip hx).1
    rw [Array.toList_zip] at h1
    exact (List.of_mem_zip h1).2
  · rw [H.scE]
    show SlotsIn _ l.division
    rw [e1]
    exact sumAt_row hs.sE (slotsIn_slot (putRun_fl hs.p5 1 (by rw [hs.l5]; omega))) _
  · rw [H.vpm]
    show SlotsIn _ l.below
    rw [e2]
    exact sumAt_row hs.sM (slotsIn_slot (putRun_fl hs.pC 0 (by rw [hs.lC]; omega))) _
  · rw [H.vpd]
    show SlotsIn _ l.on
    rw [e3]
    exact sumAt_row hs.sVD (slotsIn_slot (putRun_fl hs.pC 1 (by rw [hs.lC]; omega))) _
  · rw [H.scF]
    show SlotsIn _ l.atIndex
    rw [e4]
    refine sumAt_row hs.sF (slotsIn_batched _ _ _ _ _ fun b hb => ?_) _
    have := putRun_fl hs.pM b (by rw [hs.lM]; exact hb)
    rwa [show h.maxima + b = h.maxima + (1 * b + 0) by omega] at this
  · rw [H.scd]
    show SlotsIn _ l.key
    rw [e5]
    exact sumAt_row hs.sD (slotsIn_batched _ _ _ _ _ fun b hb =>
      sumAt_ends hs.sF _ (by omega)) _
  · rw [H.scH]
    show SlotsIn _ l.cells
    rw [e6]
    exact sumAt_row hs.sH (slotsIn_ofConst _) _

/-- A control. -/
theorem fl_bites {G : Fork} {j : ℕ} (h : G.gotF.getD j false = false) :
    ¬ SlotsIn (PscRun.Filled G) (Aff.slot j) :=
  K5Law.slotsIn_bites fun hf => by
    have hf' : G.gotF.getD j false = true := hf
    rw [h] at hf'
    cases hf'

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.fl_bites
#print axioms VerifiableInference.Desc.First.Att.P.sumAt_ends
#print axioms VerifiableInference.Desc.First.Att.P.slotsIn_formOf
#print axioms VerifiableInference.Desc.First.Att.P.rows_slots
