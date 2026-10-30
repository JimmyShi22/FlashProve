-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MergeMakesForms.lean: ROW K11-14: THE MERGE's ACCEPTING STEP MAKES THE
PUBLIC TEST formsIn AT ITS OWN RUN OF CLAIMS: behind the step, the reader of the run "the merge"
answers, its late slots are in order, and its one form names only what is there. Theorems with their
proofs.

  foldSlot_mem, addSlots_mem, start_mem   which slots the forms' makers name; they name no entry
  rowForm_ents, rowForm_slots   the form that the sumcheck leaves, at kept := {} and a start form
                   wsForkStart sv rho: no entry; every slot lies in the sumcheck's window
                   [first, first + the walk's length) or is one of sv
  lateOk_front     at the ledger IN FRONT of a run the list lateOf F G is in order, where G has F's
                   number of slots
  merge_makes_formsIn   **THE ROW.**

Limits. ONE PREMISE IS ADDED TO THE ROW's: hfree: in front of the merge every slot from the ledger's
next free number on is free (FreeAbove; run_yes_behind's own premise). It is no field of MergeFront
or BehindR. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MergedAtLink
import Johnson.Top.H0.MergeLaw.RunYes
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Top.H0.MergeLaw.Closed
import Johnson.Desc.Kinds.Law.SlotsFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Aff Fork Psc WsForkOut wsForkStart addSlot addSlots)
open OnBytes.PscRun (Later Filled Sized FreeAbove hideRun_fills hideRun_keeps)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9 (formsIn segAt? readerOf Readers lateOf lateOk lateAt slotIn affIn
  maskSeat mergeOf seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (addMul_slots addMul_ents)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim)

/-- A fold that adds multiples of slots names no entry, and names the slots that it is given. -/
theorem foldSlot_mem : ∀ (l : List (ℕ × E)) (a : Aff),
    (l.foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) a).ents.toList = a.ents.toList ∧
      ∀ x ∈ (l.foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) a).slots.toList,
        x ∈ a.slots.toList ∨ ∃ y ∈ l, x.1 = y.1
  | [], a => ⟨rfl, fun x hx => Or.inl hx⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldSlot_mem l (Aff.addMul a (Aff.slot y.1) y.2)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.foldl_cons, h1, addMul_ents]
      show a.ents.toList ++ [] = _
      rw [List.append_nil]
    · rw [List.foldl_cons] at hx
      rcases h2 x hx with h | ⟨z, hz, e⟩
      · rw [addMul_slots] at h
        rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · have h' : x ∈ [(y.1, mulE oneE y.2)] := h
          rw [List.mem_singleton] at h'
          exact Or.inr ⟨y, List.mem_cons_self, by rw [h']⟩
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- The steps of addSlots. -/
theorem addSlot_mem : ∀ (l : List E) (first : ℕ) (a : Aff),
    (l.foldl addSlot (first, a)).2.ents.toList = a.ents.toList ∧
      ∀ x ∈ (l.foldl addSlot (first, a)).2.slots.toList,
        x ∈ a.slots.toList ∨ (first ≤ x.1 ∧ x.1 < first + l.length)
  | [], _, a => ⟨rfl, fun x hx => Or.inl hx⟩
  | y :: l, first, a => by
    obtain ⟨h1, h2⟩ := addSlot_mem l (first + 1) (Aff.addMul a (Aff.slot first) y)
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.foldl_cons]
      show (l.foldl addSlot (first + 1, Aff.addMul a (Aff.slot first) y)).2.ents.toList = _
      rw [h1, addMul_ents]
      show a.ents.toList ++ [] = _
      rw [List.append_nil]
    · rw [List.foldl_cons] at hx
      rcases h2 x hx with h | ⟨g1, g2⟩
      · rw [addMul_slots] at h
        rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · have h' : x ∈ [(first, mulE oneE y)] := h
          rw [List.mem_singleton] at h'
          refine Or.inr ⟨by rw [h'], ?_⟩
          rw [h', List.length_cons]
          show first < _
          omega
      · refine Or.inr ⟨by omega, ?_⟩
        rw [List.length_cons]
        omega

theorem addSlots_mem (a : Aff) (first : ℕ) (form : Array E) :
    (addSlots a first form).ents.toList = a.ents.toList ∧
      ∀ x ∈ (addSlots a first form).slots.toList,
        x ∈ a.slots.toList ∨ (first ≤ x.1 ∧ x.1 < first + form.size) := by
  unfold addSlots
  rw [← Array.foldl_toList]
  have h := addSlot_mem form.toList first a
  rwa [Array.length_toList] at h

/-- The merge's start form. -/
theorem start_mem (sv : Array ℕ) (rho : Array E) :
    (wsForkStart sv rho).ents.toList = [] ∧
      ∀ x ∈ (wsForkStart sv rho).slots.toList, x.1 ∈ sv.toList := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  obtain ⟨h1, h2⟩ := foldSlot_mem (sv.zip rho).toList {}
  refine ⟨h1, fun x hx => ?_⟩
  rcases h2 x hx with h | ⟨y, hy, e⟩
  · exact absurd h List.not_mem_nil
  · rw [Array.toList_zip] at hy
    rw [e]
    exact (List.of_mem_zip (a := y.1) (b := y.2) hy).1

/-- **The form that the sumcheck leaves names no entry.** -/
theorem rowForm_ents (p : Psc) (S0 : E) (sv : Array ℕ) (rho : Array E)
    (hs : p.start = wsForkStart sv rho) : (p.rowForm S0 {}).ents.toList = [] := by
  unfold Psc.rowForm
  simp only []
  rw [addMul_ents, addMul_ents, (addSlots_mem _ _ _).1]
  show ([] ++ (Aff.addMul (Aff.ofConst p.target) p.start _).ents.toList.map _) ++ [] = []
  rw [addMul_ents, hs, (start_mem sv rho).1]
  rfl

/-- **Its slots**: the sumcheck's window, and the start form's. -/
theorem rowForm_slots (p : Psc) (S0 : E) (sv : Array ℕ) (rho : Array E)
    (hs : p.start = wsForkStart sv rho) :
    ∀ x ∈ (p.rowForm S0 {}).slots.toList,
      (p.first ≤ x.1 ∧ x.1 < p.first + p.walk.1.length) ∨ x.1 ∈ sv.toList := by
  intro x hx
  unfold Psc.rowForm at hx
  simp only [] at hx
  rw [addMul_slots, addMul_slots] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases (addSlots_mem _ _ _).2 x hx with h | h
      · exact absurd h List.not_mem_nil
      · rw [List.size_toArray] at h
        exact Or.inl h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have hy' :
          y ∈ (Aff.addMul (Aff.ofConst p.target) p.start (subE zeroE oneE)).slots.toList := hy
      rw [addMul_slots] at hy'
      rcases List.mem_append.1 hy' with h | h
      · exact absurd h List.not_mem_nil
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
        rw [hs] at hz
        exact Or.inr ((start_mem sv rho).2 z hz)
  · exact absurd hx List.not_mem_nil

/-- **At the ledger in front of a run its late slots are in order.** -/
theorem lateOk_front (a : K9.Part) (G : Fork) (hns : G.ns = a.F.ns) :
    lateOk (lateOf a.F G) a = true := by
  unfold lateOk
  refine List.all_eq_true.2 fun x hx => ?_
  have hm := mem_lateOf hx
  have hlt : x.1 < G.ns := by
    unfold lateOf at hx
    obtain ⟨j, hj, hx'⟩ := List.mem_filterMap.1 hx
    split at hx'
    · rw [← Option.some.inj hx']
      exact List.mem_range.1 hj
    · exact nomatch hx'
  have h0 : a.F.gotF.getD x.1 false = false := by
    have := hm.1
    unfold Filled at this
    simpa using this
  simp [h0, ← hns, hlt]

/-- **ROW K11-14: THE MERGE MAKES formsIn AT ITS OWN RUN.** -/
theorem merge_makes_formsIn (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (hf : frontR P s = true)
    (hfree : ∀ a, s.here = .head a → FreeAbove a.F) (own : List (ℕ × ℕ))
    (xM : VerifiableInference.Desc.Sound.Mem) (R : ℕ) (hM : MaskAt own xM R s) :
    formsIn (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s' = true := by
  obtain ⟨a, a', tp, F, claim, x, wo, ha, ha', hcl, hx, hwo, _, hm, hF', _, _, _⟩ := decide_inv h
  obtain ⟨x₁, mu, c, beta, v, T, r1, rY, rV, qs, _, _, _, hT, hE, _, _, hsFv, _, _, _⟩ :=
    hear_ended hm
  have hz : Sized a.F := by
    unfold frontR at hf
    rw [ha] at hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    exact ⟨hf.1.1.1, hf.1.1.2, hf.1.2⟩
  have hlen : wo.p.walk.1.length = 2 * P.lay.lk + 2 := by rw [hE.walkLen, entries_merge]
  have hL : Later a.F a'.F := by
    obtain ⟨b, b', e1, e2, hl⟩ := decide_later h
    rw [ha] at e1
    rw [ha'] at e2
    cases e1
    cases e2
    exact hl
  have hz' : Sized a'.F := hL.sized hz
  obtain ⟨b, b', wo', e1, e2, e3, _, hfirst, hwin⟩ := decide_marks h
  rw [ha] at e1
  rw [ha'] at e2
  cases e1
  cases e2
  rw [hwo] at e3
  cases e3
  obtain ⟨_, _, hwin⟩ := hwin hz (hfree a ha)
  obtain ⟨s₃, hrun⟩ := run_yes_behind h a ha hz (hfree a ha) wo a' ha' hwo hlen 0
  obtain ⟨a₂, wo₂, G, g1, g2, g3, _, hG⟩ := claim_inv hrun
  rw [ha'] at g1
  cases g1
  rw [hwo] at g2
  cases g2
  obtain ⟨a9, o, hseg, ho, hseat, _⟩ := maskAt_behind P h hM
  have hop : a'.opened = true := by
    have hs : (s'.fork?).isSome = true := by
      unfold segAt? at hseg
      cases hl : s'.link? with
      | none => simp [hl] at hseg
      | some L =>
        cases hk : s'.fork? with
        | none => simp [hl, hk] at hseg
        | some F₀ => rfl
    unfold S.fork? at hs
    rw [ha'] at hs
    by_contra hc
    simp [hc] at hs
  have hfork : s'.fork? = some a'.F := by
    unfold S.fork?
    rw [ha']
    simp [hop]
  have hfork₃ : s₃.fork? = some G := by
    rw [g3]
    unfold S.fork?
    simp [hop]
  have ha9 : a9.F = a'.F := by
    unfold segAt? at hseg
    rw [hfork] at hseg
    cases hl : s'.link? with
    | none => simp [hl] at hseg
    | some L =>
      cases ht : s'.tl? with
      | none => simp [hl, ht] at hseg
      | some tl =>
        simp [hl, ht] at hseg
        rw [← hseg]
  have hGl : Later a'.F G := hideRun_keeps hG
  have hents := rowForm_ents wo.p wo.fvp #[x.sV] _ hE.start
  have hread : readerOf (mergeStates "the merge") 8 "the merge" s' =
      some { forms := [wo.p.rowForm wo.fvp {}], late := lateOf a'.F G } := by
    unfold readerOf
    rw [mergeStates_find]
    simp only [Option.bind_some, hrun, hfork, hfork₃]
    have : (wo.p.rowForm wo.fvp {}).ents = #[] := by
      apply Array.toList_inj.1
      exact hents
    simp [this]
  unfold formsIn
  show (match segAt? s', readerOf (mergeStates "the merge") 8 "the merge" s' with
    | some a, some R => lateOk R.late a && R.forms.all fun f => affIn own (mergeOf s') R.late a f
    | _, _ => false) = true
  rw [hseg, hread]
  have hlate : lateOk (lateOf a'.F G) a9 = true := by
    rw [← ha9]
    exact lateOk_front a9 G (by rw [hGl.ns, ha9])
  have hmask : (maskSeat own a9).isSome = true := by
    unfold maskSeat
    rw [VerifiableInference.Desc.Sound.maskAt_eq, ho]
    show (seatAt own a9.d.book o).isSome = true
    rw [hseat]
    rfl
  have hmerge : mergeOf s' = some wo.sFv := by
    unfold mergeOf
    rw [ha']
    show a'.wo.map (·.sFv) = _
    rw [hwo]
    rfl
  have hsv : Filled a.F x.sV ∧ x.sV < a.F.ns := by
    have hfl : Filled a.F x.sV := filled_of_public (x := x₁) hT
    refine ⟨hfl, ?_⟩
    rw [← hz.2.2]
    by_contra hc
    unfold Filled at hfl
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hfl
    simp at hfl
  simp only [hlate, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true]
  unfold affIn
  rw [hents]
  simp only [List.all_nil, Bool.true_and]
  refine List.all_eq_true.2 fun y hy => ?_
  unfold slotIn
  rw [hmask, hmerge, ha9]
  rcases rowForm_slots wo.p wo.fvp #[x.sV] _ hE.start y hy with ⟨w1, w2⟩ | hy'
  · rw [hlen] at w2
    obtain ⟨k1, k2⟩ := hwin y.1 w1 w2
    have k3 : Filled G y.1 := by
      obtain ⟨_, _, hfill, _⟩ := OnBytes.PscRun.hideRun_ok a'.F G _ _ _ hz' hG
      have g := (hfill (y.1 - wo.p.first) (by rw [Array.size_replicate, hlen]; omega)).2.2.1
      rwa [Nat.add_sub_cancel' w1] at g
    have k4 := lateAt_some (F := a'.F) (G := G) (by rw [hGl.ns]; exact k1) k2 k3
    have k5 : wo.sFv ≠ y.1 := by
      rw [hsFv, ← hfirst]
      omega
    simp [k1, k4, k5]
  · have e : y.1 = x.sV := by simpa using hy'
    have k1 : Filled a'.F y.1 := by
      rw [e]
      exact (hL.keep _ hsv.1).1
    have k2 : y.1 < a'.F.ns := by
      rw [e, hL.ns]
      exact hsv.2
    have k5 : wo.sFv ≠ y.1 := by
      intro hc
      refine hfree a ha wo.sFv (by rw [hsFv]; omega) ?_
      rw [hc, e]
      exact hsv.1
    unfold Filled at k1
    simp [k1, k2, k5, hz'.1, hz'.2.1]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.rowForm_ents
#print axioms VerifiableInference.Desc.First.MergeLaw.rowForm_slots
#print axioms VerifiableInference.Desc.First.MergeLaw.lateOk_front
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_makes_formsIn
