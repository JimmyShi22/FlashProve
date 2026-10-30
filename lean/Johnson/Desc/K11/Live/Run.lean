-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/Run.lean: the proofs of `WalkLive`, `MergeRunLive`, `MergeRunLiveStart`,
`MergeRunPlain`, `MergeRunUnnamed`, `MergeRunHands` and `MergeLiveSlot`
(Johnson/Desc/K11/Live/RunStatement.lean), to the letter, with their helpers and two definitions for
these (`varsAt`, `coefAt`). Lemmas; none of the library's goals.

How. What the run's yes holds is the library's own `claim_inv` (Johnson/Top/H0/MergeLaw/Run.lean):
one claim, whose form is `Psc.rowForm`; of the state the head's ledger alone turns. The linear form
of the hiding polynomial: by induction on the rounds' challenges: each step lays two products of
elements that read other than 0 in front. The form's pairs: `Aff.addMul` only appends pairs
(`addMul_slots`, Johnson/Desc/Kinds/Law/SlotsFilled.lean): so the coefficient on a slot (the sum
over the pairs that name it) is followed through the form's four steps: on a slot of the window it
is the walk's entry. `liveAt` on the field's side: `liveAt_iff`
(Johnson/Desc/K9/Honest/SlotsLive.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Live.RunStatement
import Johnson.Top.H0.MergeLaw.MergeMakesForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Live
open OnBytes (E zeroE oneE mulE addE subE zipT zipT_eq)
open OnBytes.Model (Reading Aff Psc WsForkOut addSlot addSlots slotValue)
open OnBytes.Psc (Weight hidingWalk powers polyAt)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (claim_inv addSlots_mem)
open VerifiableInference.Desc.Kinds.Head.Law (addMul_slots)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt unnamedIn liveAt_iff slotCoef unitAt)

/-! ## The hiding polynomial's linear form -/

/-- The list of variables with their challenges. -/
def varsAt (gs : List E) (b : E) : List (Weight × E) :=
  gs.map (fun g => (Weight.plain 3, g)) ++ [(Weight.atZero 2, b)]

theorem varsAt_ne (gs : List E) (b : E) : varsAt gs b ≠ [] := by
  unfold varsAt
  simp

/-- One step of the walk, in front of a list that is not empty. -/
theorem walk_cons (w : Weight) (g : E) : ∀ l : List (Weight × E), l ≠ [] →
    hidingWalk ((w, g) :: l) =
      (powers (mulE (hidingWalk l).2 g) g (w.d - 1) ++ (hidingWalk l).1,
        mulE (hidingWalk l).2 (polyAt w.psi g))
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- Every coefficient reads other than 0; so does the product; there are 2 n + 2 coefficients, n the
length of gs. -/
theorem walk_all (b : E) (hb : Reading.gl.val b ≠ 0) : ∀ gs : List E,
    (∀ g ∈ gs, Reading.gl.val g ≠ 0) →
    (∀ e ∈ (hidingWalk (varsAt gs b)).1, Reading.gl.val e ≠ 0) ∧
      Reading.gl.val (hidingWalk (varsAt gs b)).2 ≠ 0 ∧
      (hidingWalk (varsAt gs b)).1.length = 2 * gs.length + 2
  | [], _ => by
    have e : hidingWalk (varsAt [] b) =
        ([oneE, mulE oneE b], addE (mulE zeroE b) oneE) := rfl
    rw [e]
    refine ⟨?_, ?_, rfl⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [Reading.gl.one]
        exact one_ne_zero
      · obtain rfl := List.mem_singleton.1 hx
        rw [Reading.gl.mul, Reading.gl.one, one_mul]
        exact hb
    · show Reading.gl.val (addE (mulE zeroE b) oneE) ≠ 0
      rw [Reading.gl.add, Reading.gl.mul, Reading.gl.zero, Reading.gl.one, zero_mul, zero_add]
      exact one_ne_zero
  | g :: gs, h => by
    obtain ⟨i1, i2, i3⟩ := walk_all b hb gs fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hg : Reading.gl.val g ≠ 0 := h g List.mem_cons_self
    have e : hidingWalk (varsAt (g :: gs) b) =
        ([mulE (hidingWalk (varsAt gs b)).2 g, mulE (mulE (hidingWalk (varsAt gs b)).2 g) g] ++
          (hidingWalk (varsAt gs b)).1,
          mulE (hidingWalk (varsAt gs b)).2
            (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE)) :=
      walk_cons (Weight.plain 3) g (varsAt gs b) (varsAt_ne gs b)
    rw [e]
    have hc : Reading.gl.val (mulE (hidingWalk (varsAt gs b)).2 g) ≠ 0 := by
      rw [Reading.gl.mul]
      exact mul_ne_zero i2 hg
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hc
        · obtain rfl := List.mem_singleton.1 hx
          rw [Reading.gl.mul]
          exact mul_ne_zero hc hg
      · exact i1 x hx
    · show Reading.gl.val (mulE _ (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE)) ≠ 0
      rw [Reading.gl.mul, Reading.gl.add, Reading.gl.mul, Reading.gl.add, Reading.gl.mul,
        Reading.gl.zero, Reading.gl.one, zero_mul, zero_add, one_mul, add_zero]
      exact mul_ne_zero i2 hg
    · show ([_, _] ++ (hidingWalk (varsAt gs b)).1).length = _
      rw [List.length_append, i3, List.length_cons]
      show 2 + (2 * gs.length + 2) = 2 * (gs.length + 1) + 2
      omega

/-- **Every coefficient of the linear form, and the product, read other than 0.** -/
theorem walkLive : WalkLive := fun gs b hg hb =>
  ⟨(walk_all b hb gs hg).1, (walk_all b hb gs hg).2.1⟩

/-! ## The coefficient on a slot, through the form's steps -/

/-- The coefficient with which a form names slot j. -/
def coefAt (f : Aff) (j : Nat) : Cb.Gl.E :=
  (f.slots.toList.map (slotValue Reading.gl (unitAt Cb.Gl.E j))).sum

theorem sum_scaled (k : E) (j : Nat) : ∀ l : List (Nat × E),
    ((l.map fun x => (x.1, mulE x.2 k)).map (slotValue Reading.gl (unitAt Cb.Gl.E j))).sum =
      Reading.gl.val k * (l.map (slotValue Reading.gl (unitAt Cb.Gl.E j))).sum
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_scaled k j l, slotValue, Reading.gl.mul]
    ring

theorem coef_addMul (a b : Aff) (k : E) (j : Nat) :
    coefAt (Aff.addMul a b k) j = coefAt a j + Reading.gl.val k * coefAt b j := by
  unfold coefAt
  rw [addMul_slots, List.map_append, List.sum_append, sum_scaled]

theorem coef_slot (i j : Nat) : coefAt (Aff.slot i) j = if i = j then 1 else 0 := by
  show (Reading.gl.val oneE * (if i = j then 1 else 0) + 0 : Cb.Gl.E) = _
  rw [Reading.gl.one, one_mul, add_zero]

/-- Slots from first on are laid: a slot below first keeps its coefficient. -/
theorem coef_below (j : Nat) : ∀ (l : List E) (first : Nat) (a : Aff), j < first →
    coefAt (l.foldl addSlot (first, a)).2 j = coefAt a j
  | [], _, _, _ => rfl
  | y :: l, first, a, h => by
    show coefAt (l.foldl addSlot (first + 1, Aff.addMul a (Aff.slot first) y)).2 j = _
    rw [coef_below j l (first + 1) _ (by omega), coef_addMul, coef_slot,
      if_neg (by omega), mul_zero, add_zero]

/-- On a slot of the window, where the form in front has none: not 0. -/
theorem coef_window (j : Nat) : ∀ (l : List E) (first : Nat) (a : Aff),
    (∀ e ∈ l, Reading.gl.val e ≠ 0) → first ≤ j → j < first + l.length → coefAt a j = 0 →
    coefAt (l.foldl addSlot (first, a)).2 j ≠ 0
  | [], first, _, _, h1, h2, _ => by
    simp at h2
    omega
  | y :: l, first, a, hl, h1, h2, h0 => by
    show coefAt (l.foldl addSlot (first + 1, Aff.addMul a (Aff.slot first) y)).2 j ≠ 0
    by_cases e : first = j
    · rw [coef_below j l (first + 1) _ (by omega), coef_addMul, coef_slot, if_pos e, h0, zero_add,
        mul_one]
      exact hl y List.mem_cons_self
    · refine coef_window j l (first + 1) _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (by omega) (by
          rw [List.length_cons] at h2
          omega) ?_
      rw [coef_addMul, coef_slot, if_neg e, h0, mul_zero, add_zero]

/-- The coefficient of a form that names one slot. -/
theorem coef_one (f : Aff) (sv j : Nat) (c : E) (h : f.slots.toList = [(sv, c)]) :
    coefAt f j = Reading.gl.val c * (if sv = j then 1 else 0) := by
  unfold coefAt
  rw [h]
  show (Reading.gl.val c * (if sv = j then 1 else 0) + 0 : Cb.Gl.E) = _
  rw [add_zero]

/-- The form that the sumcheck leaves, step by step: its coefficient on a slot. -/
theorem coef_rowForm (p : Psc) (S0 c : E) (sv j : Nat) (hs : p.start.slots.toList = [(sv, c)]) :
    coefAt (p.rowForm S0 {}) j =
      coefAt (p.walk.1.foldl addSlot (p.first,
        Aff.ofConst (subE zeroE (subE p.claim (mulE p.eps S0))))).2 j +
      Reading.gl.val (mulE p.eps p.walk.2) *
        (Reading.gl.val (subE zeroE oneE) * (Reading.gl.val c * (if sv = j then 1 else 0))) := by
  have e0 : ∀ v : E, coefAt (Aff.ofConst v) j = 0 := fun _ => rfl
  have e1 : coefAt ({} : Aff) j = 0 := rfl
  have e2 : coefAt (Aff.ofConst p.target - p.start) j =
      Reading.gl.val (subE zeroE oneE) * (Reading.gl.val c * (if sv = j then 1 else 0)) := by
    show coefAt (Aff.addMul (Aff.ofConst p.target) p.start (subE zeroE oneE)) j = _
    rw [coef_addMul, e0, coef_one p.start sv j c hs, zero_add]
  unfold Psc.rowForm
  simp only []
  rw [coef_addMul, coef_addMul, e1, e2, mul_zero, add_zero]
  unfold addSlots
  rw [← Array.foldl_toList]

/-- On a slot of the window: not 0. -/
theorem coef_rowForm_window (p : Psc) (S0 c : E) (sv j : Nat)
    (hs : p.start.slots.toList = [(sv, c)]) (hsv : sv < p.first)
    (hw : ∀ e ∈ p.walk.1, Reading.gl.val e ≠ 0) (h1 : p.first ≤ j)
    (h2 : j < p.first + p.walk.1.length) : coefAt (p.rowForm S0 {}) j ≠ 0 := by
  rw [coef_rowForm p S0 c sv j hs, if_neg (by omega), mul_zero, mul_zero, mul_zero, add_zero]
  exact coef_window j _ p.first _ hw h1 h2 rfl

/-- On the start's slot: not 0. -/
theorem coef_rowForm_start (p : Psc) (S0 c : E) (sv : Nat)
    (hs : p.start.slots.toList = [(sv, c)]) (hsv : sv < p.first) (hc : Reading.gl.val c ≠ 0)
    (he : Reading.gl.val p.eps ≠ 0) (hP : Reading.gl.val p.walk.2 ≠ 0) :
    coefAt (p.rowForm S0 {}) sv ≠ 0 := by
  rw [coef_rowForm p S0 c sv sv hs, coef_below sv _ p.first _ hsv, if_pos rfl, mul_one]
  have e0 : coefAt (Aff.ofConst (subE zeroE (subE p.claim (mulE p.eps S0)))) sv = 0 := rfl
  rw [e0, zero_add, Reading.gl.mul, Reading.gl.sub, Reading.gl.zero, Reading.gl.one, zero_sub]
  exact mul_ne_zero (mul_ne_zero he hP) (mul_ne_zero (neg_ne_zero.2 one_ne_zero) hc)

/-! ## The walk at the condition -/

theorem zip_replicate (w : Weight) : ∀ gs : List E,
    (List.replicate gs.length w).zip gs = gs.map fun g => (w, g)
  | [] => rfl
  | g :: gs => by
    show (w, g) :: ((List.replicate gs.length w).zip gs) = _
    rw [zip_replicate w gs]
    rfl

/-- Under the condition's clauses on the sumcheck: the walk's entries and its product read other
than 0, and there are 2 lk + 2 entries. -/
theorem walk_at (p : Psc) (lk : Nat)
    (hv : p.vars.toList = List.replicate lk (Weight.plain 3) ++ [Weight.atZero 2])
    (hr : p.r.size = lk + 1) (hz : ∀ e ∈ p.r.toList, Reading.gl.val e ≠ 0) :
    (∀ e ∈ p.walk.1, Reading.gl.val e ≠ 0) ∧ Reading.gl.val p.walk.2 ≠ 0 ∧
      p.walk.1.length = 2 * lk + 2 := by
  have hne : p.r.toList ≠ [] := by
    intro h
    have : p.r.toList.length = lk + 1 := by simpa using hr
    rw [h] at this
    simp at this
  obtain ⟨gs, b, hgb⟩ : ∃ gs b, p.r.toList = gs ++ [b] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  have hlen : gs.length = lk := by
    have : p.r.toList.length = lk + 1 := by simpa using hr
    rw [hgb, List.length_append] at this
    simpa using this
  have hw : p.walk = hidingWalk (varsAt gs b) := by
    unfold Psc.walk varsAt
    rw [zipT_eq, hv, hgb, ← hlen, List.zip_append (by simp), zip_replicate]
    rfl
  obtain ⟨a1, a2, a3⟩ := walk_all b (hz b (by rw [hgb]; simp)) gs
    fun g hg => hz g (by rw [hgb]; exact List.mem_append_left _ hg)
  rw [hw]
  exact ⟨a1, a2, by rw [a3, hlen]⟩

/-! ## The seven's other six -/

/-- What the run yields under the condition. -/
theorem run_at {lk first sv n : Nat} {s : S} {z : List Claim × S} (hI : MergeLive lk first sv s)
    (hz : headMergeClaim n s = .ok z) :
    ∃ (a : HeadOwn) (wo : WsForkOut) (c : E) (G : OnBytes.Model.Fork), s.here = .head a ∧
      a.wo = some wo ∧ z.2 = { s with here := .head { a with F := G } } ∧
      z.1 = [{ form := wo.p.rowForm wo.fvp {} }] ∧ wo.p.first = first ∧
      wo.p.start.slots.toList = [(sv, c)] ∧ Reading.gl.val c ≠ 0 ∧ sv < first ∧
      Reading.gl.val wo.p.eps ≠ 0 ∧ (∀ e ∈ wo.p.walk.1, Reading.gl.val e ≠ 0) ∧
      Reading.gl.val wo.p.walk.2 ≠ 0 ∧ wo.p.walk.1.length = 2 * lk + 2 := by
  obtain ⟨a, wo, c, ha, hw, hf, hv, hr, hs, hc, hsv, _, he, hne⟩ := hI
  obtain ⟨cls, s'⟩ := z
  obtain ⟨a', wo', G, ha', hw', hs', hcl, _⟩ := claim_inv hz
  obtain rfl : a' = a := by
    rw [ha] at ha'
    cases ha'
    rfl
  obtain rfl : wo' = wo := Option.some.inj (hw'.symm.trans hw)
  obtain ⟨w1, w2, w3⟩ := walk_at wo'.p lk hv hr hne
  exact ⟨a', wo', c, G, ha, hw, hs', hcl, hf, hs, hc, hsv, he, w1, w2, w3⟩

/-- **`liveAt` on the window.** -/
theorem mergeRunLive : MergeRunLive := by
  intro lk first sv n s z hI hz j h1 h2
  obtain ⟨_, wo, c, _, _, _, _, hcl, hf, hs, _, hsv, _, w1, _, w3⟩ := run_at hI hz
  rw [hcl, liveAt_iff]
  refine ⟨_, List.mem_singleton.2 rfl, rfl, ?_⟩
  exact coef_rowForm_window wo.p wo.fvp c sv j hs (by rw [hf]; exact hsv) w1
    (by rw [hf]; exact h1) (by rw [hf, w3]; omega)

/-- **`liveAt` at the start's slot.** -/
theorem mergeRunLiveStart : MergeRunLiveStart := by
  intro lk first sv n s z hI hz
  obtain ⟨_, wo, c, _, _, _, _, hcl, hf, hs, hc, hsv, he, _, w2, _⟩ := run_at hI hz
  rw [hcl, liveAt_iff]
  refine ⟨_, List.mem_singleton.2 rfl, rfl, ?_⟩
  exact coef_rowForm_start wo.p wo.fvp c sv hs (by rw [hf]; exact hsv) hc he w2

/-- **`plainAt` at every slot.** -/
theorem mergeRunPlain : MergeRunPlain := by
  intro n s z hz j
  obtain ⟨cls, s'⟩ := z
  obtain ⟨_, _, _, _, _, _, hc, _⟩ := claim_inv hz
  show plainAt cls j = true
  rw [hc]
  rfl

/-- **`unnamedAt` at the end value's slot.** -/
theorem mergeRunUnnamed : MergeRunUnnamed := by
  intro lk first sv n s z hI hz
  obtain ⟨_, wo, c, _, _, _, _, hcl, hf, hs, _, hsv, _, _, _, w3⟩ := run_at hI hz
  rw [hcl]
  show (([{ form := wo.p.rowForm wo.fvp {} }] : List Claim).all fun cl =>
    unnamedIn cl (first + 2 * lk + 2)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, unnamedIn, List.all_eq_true, bne_iff_ne]
  intro x hx
  unfold Psc.rowForm at hx
  simp only [] at hx
  rw [addMul_slots, addMul_slots] at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · rcases (addSlots_mem _ _ _).2 x hx with h | ⟨_, h⟩
      · exact absurd h List.not_mem_nil
      · have : x.1 < first + (2 * lk + 2) := by
          rw [← hf, ← w3]
          simpa using h
        omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have hy' : y ∈ (Aff.addMul (Aff.ofConst wo.p.target) wo.p.start
          (subE zeroE oneE)).slots.toList := hy
      rw [addMul_slots, hs] at hy'
      rcases List.mem_append.1 hy' with h | h
      · exact absurd h List.not_mem_nil
      · obtain rfl := List.mem_singleton.1 h
        show sv ≠ _
        omega
  · exact absurd (List.mem_map.1 hx).choose_spec.1 List.not_mem_nil

/-- **The run hands the condition on.** -/
theorem mergeRunHands : MergeRunHands := by
  intro lk first sv n s z hI hz
  obtain ⟨a, wo, c, ha, hw, rest⟩ := hI
  obtain ⟨cls, s'⟩ := z
  obtain ⟨a', _, G, ha', _, hs', _, _⟩ := claim_inv hz
  obtain rfl : a' = a := by
    rw [ha] at ha'
    cases ha'
    rfl
  exact ⟨{ a' with F := G }, wo, c, by rw [hs'], hw, rest⟩

/-- **The slot that the batching's tests read.** -/
theorem mergeLiveSlot : MergeLiveSlot := by
  intro lk first sv s hI
  obtain ⟨a, wo, c, ha, hw, _, _, _, _, _, _, hF, _⟩ := hI
  unfold mergeOf
  rw [ha]
  show a.wo.map (·.sFv) = _
  rw [hw]
  show some wo.sFv = _
  rw [hF]

end Johnson.Desc.First.ForkMerge.Live

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Live.walkLive
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunLive
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunLiveStart
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunPlain
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunUnnamed
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeRunHands
#print axioms Johnson.Desc.First.ForkMerge.Live.mergeLiveSlot
#print axioms Johnson.Desc.First.ForkMerge.Live.varsAt
#print axioms Johnson.Desc.First.ForkMerge.Live.varsAt_ne
#print axioms Johnson.Desc.First.ForkMerge.Live.walk_cons
#print axioms Johnson.Desc.First.ForkMerge.Live.walk_all
#print axioms Johnson.Desc.First.ForkMerge.Live.coefAt
#print axioms Johnson.Desc.First.ForkMerge.Live.sum_scaled
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_addMul
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_slot
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_below
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_window
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_one
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_rowForm
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_rowForm_window
#print axioms Johnson.Desc.First.ForkMerge.Live.coef_rowForm_start
#print axioms Johnson.Desc.First.ForkMerge.Live.zip_replicate
#print axioms Johnson.Desc.First.ForkMerge.Live.walk_at
#print axioms Johnson.Desc.First.ForkMerge.Live.run_at
