-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Coef.lean: the coefficient with which a form names a hidden
scalar's slot, and the coefficients of the one form that a masked sumcheck leaves. Definitions,
statements and proofs ON THE VERIFIER's TEXT; no prover is in this file.

Why. Behind a segment's batching the verifier asks that every sent scalar stands in a claim: that
its coefficient in the sum of all claims is not 0. Johnson/Desc/K9/Honest/SlotsLive.lean states what
a list of claims must have for that (`liveAt`: some claim that takes its own number names the slot
with a coefficient other than 0). This file gives the tools to show it of the output head's claims:
the tools for `liveAt`; that file's `plainAt` and `unnamedAt` are not spoken of.

  `delta j f`       the coefficient of the form f on slot j: f's value in the world in which the
                    value under slot j is 1 and all else 0, less its value in the world in which all
                    is 0
`slotCoef_asClaim` it is `slotCoef` (Johnson/Desc/K9/Honest/SlotsFew.lean) of the plain claim of f
  `live_of_delta`   a form of a list with a coefficient other than 0 on slot j makes the slot live
  `kept_delta`      "the coefficient on slot j is 0" is kept by the forms' arithmetic (`Kept`,
                    Johnson/Desc/Kinds/Law/FormsAll.lean)
  `delta_add`, `delta_sub`, `delta_slot`, `delta_sm`, `delta_slotsIn`, `delta_bare`   the
                    coefficient through the forms' arithmetic; GoodLaw/Forms.lean calls them too
  `AllPoint l`      every variable of the list is summed at a point
  `hidingAt_ne`     **at variables that are summed at a point, with no challenge 0: every
                    coefficient of the hiding polynomial's linear form reads as other than 0, and
                    the product of all psi reads as 1**
  `hidingAt_one`    the second half alone: it asks nothing of the challenges
  `delta_rowForm`   the coefficient of a masked sumcheck's one form on any slot
  `delta_own`, `delta_lead`   so on each of its own slots, and on the claimed sum's slot
  `live_own`, `live_lead`, `live_var`   the same as "the slot is live", at what the part's hearing
                    hands back
  `delta_lead'`, `live_lead'`   `delta_lead` and `live_lead` without their premise on the
                    challenges, which these two ask and do not need
All else is a helper of this file.

Limits. CONDITIONAL: no challenge reads as 0; the reading of the rounds returns; the start form
names only slots in front of the sumcheck's own; for the claimed sum's slot: it lies in front, the
start form is that one slot, and the element sampled at the beginning does not read as 0.
Nothing on the batching element: a slot that is live has a coefficient in the sum that is a
polynomial in it other than the zero polynomial, and can still come to 0. "Reads as" means the
reading of three words as an element of the field (`Reading.gl`). GROUND:
Johnson/Desc/K9/Honest/SlotsFew.lean and SlotsLive.lean:
four of their definitions and two of their theorems are called.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.SlotsFilled
import Johnson.Desc.Kinds.Law.HeardEnds
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Part.MaskedSumRow
import Johnson.Desc.K9.Honest.SlotsLive
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.Kinds.Law.HonestParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6.GoodLaw

section
open OnBytes (E zeroE oneE mulE)
open OnBytes.Model (Aff Reading World)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (asClaim)
open VerifiableInference.Desc.Kinds.Head.Law (K rd Kept)
open VerifiableInference.Desc.Kinds.Head.Law.Came (val)
open VerifiableInference.Desc.K9H (unitAt nought slotCoef liveAt)
open VerifiableInference.Desc.Part.MaskedSum (Var Heard hidingAt psiAt powersFrom rowForm dotFrom)

/-- The coefficient with which a form names slot j: its value in the world in which the value under
slot j is 1 and all else 0, less its value in the world in which all is 0. -/
noncomputable def delta (j : Nat) (f : Form) : K := val (unitAt K j) f - val (nought K) f

theorem slotCoef_asClaim (f : Form) (j : Nat) :
    slotCoef Reading.gl (asClaim f) j = delta j f := by
  rw [← VerifiableInference.Desc.K9H.claimValue_sub]
  simp [delta, val, VerifiableInference.Desc.K9L.claimValue, asClaim]

/-- A form of the list with a coefficient other than 0 on slot j makes the slot live. -/
theorem live_of_delta {fs : List Form} {f : Form} (hf : f ∈ fs) {j : Nat} (h : delta j f ≠ 0) :
    liveAt (fs.map asClaim) j = true := by
  rw [VerifiableInference.Desc.K9H.liveAt_iff]
  exact ⟨asClaim f, List.mem_map_of_mem hf, rfl, by rw [slotCoef_asClaim]; exact h⟩

theorem delta_add (j : Nat) (f g : Form) : delta j (f + g) = delta j f + delta j g := by
  unfold delta
  rw [Head.Law.Came.val_add, Head.Law.Came.val_add]
  ring

theorem delta_sub (j : Nat) (f g : Form) : delta j (f - g) = delta j f - delta j g := by
  unfold delta
  rw [Head.Law.Came.val_sub, Head.Law.Came.val_sub]
  ring

theorem delta_slot (j i : Nat) : delta j (Aff.slot i) = if i = j then 1 else 0 := by
  unfold delta val
  rw [Aff.value_slot, Aff.value_slot]
  show (if i = j then (1 : K) else 0) - 0 = _
  ring

/-- "The coefficient on slot j is 0" is kept by the forms' arithmetic. -/
theorem kept_delta (j : Nat) : Kept (fun f => delta j f = 0) where
  addMul := fun {a b} k ha hb => by
    have ha' : val (unitAt K j) a - val (nought K) a = 0 := ha
    have hb' : val (unitAt K j) b - val (nought K) b = 0 := hb
    show val (unitAt K j) (Aff.addMul a b k) - val (nought K) (Aff.addMul a b k) = 0
    unfold val at ha' hb' ⊢
    rw [Aff.value_addMul, Aff.value_addMul]
    linear_combination ha' + Reading.gl.val k * hb'
  bare := fun f he hs => by
    show val (unitAt K j) f - val (nought K) f = 0
    unfold val Aff.value
    rw [he, hs]
    simp

/-- A form that does not name slot j has the coefficient 0 there. -/
theorem delta_unnamed (j : Nat) (f : Form) (h : ∀ x, x ∈ f.slots.toList → x.1 ≠ j) :
    delta j f = 0 := by
  unfold delta val Aff.value
  have e1 : f.slots.toList.map (OnBytes.Model.slotValue Reading.gl (unitAt K j)) =
      f.slots.toList.map (OnBytes.Model.slotValue Reading.gl (nought K)) :=
    List.map_congr_left fun x hx => by
      show Reading.gl.val x.2 * (if x.1 = j then (1 : K) else 0) = Reading.gl.val x.2 * 0
      rw [if_neg (h x hx)]
  have e2 : f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl (unitAt K j)) =
      f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl (nought K)) := rfl
  rw [e1, e2]
  ring

/-! ## The hiding polynomial's linear form at point variables -/

theorem powersFrom_ne (x : E) (hx : rd x ≠ 0) : ∀ (n : Nat) (a : E), rd a ≠ 0 →
    ∀ w ∈ powersFrom x n a, rd w ≠ 0
  | 0, _, _, w, hw => by simp [powersFrom] at hw
  | n + 1, a, ha, w, hw => by
    rw [powersFrom, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ha
    · refine powersFrom_ne x hx n (mulE a x) ?_ w hw
      show Reading.gl.val (mulE a x) ≠ 0
      rw [Reading.gl.mul]
      exact mul_ne_zero ha hx

/-- Every variable is summed at a point. -/
def AllPoint (l : List (Var × E)) : Prop := ∀ p ∈ l, ∃ z d, p.1 = Var.point z d

/-- **At point variables, with no challenge 0: every coefficient of the hiding polynomial's linear
form is other than 0, and the product of all psi is 1.** -/
theorem hidingAt_ne : ∀ (l : List (Var × E)), AllPoint l → (∀ p ∈ l, rd p.2 ≠ 0) →
    (∀ w ∈ (hidingAt l).1, rd w ≠ 0) ∧ rd (hidingAt l).2 = 1
  | [], _, _ => ⟨fun w hw => by simp [hidingAt] at hw, Reading.gl.one⟩
  | [(v, r)], hp, hr => by
    obtain ⟨z, d, hv⟩ := hp (v, r) (by simp)
    have hv' : v = Var.point z d := hv
    subst hv'
    refine ⟨fun w hw => ?_, Reading.gl.one⟩
    exact powersFrom_ne r (hr (Var.point z d, r) (by simp)) _ oneE
      (by show Reading.gl.val oneE ≠ 0; rw [Reading.gl.one]; exact one_ne_zero) w hw
  | (v, r) :: q :: rest, hp, hr => by
    obtain ⟨i1, i2⟩ := hidingAt_ne (q :: rest) (fun p h => hp p (List.mem_cons_of_mem _ h))
      (fun p h => hr p (List.mem_cons_of_mem _ h))
    obtain ⟨z, d, hv⟩ := hp (v, r) (by simp)
    have hv' : v = Var.point z d := hv
    subst hv'
    have hr0 : rd r ≠ 0 := hr (Var.point z d, r) (by simp)
    constructor
    · intro w hw
      have hw' : w ∈ powersFrom r ((Var.point z d).d - 1) (mulE (hidingAt (q :: rest)).2 r) ++
          (hidingAt (q :: rest)).1 := hw
      rcases List.mem_append.1 hw' with h | h
      · refine powersFrom_ne r hr0 _ _ ?_ w h
        show Reading.gl.val (mulE (hidingAt (q :: rest)).2 r) ≠ 0
        rw [Reading.gl.mul]
        have i2' : Reading.gl.val (hidingAt (q :: rest)).2 = 1 := i2
        rw [i2', one_mul]
        exact hr0
      · exact i1 w h
    · show Reading.gl.val (mulE (hidingAt (q :: rest)).2 (psiAt (Var.point z d) r)) = 1
      rw [Reading.gl.mul]
      have i2' : Reading.gl.val (hidingAt (q :: rest)).2 = 1 := i2
      rw [i2']
      show 1 * Reading.gl.val oneE = 1
      rw [Reading.gl.one, one_mul]

/-- At point variables the product of all psi is 1, whatever the challenges: the second half of
`hidingAt_ne`, by that proof's own lines for it. -/
theorem hidingAt_one : ∀ (l : List (Var × E)), AllPoint l → rd (hidingAt l).2 = 1
  | [], _ => Reading.gl.one
  | [(v, r)], hp => by
    obtain ⟨z, d, hv⟩ := hp (v, r) (by simp)
    have hv' : v = Var.point z d := hv
    subst hv'
    exact Reading.gl.one
  | (v, r) :: q :: rest, hp => by
    have i2 := hidingAt_one (q :: rest) (fun p h => hp p (List.mem_cons_of_mem _ h))
    obtain ⟨z, d, hv⟩ := hp (v, r) (by simp)
    have hv' : v = Var.point z d := hv
    subst hv'
    show Reading.gl.val (mulE (hidingAt (q :: rest)).2 (psiAt (Var.point z d) r)) = 1
    rw [Reading.gl.mul]
    have i2' : Reading.gl.val (hidingAt (q :: rest)).2 = 1 := i2
    rw [i2']
    show 1 * Reading.gl.val oneE = 1
    rw [Reading.gl.one, one_mul]

/-! ## A dot product against an indicator -/

theorem dotFrom_zero : ∀ (u : List E), dotFrom Reading.gl (fun _ => (0 : K)) u = 0
  | [] => rfl
  | x :: u => by
    show Reading.gl.val x * 0 + dotFrom Reading.gl (fun _ => (0 : K)) u = 0
    rw [dotFrom_zero u]
    ring

theorem dotFrom_unit : ∀ (u : List E) (i : Nat), i < u.length →
    dotFrom Reading.gl (fun k => if k = i then (1 : K) else 0) u = rd (u.getD i zeroE)
  | [], i, h => by simp at h
  | x :: u, 0, _ => by
    show Reading.gl.val x * (if (0 : Nat) = 0 then (1 : K) else 0) +
      dotFrom Reading.gl (fun k => if k + 1 = 0 then (1 : K) else 0) u = _
    have e : (fun k : Nat => if k + 1 = 0 then (1 : K) else 0) = fun _ => 0 := by
      funext k
      simp
    rw [e, dotFrom_zero]
    simp [rd]
  | x :: u, i + 1, h => by
    show Reading.gl.val x * (if (0 : Nat) = i + 1 then (1 : K) else 0) +
      dotFrom Reading.gl (fun k => if k + 1 = i + 1 then (1 : K) else 0) u = _
    have e : (fun k : Nat => if k + 1 = i + 1 then (1 : K) else 0) =
        fun k => if k = i then (1 : K) else 0 := by
      funext k
      simp
    rw [e, dotFrom_unit u i (by simpa using h)]
    simp

theorem dotFrom_off : ∀ (u : List E) (g : Nat → K), (∀ k, k < u.length → g k = 0) →
    dotFrom Reading.gl g u = 0
  | [], _, _ => rfl
  | x :: u, g, h => by
    show Reading.gl.val x * g 0 + dotFrom Reading.gl (fun k => g (k + 1)) u = 0
    rw [h 0 (by simp), dotFrom_off u (fun k => g (k + 1)) fun k hk => h (k + 1) (by simpa using hk)]
    ring

/-! ## The one form that a masked sumcheck leaves -/

/-- The coefficient of the form on any slot. -/
theorem delta_rowForm (h : Heard) (S0 : E) (j : Nat) :
    delta j (rowForm h S0 {}) =
      dotFrom Reading.gl (fun i => if h.first + i = j then (1 : K) else 0)
        (hidingAt (h.vars.zip h.r)).1 -
      rd h.eps * rd (hidingAt (h.vars.zip h.r)).2 * delta j h.start := by
  unfold delta val
  rw [VerifiableInference.Desc.Part.MaskedSum.rowForm_value,
    VerifiableInference.Desc.Part.MaskedSum.rowForm_value]
  have e0 : dotFrom Reading.gl (fun i => (nought K).slot (h.first + i))
      (hidingAt (h.vars.zip h.r)).1 = 0 := dotFrom_zero _
  have e1 : (fun i => (unitAt K j).slot (h.first + i)) =
      fun i => if h.first + i = j then (1 : K) else 0 := rfl
  have e2 : ∀ W : World K, Aff.value Reading.gl W ({} : Aff) = 0 := fun W => by
    simp [Aff.value, Reading.gl.zero]
  rw [e0, e1, e2, e2]
  unfold rd
  ring

/-- **ITS OWN SLOTS.** At point variables, with no challenge 0, where the start form does not name
the slot: the coefficient on own slot number i is other than 0. -/
theorem delta_own (h : Heard) (S0 : E) (hp : AllPoint (h.vars.zip h.r))
    (hr : ∀ p ∈ h.vars.zip h.r, rd p.2 ≠ 0) (i : Nat)
    (hi : i < (hidingAt (h.vars.zip h.r)).1.length)
    (hs : ∀ x, x ∈ h.start.slots.toList → x.1 ≠ h.first + i) :
    delta (h.first + i) (rowForm h S0 {}) ≠ 0 := by
  rw [delta_rowForm, delta_unnamed _ _ hs, mul_zero, sub_zero]
  have e : (fun k => if h.first + k = h.first + i then (1 : K) else 0) =
      fun k => if k = i then (1 : K) else 0 := by
    funext k
    simp
  rw [e, dotFrom_unit _ i hi]
  refine (hidingAt_ne _ hp hr).1 _ ?_
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **THE CLAIMED SUM's SLOT**, in front of the own slots: the coefficient is other than 0 where the
element sampled at the beginning is (it is minus that element). The premise on the challenges (hr)
is asked too; the proof needs it only because it calls `hidingAt_ne` whole: `delta_lead'` has the
same end without it. -/
theorem delta_lead (h : Heard) (S0 : E) (hp : AllPoint (h.vars.zip h.r))
    (hr : ∀ p ∈ h.vars.zip h.r, rd p.2 ≠ 0) (c : Nat) (hc : c < h.first)
    (hs : h.start = Aff.slot c) (he : rd h.eps ≠ 0) :
    delta c (rowForm h S0 {}) ≠ 0 := by
  rw [delta_rowForm, hs, delta_slot, if_pos rfl, (hidingAt_ne _ hp hr).2,
    dotFrom_off _ _ fun k _ => if_neg (by omega)]
  simpa using he

/-- `delta_lead` without its premise on the challenges. -/
theorem delta_lead' (h : Heard) (S0 : E) (hp : AllPoint (h.vars.zip h.r)) (c : Nat)
    (hc : c < h.first) (hs : h.start = Aff.slot c) (he : rd h.eps ≠ 0) :
    delta c (rowForm h S0 {}) ≠ 0 := by
  rw [delta_rowForm, hs, delta_slot, if_pos rfl, hidingAt_one _ hp,
    dotFrom_off _ _ fun k _ => if_neg (by omega)]
  simpa using he

end

section
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (asClaim)
open VerifiableInference.Desc.Kinds.Head.Law (K rd SlotsIn callOf heardRec)
open VerifiableInference.Desc.Kinds.Head.Law.Came (val)
open VerifiableInference.Desc.K9H (liveAt)
open VerifiableInference.Desc.Part.MaskedSum (Var Heard hidingAt rowForm)

theorem delta_sm (j k : Nat) (f : Form) :
    delta j (OnBytes.Desc.First.P6.sm k f) = (k : K) * delta j f := by
  unfold delta val
  rw [OnBytes.Desc.First.P6.sm_value, OnBytes.Desc.First.P6.sm_value]
  ring

theorem delta_slotsIn {lo hi : Nat} {f : Form} (h : SlotsIn lo hi f) (j : Nat)
    (hj : j < lo ∨ hi ≤ j) : delta j f = 0 :=
  delta_unnamed j f fun x hx => by
    have := h x hx
    omega

theorem delta_bare (j : Nat) (f : Form) (h : f.slots = #[]) : delta j f = 0 :=
  delta_unnamed j f fun x hx => by
    rw [h] at hx
    simp at hx

/-! ## A masked sumcheck as the part hands it back -/

theorem allPoint_callOf (lead : Nat) (z : Point) (e : Nat) (r : List E) :
    AllPoint ((callOf lead z e).all.zip r) := by
  intro p hp
  have h1 : p.1 ∈ (callOf lead z e).all := (List.of_mem_zip (a := p.1) (b := p.2) hp).1
  have h2 : p.1 ∈ z.toList.map (Var.point · 3) ++ [Var.point zeroE (2 + 1)] := h1
  rcases List.mem_append.1 h2 with h | h
  · obtain ⟨x, _, hx⟩ := List.mem_map.1 h
    exact ⟨x, 3, hx.symm⟩
  · exact ⟨zeroE, 2 + 1, by simpa using h⟩

theorem left_eq {S : Sum} {hd : Heard} (h : S.psc = some hd) (S0 : E) :
    S.left S0 = rowForm hd S0 {} := by
  unfold Sum.left
  rw [h]
  rfl

/-- The own slots of a sumcheck whose form stands in the list are live. -/
theorem live_own {fs : List Form} {S : Sum} {S0 : E} (hmem : S.left S0 ∈ fs) {C : Form} {T : E}
    {R : VerifiableInference.Desc.Part.MaskedSum.Read} {lead : Nat} {z : Point} {e first : Nat}
    {t : List Fmt.RoundView}
    (hR : VerifiableInference.Desc.Part.MaskedSum.readAll (callOf lead z e) t = some R)
    (hpsc : S.psc = some (heardRec C T R (callOf lead z e) first))
    (hr : ∀ x ∈ R.rounds.map (·.2), rd x ≠ 0) (hC : ∀ x, x ∈ C.slots.toList → x.1 < first) :
    ∀ j, first ≤ j → j < first + (2 * z.size + 3) → liveAt (fs.map asClaim) j = true := by
  intro j j1 j2
  obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by omega⟩
  refine live_of_delta hmem ?_
  rw [left_eq hpsc]
  have hlen := Head.Law.own_length lead z e hR
  rw [Head.Law.own_callOf] at hlen
  exact delta_own (heardRec C T R (callOf lead z e) first) S0 (allPoint_callOf lead z e _)
    (fun p hp => hr p.2 (List.of_mem_zip (a := p.1) (b := p.2) hp).2) i
    (by
      show i < (hidingAt ((callOf lead z e).all.zip (R.rounds.map (·.2)))).1.length
      rw [hlen]
      omega)
    (fun x hx => by
      have := hC x hx
      show x.1 ≠ first + i
      omega)

/-- The claimed sum's slot is live where the element sampled at the beginning is not 0. The premise
on the challenges (hr) is asked too, and is not needed: `live_lead'` has the same end without it. -/
theorem live_lead {fs : List Form} {S : Sum} {S0 : E} (hmem : S.left S0 ∈ fs) {T : E}
    {R : VerifiableInference.Desc.Part.MaskedSum.Read} {lead : Nat} {z : Point} {e first c : Nat}
    (hpsc : S.psc = some (heardRec (Aff.slot c) T R (callOf lead z e) first))
    (hr : ∀ x ∈ R.rounds.map (·.2), rd x ≠ 0) (hc : c < first) (he : rd R.eps ≠ 0) :
    liveAt (fs.map asClaim) c = true := by
  refine live_of_delta hmem ?_
  rw [left_eq hpsc]
  exact delta_lead (heardRec (Aff.slot c) T R (callOf lead z e) first) S0
    (allPoint_callOf lead z e _)
    (fun p hp => hr p.2 (List.of_mem_zip (a := p.1) (b := p.2) hp).2) c hc rfl he

/-- `live_lead` without its premise on the challenges. -/
theorem live_lead' {fs : List Form} {S : Sum} {S0 : E} (hmem : S.left S0 ∈ fs) {T : E}
    {R : VerifiableInference.Desc.Part.MaskedSum.Read} {lead : Nat} {z : Point} {e first c : Nat}
    (hpsc : S.psc = some (heardRec (Aff.slot c) T R (callOf lead z e) first))
    (hc : c < first) (he : rd R.eps ≠ 0) :
    liveAt (fs.map asClaim) c = true := by
  refine live_of_delta hmem ?_
  rw [left_eq hpsc]
  exact delta_lead' (heardRec (Aff.slot c) T R (callOf lead z e) first) S0
    (allPoint_callOf lead z e _) c hc rfl he

/-- A form "the variable under slot a, less a form that does not name it" makes slot a live. -/
theorem live_var {fs : List Form} {v g : Form} (hmem : v - g ∈ fs) {a : Nat} (hv : v = Aff.slot a)
    (hg : delta a g = 0) : liveAt (fs.map asClaim) a = true := by
  refine live_of_delta hmem ?_
  rw [delta_sub, hv, delta_slot, if_pos rfl, hg]
  simp

end

#print axioms slotCoef_asClaim
#print axioms live_of_delta
#print axioms delta_add
#print axioms delta_sub
#print axioms delta_slot
#print axioms kept_delta
#print axioms delta_unnamed
#print axioms powersFrom_ne
#print axioms hidingAt_ne
#print axioms hidingAt_one
#print axioms dotFrom_zero
#print axioms dotFrom_unit
#print axioms dotFrom_off
#print axioms delta_rowForm
#print axioms delta_own
#print axioms delta_lead
#print axioms delta_lead'
#print axioms delta_sm
#print axioms delta_slotsIn
#print axioms delta_bare
#print axioms allPoint_callOf
#print axioms left_eq
#print axioms live_own
#print axioms live_lead
#print axioms live_lead'
#print axioms live_var

end ProofFile.Honest.K6.GoodLaw
