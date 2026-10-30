-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Coef.lean: with which coefficient a form names a slot, read in
the library's field: the rules by which it is reckoned, and the coefficients of the row that a
masked sumcheck leaves. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there form, slot, row, sumcheck, read, world and worth. In this
file: the coefficient is that of Johnson/Desc/K9/Honest/SlotsFew.lean (`slotCoef`), at a form. It is
the form's value in the world in which slot j is worth 1 and all else 0, less its value in the world
in which all is 0; so the library's rules on values (OnBytes/Model/HideLaws.lean) give the rules on
coefficients. The hiding polynomial of a masked sumcheck is the library's term; its weights are what
`hidingAt` (Johnson/Desc/Part/MaskedSum4.lean) returns.

What is shown.
  `vl`, `sc`, `sc_eq`: the reading; the coefficient; the coefficient as a difference of two values.
  `sc_ofConst`, `sc_empty`, `sc_slot`, `sc_addMul`, `sc_scale`, `sc_add`, `sc_sub`, `sc_out`: a
    constant, the empty form, a slot, a + k b, k a, a + b, a - b; a slot that the form does not
    name.
  `dot_unit`, `dot_nought`: a list of coefficients set on slots in a row.
  `rowAff_value`, `sc_rowAff`: the row of a masked sumcheck (`rowAff`,
    Johnson/Desc/Part/MaskedSumTie.lean): on slot j, the hiding polynomial's weight where j is one
    of the sumcheck's own slots, less eps times the product of all psi times the start form's
    coefficient.
  `powers_ne`, `hiding_pt`, `hiding_one`: where all variables are summed at a point, that product is
    1; and where no challenge is 0, no weight is 0.
  `front_coef`: on a slot in front: minus eps times the start form's coefficient, whatever the
    challenges.
  `record_coef`, `whole_coef`: the same of a structure that `hear` returns, at any end term; of what
    `whole` returns.
  `live_iff`: the test `liveIn` of Honest/K3/GoodDraws.lean, in these words.
Helpers: `GE`, `Pt`, `vl_one`, `all_pt`. Second names. `vl` is the text of `rd`
(Honest/K3/Law/Statements.lean): both are `Reading.gl.val`. `GE` is the text of the library's
`OnBytes.Slice.GE` (OnBytes/Slice/Draws.lean): both are `Cb.Gl.E`. `Pt v` says as a proposition what
the library's test `Var.isPoint` (Johnson/Top/H/P1Tie/Words.lean) says with code; the tie:
`pt_iff_isPoint` (Honest/K3/Law/TiesSealedForms.lean [not in this library]).

Hypotheses that remain, in `record_coef` and `whole_coef`.
  `hh`, `hw`: the masked sumcheck's hearing returns (`MaskedSum.hear`, `MaskedSum.whole`).
  `hC`: the start form names slots between lo and the ledger's next slot alone.
  `hp`: each variable of the call is summed at a point (`Pt`).
  `hr`: no challenge reads as 0.
In `front_coef`: `hh`, `hp`, and `hj`: the slot lies in front of the ledger's next slot. In
`sc_out`: `h`, `hj`: the form names slots from lo to hi alone; j lies outside. In `powers_ne`: `hr`:
vl r ≠ 0, and a hypothesis without a name: vl a ≠ 0. In `all_pt`: `hp`.

Users. Honest/K3/Good/Step.lean imports this file.

Limits. Rules on forms. Nothing here goes through the lookup's course.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesOwn
import Johnson.Desc.Part.MaskedSumRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff Reading World Ent slotValue)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum
    (Var Call Heard hidingAt powersFrom psiAt ownSlots rowAff dotFrom
  onSlots_value)
open VerifiableInference.Desc.K9H (slotCoef unitAt nought liveAt_iff)
open ProofFile.Honest.K3.Parts (In)

abbrev GE : Type := Cb.Gl.E

/-- An element of the program, read in the library's field. -/
def vl (x : E) : GE := Reading.gl.val x

/-- **The coefficient with which a form names slot j.** -/
def sc (a : Aff) (j : Nat) : GE := slotCoef Reading.gl ({ form := a } : Claim) j

/-- It is the form's value where slot j is worth 1 and all else 0, less its value where all is 0. -/
theorem sc_eq (a : Aff) (j : Nat) :
    sc a j = a.value Reading.gl (unitAt GE j) - a.value Reading.gl (nought GE) := by
  have e1 : ∀ (W : World GE), (∀ t r i, W.entry t r i = 0) →
      (a.ents.toList.map (Ent.value Reading.gl W)).sum = 0 := by
    intro W hW
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
    simp [Ent.value, hW]
  have e2 : (a.slots.toList.map (slotValue Reading.gl (nought GE))).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
    simp [slotValue, nought]
  show (a.slots.toList.map (slotValue Reading.gl (unitAt GE j))).sum = _
  unfold Aff.value
  rw [e1 _ (fun _ _ _ => rfl), e1 _ (fun _ _ _ => rfl), e2]
  ring

theorem sc_ofConst (v : E) (j : Nat) : sc (Aff.ofConst v) j = 0 := by
  rw [sc_eq, Aff.value_ofConst, Aff.value_ofConst]
  ring

theorem sc_empty (j : Nat) : sc {} j = 0 := by
  rw [sc_eq, Aff.value_empty, Aff.value_empty]
  ring

theorem sc_slot (i j : Nat) : sc (Aff.slot i) j = if i = j then 1 else 0 := by
  rw [sc_eq, Aff.value_slot, Aff.value_slot]
  simp [unitAt, nought]

theorem sc_addMul (a b : Aff) (k : E) (j : Nat) : sc (Aff.addMul a b k) j = sc a j + vl k * sc b j
    := by
  rw [sc_eq, sc_eq, sc_eq, Aff.value_addMul, Aff.value_addMul]
  unfold vl
  ring

theorem sc_scale (a : Aff) (k : E) (j : Nat) : sc (Aff.scale a k) j = vl k * sc a j := by
  rw [sc_eq, sc_eq, Aff.value_scale, Aff.value_scale]
  unfold vl
  ring

theorem sc_add (a b : Aff) (j : Nat) : sc (a + b) j = sc a j + sc b j := by
  rw [sc_eq, sc_eq, sc_eq, Aff.value_add, Aff.value_add]
  ring

theorem sc_sub (a b : Aff) (j : Nat) : sc (a - b) j = sc a j - sc b j := by
  rw [sc_eq, sc_eq, sc_eq, Aff.value_sub, Aff.value_sub]
  ring

/-- A form that names slots between lo and hi alone names no slot outside. -/
theorem sc_out {lo hi : Nat} {a : Aff} (h : In lo hi a) {j : Nat} (hj : j < lo ∨ hi ≤ j) : sc a j =
    0 := by
  show (a.slots.toList.map (slotValue Reading.gl (unitAt GE j))).sum = 0
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hne : x.1 ≠ j := by
    have := h x hx
    omega
  simp [slotValue, unitAt, hne]

/-! ## Coefficients set on slots in a row -/

theorem dot_nought : ∀ (u : List E) (first : Nat),
    dotFrom Reading.gl (fun i => (nought GE).slot (first + i)) u = 0
  | [], _ => rfl
  | x :: u, first => by
    have hf : (fun i => (nought GE).slot (first + (i + 1))) = fun i => (nought GE).slot
      (first + 1 + i) :=
      rfl
    show Reading.gl.val x * (nought GE).slot (first + 0) +
      dotFrom Reading.gl (fun i => (nought GE).slot (first + (i + 1))) u = 0
    rw [hf, dot_nought u (first + 1)]
    simp [nought]

theorem dot_unit (j : Nat) : ∀ (u : List E) (first : Nat),
    dotFrom Reading.gl (fun i => (unitAt GE j).slot (first + i)) u =
      if first ≤ j ∧ j < first + u.length then vl (u.getD (j - first) zeroE) else 0
  | [], first => by
    have c : ¬ (first ≤ j ∧ j < first + ([] : List E).length) := by
      simp only [List.length_nil]
      omega
    rw [if_neg c]
    rfl
  | x :: u, first => by
    have hf : (fun i => (unitAt GE j).slot (first + (i + 1))) =
        fun i => (unitAt GE j).slot (first + 1 + i) := by
      funext i
      congr 1
      omega
    show Reading.gl.val x * (unitAt GE j).slot (first + 0) +
      dotFrom Reading.gl (fun i => (unitAt GE j).slot (first + (i + 1))) u = _
    rw [hf, dot_unit j u (first + 1)]
    by_cases h0 : first = j
    · subst h0
      have c1 : ¬ (first + 1 ≤ first ∧ first < first + 1 + u.length) := by omega
      have c2 : first ≤ first ∧ first < first + (x :: u).length := by
        simp only [List.length_cons]
        omega
      have e : (unitAt GE first).slot (first + 0) = 1 := by simp [unitAt]
      rw [if_neg c1, if_pos c2, e, Nat.sub_self]
      simp [vl]
    · have e : (unitAt GE j).slot (first + 0) = 0 := by simp [unitAt, h0]
      rw [e]
      by_cases c : first + 1 ≤ j ∧ j < first + 1 + u.length
      · have c2 : first ≤ j ∧ j < first + (x :: u).length := by
          simp only [List.length_cons]
          omega
        have e2 : j - first = (j - (first + 1)) + 1 := by omega
        rw [if_pos c, if_pos c2, e2, List.getD_cons_succ]
        ring
      · have c2 : ¬ (first ≤ j ∧ j < first + (x :: u).length) := by
          simp only [List.length_cons]
          omega
        rw [if_neg c, if_neg c2]
        ring

/-! ## The row of a masked sumcheck -/

theorem rowAff_value (W : World GE) (h : Heard) (S0 : E) (kept : Aff) :
    (rowAff h S0 kept).value Reading.gl W =
      dotFrom Reading.gl (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 +
        Reading.gl.val h.eps * Reading.gl.val (hidingAt (h.vars.zip h.r)).2 *
          (Reading.gl.val h.target - h.start.value Reading.gl W) +
        Reading.gl.val h.eps * kept.value Reading.gl W -
        (Reading.gl.val h.claim - Reading.gl.val h.eps * Reading.gl.val S0) := by
  unfold rowAff
  simp only [Aff.value_addMul, onSlots_value, Aff.value_sub, Aff.value_ofConst, Reading.gl.sub,
    Reading.gl.mul, Reading.gl.zero]
  ring

/-- **The coefficients of a masked sumcheck's row**, no term kept. -/
theorem sc_rowAff (h : Heard) (S0 : E) (j : Nat) :
    sc (rowAff h S0 {}) j =
      (if h.first ≤ j ∧ j < h.first + (hidingAt (h.vars.zip h.r)).1.length then
        vl ((hidingAt (h.vars.zip h.r)).1.getD (j - h.first) zeroE) else 0) -
        vl h.eps * vl (hidingAt (h.vars.zip h.r)).2 * sc h.start j := by
  rw [sc_eq, rowAff_value, rowAff_value, dot_unit, dot_nought, sc_eq, Aff.value_empty,
    Aff.value_empty]
  unfold vl
  ring

/-! ## All variables summed at a point -/

/-- The variable is summed at a point. -/
def Pt (v : Var) : Prop := ∃ z d, v = Var.point z d

theorem powers_ne {r : E} (hr : vl r ≠ 0) : ∀ (n : Nat) (a : E), vl a ≠ 0 →
    ∀ y ∈ powersFrom r n a, vl y ≠ 0
  | 0, _, _, y, hy => by simp [powersFrom] at hy
  | n + 1, a, ha, y, hy => by
    have hy' : y ∈ a :: powersFrom r n (mulE a r) := hy
    rcases List.mem_cons.1 hy' with h1 | h1
    · rw [h1]
      exact ha
    · refine powers_ne hr n (mulE a r) ?_ y h1
      show Reading.gl.val (mulE a r) ≠ 0
      rw [Reading.gl.mul]
      exact mul_ne_zero ha hr

theorem vl_one : vl oneE = 1 := Reading.gl.one

/-- **Where all variables are summed at a point and no challenge is 0**: the product of all psi is
1, and no weight of the hiding polynomial's coefficients is 0. -/
theorem hiding_pt : ∀ (l : List (Var × E)), (∀ x ∈ l, Pt x.1) → (∀ x ∈ l, vl x.2 ≠ 0) →
    vl (hidingAt l).2 = 1 ∧ ∀ y ∈ (hidingAt l).1, vl y ≠ 0
  | [], _, _ => ⟨vl_one, fun y hy => by simp [hidingAt] at hy⟩
  | [(v, r)], hp, hr => by
    obtain ⟨z, d, rfl⟩ := hp (v, r) (by simp)
    have hr' : vl r ≠ 0 := hr (Var.point z d, r) (by simp)
    refine ⟨vl_one, fun y hy => ?_⟩
    have hy' : y ∈ powersFrom r d oneE := hy
    exact powers_ne hr' d oneE (by rw [vl_one]; exact one_ne_zero) y hy'
  | (v, r) :: x2 :: rest, hp, hr => by
    obtain ⟨z, d, rfl⟩ := hp (v, r) (by simp)
    have hr' : vl r ≠ 0 := hr (Var.point z d, r) (by simp)
    obtain ⟨i1, i2⟩ := hiding_pt (x2 :: rest) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    have e : hidingAt ((Var.point z d, r) :: x2 :: rest) =
        (powersFrom r (d - 1) (mulE (hidingAt (x2 :: rest)).2 r) ++ (hidingAt (x2 :: rest)).1,
          mulE (hidingAt (x2 :: rest)).2 oneE) := rfl
    rw [e]
    refine ⟨?_, fun y hy => ?_⟩
    · show Reading.gl.val (mulE _ oneE) = 1
      rw [Reading.gl.mul, Reading.gl.one, mul_one]
      exact i1
    · rcases List.mem_append.1 hy with h1 | h1
      · refine powers_ne hr' _ _ ?_ y h1
        show Reading.gl.val (mulE _ r) ≠ 0
        rw [Reading.gl.mul]
        have i1' : Reading.gl.val (hidingAt (x2 :: rest)).2 = 1 := i1
        rw [i1', one_mul]
        exact hr'
      · exact i2 y h1

/-- Where all variables are summed at a point the product of all psi is 1,
whatever the challenges. -/
theorem hiding_one : ∀ (l : List (Var × E)), (∀ x ∈ l, Pt x.1) → vl (hidingAt l).2 = 1
  | [], _ => vl_one
  | [(v, r)], hp => by
    obtain ⟨z, d, rfl⟩ := hp (v, r) (by simp)
    exact vl_one
  | (v, r) :: x2 :: rest, hp => by
    obtain ⟨z, d, rfl⟩ := hp (v, r) (by simp)
    have i1 := hiding_one (x2 :: rest) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    show Reading.gl.val (mulE (hidingAt (x2 :: rest)).2 oneE) = 1
    rw [Reading.gl.mul, Reading.gl.one, mul_one]
    exact i1

/-- All variables of a call are summed at a point, Y among them. -/
theorem all_pt {k : Call} (hp : ∀ v ∈ k.vs, Pt v) : ∀ v ∈ k.all, Pt v := by
  intro v hv
  unfold Call.all at hv
  cases he : k.ends with
  | none =>
    rw [he] at hv
    exact hp v hv
  | some e =>
    rw [he] at hv
    rcases List.mem_append.1 hv with h1 | h1
    · exact hp v h1
    · exact ⟨zeroE, e.dY + 1, by simpa using h1⟩

/-- On a slot in front of the sumcheck's own the row's coefficient is minus eps times the start
form's, whatever the challenges. -/
theorem front_coef {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : MaskedSum.hear C k F rs = some (h, G)) (hp : ∀ v ∈ k.vs, Pt v) (S0 : E) (j : Nat)
    (hj : j < F.next) : sc (rowAff h S0 {}) j = - (vl h.eps * sc C j) := by
  obtain ⟨a1, _, _⟩ := MaskedSum.heard_lenK hh
  obtain ⟨_, T, R, _, _, he, _⟩ := MaskedSum.hear_spec hh
  have hv : h.vars = k.all := by rw [he]
  have hs : h.start = C := by rw [he]
  have p1 := hiding_one (h.vars.zip h.r)
    (fun x hx => all_pt hp x.1 (by rw [← hv]; exact (List.of_mem_zip hx).1))
  have c : ¬ (h.first ≤ j ∧ j < h.first + (hidingAt (h.vars.zip h.r)).1.length) := by
    rw [a1]
    omega
  rw [sc_rowAff, if_neg c, p1, hs]
  ring

/-- **The coefficients of the row of a structure that the hearing makes**: all variables summed at a
point, no challenge 0, the start form on slots in front of the sumcheck's own: none of the own
slots' coefficients is 0; on a slot in front the coefficient is minus eps times the start form's. -/
theorem record_coef {lo : Nat} {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : MaskedSum.hear C k F rs = some (h, G)) (hC : In lo F.next C) (hp : ∀ v ∈ k.vs, Pt v)
    (hr : ∀ x ∈ h.r, vl x ≠ 0) (S0 : E) :
    (∀ j, F.next ≤ j → j < F.next + ownSlots k.all → sc (rowAff h S0 {}) j ≠ 0) ∧
      ∀ j, j < F.next → sc (rowAff h S0 {}) j = - (vl h.eps * sc C j) := by
  obtain ⟨a1, _, a3⟩ := MaskedSum.heard_lenK hh
  obtain ⟨_, T, R, _, _, he, _⟩ := MaskedSum.hear_spec hh
  have hv : h.vars = k.all := by rw [he]
  have hs : h.start = C := by rw [he]
  obtain ⟨p1, p2⟩ := hiding_pt (h.vars.zip h.r)
    (fun x hx => all_pt hp x.1 (by rw [← hv]; exact (List.of_mem_zip hx).1))
    (fun x hx => hr x.2 (List.of_mem_zip hx).2)
  refine ⟨fun j j1 j2 => ?_, fun j j1 => ?_⟩
  · rw [sc_rowAff, a1, a3, if_pos ⟨j1, j2⟩, hs, sc_out hC (Or.inr j1), mul_zero, sub_zero]
    apply p2
    have hlt : j - F.next < (hidingAt (h.vars.zip h.r)).1.length := by
      rw [a3]
      omega
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  · have c : ¬ (F.next ≤ j ∧ j < F.next + ownSlots k.all) := by omega
    rw [sc_rowAff, a1, a3, if_neg c, p1, hs]
    ring

/-- The same of what `whole` returns. -/
theorem whole_coef {lo : Nat} {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G))
    (hC : In lo F.next C) (hp : ∀ v ∈ k.vs, Pt v) (hr : ∀ x ∈ h.r, vl x ≠ 0) :
    (∀ j, F.next ≤ j → j < F.next + ownSlots k.all → sc f j ≠ 0) ∧
      ∀ j, j < F.next → sc f j = - (vl h.eps * sc C j) := by
  obtain ⟨_, G1, sh, _, hh, _, hrow⟩ := MaskedSum.whole_parts hw
  rw [MaskedSum.row_spec hrow]
  exact record_coef hh hC hp hr _

/-! ## The test on forms, in these words -/

theorem live_iff (l : List Aff) (j : Nat) : liveIn l j = true ↔ ∃ a ∈ l, sc a j ≠ 0 := by
  rw [liveIn_eq, liveAt_iff]
  constructor
  · rintro ⟨cl, hcl, _, hne⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hcl
    exact ⟨a, ha, hne⟩
  · rintro ⟨a, ha, hne⟩
    exact ⟨{ form := a }, List.mem_map.2 ⟨a, ha, rfl⟩, rfl, hne⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.sc_eq
#print axioms ProofFile.Honest.K3.Good.sc_ofConst
#print axioms ProofFile.Honest.K3.Good.sc_empty
#print axioms ProofFile.Honest.K3.Good.sc_slot
#print axioms ProofFile.Honest.K3.Good.sc_addMul
#print axioms ProofFile.Honest.K3.Good.sc_scale
#print axioms ProofFile.Honest.K3.Good.sc_add
#print axioms ProofFile.Honest.K3.Good.sc_sub
#print axioms ProofFile.Honest.K3.Good.sc_out
#print axioms ProofFile.Honest.K3.Good.dot_nought
#print axioms ProofFile.Honest.K3.Good.dot_unit
#print axioms ProofFile.Honest.K3.Good.rowAff_value
#print axioms ProofFile.Honest.K3.Good.sc_rowAff
#print axioms ProofFile.Honest.K3.Good.powers_ne
#print axioms ProofFile.Honest.K3.Good.vl_one
#print axioms ProofFile.Honest.K3.Good.hiding_pt
#print axioms ProofFile.Honest.K3.Good.hiding_one
#print axioms ProofFile.Honest.K3.Good.all_pt
#print axioms ProofFile.Honest.K3.Good.front_coef
#print axioms ProofFile.Honest.K3.Good.record_coef
#print axioms ProofFile.Honest.K3.Good.whole_coef
#print axioms ProofFile.Honest.K3.Good.live_iff
