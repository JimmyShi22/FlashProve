-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Coef.lean: THE COEFFICIENT WITH WHICH A FORM NAMES A SLOT,
AS A DIFFERENCE OF TWO VALUES; AND WHEN NO COEFFICIENT OF A MASKED SUMCHECK's HIDING WINDOW IS 0.

What is here. A KIT ON THE VERIFIER's FORMS: no prover is in it, and no sub-protocol. `cf ρ f j` is
the library's `slotCoef` (Johnson/Desc/K9/Honest/SlotsFew.lean) at the plain claim of the form f:
the sum of f's coefficients on slot j, read in a ring. `cf_eq`: it is f's value in the world where
slot j holds 1 and all else 0, less f's value in the world where all is 0. So the library's laws on
values (OnBytes/Model/HideLaws.lean) carry over to coefficients: sums, differences, multiples, and
the claim that a masked sumcheck leaves (`Psc.rowForm`). There, with P the product over the
variables of psi at the challenge (OnBytes/Model/Psc.lean), the coefficient on slot j is the hiding
walk's word at j - first (0 outside the window), less eps P times the start form's coefficient, plus
eps times the kept form's. Definitions, statements and proofs.

  `cf`, `cf_eq`: the coefficient; as a difference of values.
  `cf_ofConst`, `cf_slot_self`, `cf_slot_ne`, `cf_empty`, `cf_addMul`, `cf_add`, `cf_sub`,
      `cf_scale`, `cf_of_slotsIn`: the kit (`sum_zero_of`, `sumFrom_nought`: two sums that are 0).
  `cf_rowForm`, `cf_rowForm_in`, `cf_rowForm_out`: a sumcheck's own claim: at any slot; at a
      slot from its first on that its start and kept forms do not name; at a slot outside its
      window.
  `psi_plain`: psi at g reads as g under the plain weight. That it reads as 1 under an equality
      weight is the library's `OnBytes.PscTie.psi_equality` (OnBytes/Tie/Pv/Psc/FlatTie.lean).
  `powersLoop_ne`, `powers_ne`, `walk_ne`: in a ring with 1 ≠ 0 and without zero divisors no
      word of the hiding walk reads as 0, nor does P, where each variable's challenge and its psi at
      that challenge read as not 0.
  `live_of_cf`: a form of a list with a coefficient on j that is not 0 makes j live (`liveAt`,
      Johnson/Desc/K9/Honest/SlotsLive.lean) in the list as plain claims.

Kin. THE SAME RULES STAND IN FIVE MORE FILES OF THE LIBRARY THAT THIS FILE's WRITERS KNOW OF, IN
OTHER LETTERS. (1) Honest/K3/Good/Coef.lean, for the kind "lookup": `sc` a j is `slotCoef` at the
library's field at the plain claim of a: by the two definitions' texts that is `cf` at that reading.
Its `sc_eq`, `sc_ofConst`, `sc_empty`, `sc_addMul`, `sc_scale`, `sc_add`, `sc_sub` are, at that one
reading, the sentences of `cf_eq`, `cf_ofConst`, `cf_empty`, `cf_addMul`, `cf_scale`, `cf_add`,
`cf_sub`; its `sc_slot` holds `cf_slot_self` and `cf_slot_ne` in one. Of a like end under another
premise: `sc_out` (a form whose slots lie in an interval) beside `cf_of_slotsIn`; `powers_ne` and
`hiding_pt` beside `powers_ne` and `walk_ne`; `sc_rowAff`, and `sc_rowForm`
(Honest/K3/Good/Live/Forms.lean), beside `cf_rowForm`; `live_iff`, and `live_of_form` (Forms.lean),
beside `live_of_cf`. (2) Honest/K6/GoodLaw/Coef.lean, on the output head's claims: `delta`, the
difference of the two values itself, tied to `slotCoef` by `slotCoef_asClaim`: `delta_add`,
`delta_sub`, `delta_slot`, `delta_unnamed` (beside `cf_of_slotsIn`), `delta_slotsIn`, `delta_bare`,
`powersFrom_ne`, `hidingAt_ne`, `delta_rowForm`, `live_of_delta`. (3)
Johnson/Desc/K5/Honest/Law/Live.lean, for an attention segment: `slotCo` ρ f j, AT A FREE READING AS
HERE: by the definitions' texts it is `cf` ρ f j. Its `slotCo_value`, `slotCo_ofConst`,
`slotCo_empty`, `slotCo_addMul`, `slotCo_scale`, `slotCo_add`, `slotCo_sub` are the sentences of
`cf_eq`, `cf_ofConst`, `cf_empty`, `cf_addMul`, `cf_scale`, `cf_add`, `cf_sub`; `slotCo_slot` holds
`cf_slot_self` and `cf_slot_ne` in one. Of a like end: `slotCo_formOf`, `powersFrom_ne`,
`hidingAt_ne` (in a field; plain variables and variables at a point). (4)
Johnson/Desc/K8/Honest/EqSlots.lean: at a free reading `coef_value` is `cf_eq` with `cf` unfolded
and `sum_nought` is `sumFrom_nought`; `value_unnamed` stands beside `cf_of_slotsIn`; `word_leaves`
is `cf_rowForm_in` at the library's field, at S0 = 1, nothing kept, inside the window; `live_leaves`
stands beside `live_of_cf`. (5) Johnson/Desc/K11/Live/Run.lean, for the head's merge: `coefAt` is by
its text `cf` at the library's field; `coef_addMul`, `coef_slot`; `coef_rowForm`,
`coef_rowForm_window`, `coef_rowForm_start` (nothing kept; a start form of one pair); `walk_all`,
`walk_at`: `walk_ne` at plain weights of three coefficients and one weight read at 0. WHAT PARTS:
the reading and its ring are free here, in (3) and in (4)'s kit; (1), (2), (5) have the library's
field alone. The sumcheck's state is the verifier program's `Psc` here, in (4) and in (5); (1), (2),
(3) have `MaskedSum.Heard` with `hidingAt`; the library ties the two (`powers_eq`, `psiAt_read`,
`hidingAt_read`, Johnson/Desc/Part/MaskedSumTie.lean). Here alone of the six, by its writers'
reading: any weight whose psi reads as not 0 at its challenge, and a ring without zero divisors in a
field's stead. In code no one of the six names another's coefficient. ON THE LIBRARY's GROUND:
`claimValue_sub` (Johnson/Desc/K9/Honest/SlotsFew.lean) has `cf_eq` at any claim; `sumFrom_zero`
there and `sumFrom_eq_zero` (OnBytes/Model/HideLaws.lean) hold `sumFrom_nought` as a case; the plain
arm of `psiAt_read` is `psi_plain` with the sides exchanged, behind the unfolding of `psiAt` and
`Var.weight`; another `powers_eq` and `hidingWalk_eq` (OnBytes/Tie/Pv/Psc/FlatTie.lean) say what
`powers` reads as, and what the walk reads as at equality weights. `sum_zero_of` is, at a free ring,
the sentence of the lemma of that name in Honest/K1/AnswersDot.lean [not in this library]; `walk_ne`
shares its short name with another statement (Johnson/Desc/K13/Law/RowMasks.lean).

Not shown here. A KIT: whatever a statement asks stands in the statement. That any challenge reads
as not 0. Which weights a sumcheck of the verifier's has. Nothing on entries. Nothing on what a form
is worth.
No property is claimed.
-/
import Johnson.Desc.K8.Honest.FallLayers
import Johnson.Desc.K9.Honest.SlotsJoin
import Johnson.Road.K4.Slots.SlotsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.Psc (Weight hidingWalk powers powersLoop polyAt)
open OnBytes.Desc.First.K4.Slots (SlotsIn)
open VerifiableInference.Desc.K9H (slotCoef unitAt nought liveAt liveAt_iff sumFrom_unit
  sumFrom_past slotCoef_unnamed unnamedIn)
open VerifiableInference.Desc.First

section ring
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The coefficient with which the form f names slot j: the sum over all its pairs on j. -/
def cf (f : Aff) (j : ℕ) : K := slotCoef ρ { form := f } j

/-- A sum of terms that are all 0. -/
theorem sum_zero_of {α : Type} (g : α → K) (l : List α) (h : ∀ x ∈ l, g x = 0) :
    (l.map g).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact h x hx

/-- **The coefficient is a difference of two values.** -/
theorem cf_eq (f : Aff) (j : ℕ) :
    cf ρ f j = f.value ρ (unitAt K j) - f.value ρ (nought K) := by
  have e1 : (f.ents.toList.map (Ent.value ρ (unitAt K j))).sum = 0 :=
    sum_zero_of _ _ fun x _ => by
      show ρ.val x.coef * (0 : K) = 0
      rw [mul_zero]
  have e2 : (f.ents.toList.map (Ent.value ρ (nought K))).sum = 0 :=
    sum_zero_of _ _ fun x _ => by
      show ρ.val x.coef * (0 : K) = 0
      rw [mul_zero]
  have e3 : (f.slots.toList.map (slotValue ρ (nought K))).sum = 0 :=
    sum_zero_of _ _ fun x _ => by
      show ρ.val x.2 * (0 : K) = 0
      rw [mul_zero]
  show (f.slots.toList.map (slotValue ρ (unitAt K j))).sum = _
  unfold Aff.value
  rw [e1, e2, e3]
  ring

theorem cf_ofConst (v : E) (j : ℕ) : cf ρ (Aff.ofConst v) j = 0 := by
  rw [cf_eq, Aff.value_ofConst, Aff.value_ofConst, sub_self]

theorem cf_empty (j : ℕ) : cf ρ ({} : Aff) j = 0 := by
  rw [cf_eq, Aff.value_empty, Aff.value_empty, sub_self]

theorem cf_slot_self (j : ℕ) : cf ρ (Aff.slot j) j = 1 := by
  rw [cf_eq, Aff.value_slot, Aff.value_slot]
  show (if j = j then (1 : K) else 0) - 0 = 1
  rw [if_pos rfl, sub_zero]

theorem cf_slot_ne {i j : ℕ} (h : i ≠ j) : cf ρ (Aff.slot i) j = 0 := by
  rw [cf_eq, Aff.value_slot, Aff.value_slot]
  show (if i = j then (1 : K) else 0) - 0 = 0
  rw [if_neg h, sub_zero]

theorem cf_addMul (a b : Aff) (k : E) (j : ℕ) :
    cf ρ (Aff.addMul a b k) j = cf ρ a j + ρ.val k * cf ρ b j := by
  rw [cf_eq, cf_eq, cf_eq, Aff.value_addMul, Aff.value_addMul]
  ring

theorem cf_add (a b : Aff) (j : ℕ) : cf ρ (a + b) j = cf ρ a j + cf ρ b j := by
  rw [cf_eq, cf_eq, cf_eq, Aff.value_add, Aff.value_add]
  ring

theorem cf_sub (a b : Aff) (j : ℕ) : cf ρ (a - b) j = cf ρ a j - cf ρ b j := by
  rw [cf_eq, cf_eq, cf_eq, Aff.value_sub, Aff.value_sub]
  ring

theorem cf_scale (a : Aff) (k : E) (j : ℕ) : cf ρ (Aff.scale a k) j = ρ.val k * cf ρ a j := by
  rw [cf_eq, cf_eq, Aff.value_scale, Aff.value_scale]
  ring

/-- A form that does not name slot j has the coefficient 0 there. -/
theorem cf_of_slotsIn {f : Aff} {j : ℕ} (h : SlotsIn (fun i => i ≠ j) f) : cf ρ f j = 0 := by
  refine slotCoef_unnamed ρ _ j ?_
  unfold unnamedIn
  rw [List.all_eq_true]
  intro x hx
  exact bne_iff_ne.2 (h x hx)

/-- In the world where all is 0 the weighted sum of the slots' values is 0. -/
theorem sumFrom_nought : ∀ (l : List E) (s : ℕ),
    sumFrom (fun i v => ρ.val v * (nought K).slot i) s l = 0
  | [], _ => rfl
  | v :: l, s => by
    show ρ.val v * (0 : K) + sumFrom (fun i v => ρ.val v * (nought K).slot i) (s + 1) l = 0
    rw [sumFrom_nought l (s + 1), mul_zero, add_zero]

/-- **The claim that a masked sumcheck leaves, at any slot.** -/
theorem cf_rowForm (p : Psc) (S0 : E) (kept : Aff) (j : ℕ) :
    cf ρ (p.rowForm S0 kept) j =
      sumFrom (fun i v => ρ.val v * (unitAt K j).slot i) p.first p.walk.1 -
        ρ.val p.eps * ρ.val p.walk.2 * cf ρ p.start j + ρ.val p.eps * cf ρ kept j := by
  rw [cf_eq, cf_eq ρ p.start, cf_eq ρ kept, Psc.rowForm_value, Psc.rowForm_value,
    sumFrom_nought]
  ring

/-- At a slot from the sumcheck's first on that neither the start form nor the kept form names: the
hiding walk's word (0 beyond the window). -/
theorem cf_rowForm_in (p : Psc) (S0 : E) {kept : Aff} {j : ℕ} (h1 : p.first ≤ j)
    (hs : SlotsIn (fun i => i ≠ j) p.start) (hk : SlotsIn (fun i => i ≠ j) kept) :
    cf ρ (p.rowForm S0 kept) j = ρ.val (p.walk.1.getD (j - p.first) zeroE) := by
  rw [cf_rowForm, sumFrom_unit ρ j p.walk.1 p.first h1, cf_of_slotsIn ρ hs, cf_of_slotsIn ρ hk]
  ring

/-- At a slot outside the window: what the start form and the kept form bring. -/
theorem cf_rowForm_out (p : Psc) (S0 : E) (kept : Aff) {j : ℕ}
    (h : j < p.first ∨ p.first + p.walk.1.length ≤ j) :
    cf ρ (p.rowForm S0 kept) j =
      ρ.val p.eps * cf ρ kept j - ρ.val p.eps * ρ.val p.walk.2 * cf ρ p.start j := by
  rw [cf_rowForm]
  rcases h with h | h
  · rw [sumFrom_past ρ j p.walk.1 p.first h]
    ring
  · rw [sumFrom_unit ρ j p.walk.1 p.first (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none, ρ.zero]
    ring

/-- psi at g under the plain weight is g. -/
theorem psi_plain (d : ℕ) (g : E) : ρ.val (polyAt (Weight.plain d).psi g) = ρ.val g := by
  show ρ.val (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE) = ρ.val g
  rw [ρ.add, ρ.mul, ρ.add, ρ.mul, ρ.zero, ρ.one]
  ring

variable [NoZeroDivisors K]

/-- The loop of powers makes no word that reads as 0, from words that do not. -/
theorem powersLoop_ne {x : E} (hx : ρ.val x ≠ 0) : ∀ (n : ℕ) (c : E) (done : List E),
    ρ.val c ≠ 0 → (∀ y ∈ done, ρ.val y ≠ 0) → ∀ y ∈ powersLoop x n c done, ρ.val y ≠ 0
  | 0, _, done, _, hd, y, hy => hd y (List.mem_reverse.1 hy)
  | n + 1, c, done, hc, hd, y, hy =>
    powersLoop_ne hx n (mulE c x) (c :: done) (by rw [ρ.mul]; exact mul_ne_zero hc hx)
      (fun z hz => by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hc
        · exact hd z hz) y hy

/-- No one of the words c, c x, c x^2 … reads as 0, where c and x do not. -/
theorem powers_ne {c x : E} (hc : ρ.val c ≠ 0) (hx : ρ.val x ≠ 0) (n : ℕ) :
    ∀ y ∈ powers c x n, ρ.val y ≠ 0 :=
  powersLoop_ne ρ hx n c [] hc fun _ h => absurd h (List.not_mem_nil)

variable [Nontrivial K]

/-- **No word of the hiding walk reads as 0, nor does the product P**, where each variable's
challenge and its psi at that challenge read as not 0. -/
theorem walk_ne : ∀ l : List (Weight × E),
    (∀ y ∈ l, ρ.val y.2 ≠ 0 ∧ ρ.val (polyAt y.1.psi y.2) ≠ 0) →
    (∀ x ∈ (hidingWalk l).1, ρ.val x ≠ 0) ∧ ρ.val (hidingWalk l).2 ≠ 0
  | [], _ => ⟨fun _ h => absurd h (List.not_mem_nil), by
      show ρ.val oneE ≠ 0
      rw [ρ.one]
      exact one_ne_zero⟩
  | [(w, g)], h => by
    obtain ⟨h1, h2⟩ := h (w, g) (List.mem_cons.mpr (Or.inl rfl))
    refine ⟨?_, h2⟩
    show ∀ x ∈ powers oneE g w.d, ρ.val x ≠ 0
    exact powers_ne ρ (by rw [ρ.one]; exact one_ne_zero) h1 _
  | (w, g) :: y :: rest, h => by
    obtain ⟨h1, h2⟩ := h (w, g) (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨i1, i2⟩ := walk_ne (y :: rest) fun z hz => h z (List.mem_cons.mpr (Or.inr hz))
    constructor
    · show ∀ x ∈ powers (mulE (hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
        (hidingWalk (y :: rest)).1, ρ.val x ≠ 0
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact powers_ne ρ (by rw [ρ.mul]; exact mul_ne_zero i2 h1) h1 _ x hx
      · exact i1 x hx
    · show ρ.val (mulE (hidingWalk (y :: rest)).2 (polyAt w.psi g)) ≠ 0
      rw [ρ.mul]
      exact mul_ne_zero i2 h2

end ring

/-- **From a coefficient to `liveAt`**: a form of the list whose coefficient on slot j reads as not
0 makes j live in the list as plain claims. -/
theorem live_of_cf {l : List Aff} {f : Aff} {j : ℕ} (hf : f ∈ l) (h : cf Reading.gl f j ≠ 0) :
    liveAt (K8.Honest.plainOf l) j = true :=
  (liveAt_iff _ j).2 ⟨{ form := f }, List.mem_map.2 ⟨f, hf, rfl⟩, rfl, h⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.cf
#print axioms ProofFile.Honest.K4.Live.sum_zero_of
#print axioms ProofFile.Honest.K4.Live.cf_eq
#print axioms ProofFile.Honest.K4.Live.cf_ofConst
#print axioms ProofFile.Honest.K4.Live.cf_empty
#print axioms ProofFile.Honest.K4.Live.cf_slot_self
#print axioms ProofFile.Honest.K4.Live.cf_slot_ne
#print axioms ProofFile.Honest.K4.Live.cf_addMul
#print axioms ProofFile.Honest.K4.Live.cf_add
#print axioms ProofFile.Honest.K4.Live.cf_sub
#print axioms ProofFile.Honest.K4.Live.cf_scale
#print axioms ProofFile.Honest.K4.Live.cf_of_slotsIn
#print axioms ProofFile.Honest.K4.Live.sumFrom_nought
#print axioms ProofFile.Honest.K4.Live.cf_rowForm
#print axioms ProofFile.Honest.K4.Live.cf_rowForm_in
#print axioms ProofFile.Honest.K4.Live.cf_rowForm_out
#print axioms ProofFile.Honest.K4.Live.psi_plain
#print axioms ProofFile.Honest.K4.Live.powersLoop_ne
#print axioms ProofFile.Honest.K4.Live.powers_ne
#print axioms ProofFile.Honest.K4.Live.walk_ne
#print axioms ProofFile.Honest.K4.Live.live_of_cf
