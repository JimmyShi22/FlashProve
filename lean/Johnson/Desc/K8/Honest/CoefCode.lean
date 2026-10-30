-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CoefCode.lean: THE COEFFICIENT OF A CLAIM ON ONE ENTRY OF AN ARRAY, WITH
CODE. Definitions, statements and proofs. On claims alone: no ledger, no block, no prover. Lemmas;
none of the library's goals.

`coefOn` (Johnson/Desc/K8/Honest/FallCount.lean) reads a claim's coefficient on an entry off the
claim's value in two worlds: no code. Here it is computed, by the verifier's own addE and mulE: a
claim lays on an entry what its form's entries at that place bear, and what its runs that cover the
place bear.
  `entsE`, `runsE`, `coefE cl t r i`   the two shares and their sum
  `ents_diff`, `run_diff`, `runs_diff`   each share, against the values in the two worlds
  **`coefOn_eq`**   coefOn cl t r i is the value of coefE cl t r i
  `liveAt cl t r i`   coefE cl t r i is not 0 as a word; **`live_ne`**: then coefOn cl t r i is not
      0: an output of addE has words below the prime
  `noneZero_no`   where noneZero L first n says no, and first ≤ L.size or 0 < n: some u < n has
      L.getD (first + u) zeroE = zeroE: also where L is shorter than first + n. (At n = 0 and first
      > L.size the test says no and asks no entry.)
By: OnBytes.Slice.isZeroE_iff (OnBytes/Slice/ProgField.lean) · okE_add
(Johnson/Top/H/P1Tie/Words.lean) · `runSum_pick`, `runSum_nil` (FallReads.lean).
Limits: identities on one claim.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallReads
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- What a form's entries bear at the place. -/
def entsE (l : List Ent) (t r i : Nat) : E :=
  l.foldr (fun x s => if x.tree = t ∧ x.row = r ∧ x.idx = i then addE x.coef s else s) zeroE

/-- What the runs that cover the place bear. -/
def runsE (l : List Run2) (t r i : Nat) : E :=
  l.foldr (fun R s =>
    if R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n then
      addE (mulE R.coef (R.w.getD (R.w0 + (i - R.first)) zeroE)) s
    else s) zeroE

/-- **The coefficient, with code.** -/
def coefE (cl : Claim) (t r i : Nat) : E :=
  addE (entsE cl.form.ents.toList t r i) (runsE cl.runs.toList t r i)

theorem ents_diff (t r i : Nat) : ∀ l : List Ent,
    (l.map (Ent.value Reading.gl (oneAt t r i))).sum - (l.map (Ent.value Reading.gl allZero)).sum =
      Reading.gl.val (entsE l t r i)
  | [] => by
    simp only [List.map_nil, List.sum_nil, sub_zero, entsE, List.foldr_nil]
    exact Reading.gl.zero.symm
  | x :: l => by
    have ih := ents_diff t r i l
    simp only [List.map_cons, List.sum_cons, entsE, List.foldr_cons]
    have hz : Ent.value Reading.gl allZero x = 0 := by
      unfold Ent.value
      rw [entry_zero, mul_zero]
    by_cases hc : x.tree = t ∧ x.row = r ∧ x.idx = i
    · rw [if_pos hc, Reading.gl.add, hz]
      have h1 : Ent.value Reading.gl (oneAt t r i) x = Reading.gl.val x.coef := by
        unfold Ent.value
        show _ * (if x.tree = t ∧ x.row = r ∧ x.idx = i then (1 : Cb.Gl.E) else 0) = _
        rw [if_pos hc, mul_one]
      rw [h1]
      unfold entsE at ih
      linear_combination ih
    · rw [if_neg hc, hz]
      have h1 : Ent.value Reading.gl (oneAt t r i) x = 0 := by
        unfold Ent.value
        show _ * (if x.tree = t ∧ x.row = r ∧ x.idx = i then (1 : Cb.Gl.E) else 0) = _
        rw [if_neg hc, mul_zero]
      rw [h1]
      unfold entsE at ih
      linear_combination ih

theorem run_zero (R : Run2) : Run2.value Reading.gl allZero R = 0 := by
  unfold Run2.value
  simp only [entry_zero, mul_zero, runSum_zero]

theorem run_diff (t r i : Nat) (R : Run2) :
    Run2.value Reading.gl (oneAt t r i) R =
      if R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n then
        Reading.gl.val (mulE R.coef (R.w.getD (R.w0 + (i - R.first)) zeroE))
      else 0 := by
  unfold Run2.value
  by_cases hc : R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n
  · obtain ⟨c1, c2, c3, c4⟩ := hc
    rw [if_pos ⟨c1, c2, c3, c4⟩, Reading.gl.mul,
      runSum_pick _ R.n (i - R.first) (by omega) (fun d _ hne => by
        show _ * (if R.tree = t ∧ R.row = r ∧ R.first + d = i then (1 : Cb.Gl.E) else 0) = 0
        rw [if_neg (fun h => hne (by omega)), mul_zero])]
    show _ * (_ * (if R.tree = t ∧ R.row = r ∧ R.first + (i - R.first) = i then
      (1 : Cb.Gl.E) else 0)) = _
    rw [if_pos ⟨c1, c2, by omega⟩, mul_one]
  · rw [if_neg hc, runSum_nil _ R.n (fun d hd => by
      show _ * (if R.tree = t ∧ R.row = r ∧ R.first + d = i then (1 : Cb.Gl.E) else 0) = 0
      rw [if_neg (fun h => hc ⟨h.1, h.2.1, by omega, by omega⟩), mul_zero]), mul_zero]

theorem runs_diff (t r i : Nat) : ∀ l : List Run2,
    (l.map (Run2.value Reading.gl (oneAt t r i))).sum -
        (l.map (Run2.value Reading.gl allZero)).sum = Reading.gl.val (runsE l t r i)
  | [] => by
    simp only [List.map_nil, List.sum_nil, sub_zero, runsE, List.foldr_nil]
    exact Reading.gl.zero.symm
  | R :: l => by
    have ih := runs_diff t r i l
    simp only [List.map_cons, List.sum_cons, runsE, List.foldr_cons]
    rw [run_zero, run_diff]
    unfold runsE at ih
    by_cases hc : R.tree = t ∧ R.row = r ∧ R.first ≤ i ∧ i < R.first + R.n
    · rw [if_pos hc, if_pos hc, Reading.gl.add]
      linear_combination ih
    · rw [if_neg hc, if_neg hc]
      linear_combination ih

/-- **The coefficient is the code's value.** -/
theorem coefOn_eq (cl : Claim) (t r i : Nat) :
    coefOn cl t r i = Reading.gl.val (coefE cl t r i) := by
  unfold coefOn coefE K9L.claimValue Aff.value
  rw [Reading.gl.add, ← ents_diff, ← runs_diff]
  have hs : ∀ l : List (Nat × E), (l.map (slotValue Reading.gl (oneAt t r i))).sum =
      (l.map (slotValue Reading.gl allZero)).sum := fun l => rfl
  rw [hs]
  ring

/-- The coefficient is not 0, as a word. -/
def liveAt (cl : Claim) (t r i : Nat) : Bool := !isZeroE (coefE cl t r i)

/-- **A live word is a live value.** -/
theorem live_ne (cl : Claim) (t r i : Nat) (h : liveAt cl t r i = true) : coefOn cl t r i ≠ 0 := by
  rw [coefOn_eq]
  intro h0
  have h1 : isZeroE (coefE cl t r i) = true :=
    (OnBytes.Slice.isZeroE_iff _ (Part.MaskedSum.okE_add _ _)).2 h0
  unfold liveAt at h
  rw [h1] at h
  cases h

/-- Where `noneZero` says no. -/
theorem noneZero_no (L : Array E) (first n : Nat) (hfn : first ≤ L.size ∨ 0 < n)
    (h : noneZero L first n = false) :
    ∃ u, u < n ∧ L.getD (first + u) zeroE = zeroE := by
  by_cases hs : first + n ≤ L.size
  · by_contra hc
    have hall : noneZero L first n = true := by
      unfold noneZero
      simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true]
      refine ⟨hs, fun j hj => ?_⟩
      have hj' : j < n := by
        simp only [Array.size_extract] at hj
        omega
      rw [Bool.not_eq_true']
      cases hz : isZeroE (L.extract first (first + n))[j] with
      | false => rfl
      | true =>
        exfalso
        refine hc ⟨j, hj', ?_⟩
        have e := isZeroE_eq hz
        rw [Array.getElem_extract] at e
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
        simpa using e
    rw [hall] at h
    cases h
  · by_cases hf : first ≤ L.size
    · refine ⟨L.size - first, by omega, ?_⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    · refine ⟨0, hfn.resolve_left hf, ?_⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.coefOn_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.live_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.noneZero_no
