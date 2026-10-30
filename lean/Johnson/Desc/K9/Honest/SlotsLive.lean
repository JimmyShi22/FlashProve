-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/SlotsLive.lean (kind K9): "THE CLAIMS ARE GOOD ON THE SLOTS", AS A BOOL WITH
CODE, AND WHAT IT GIVES. Definitions with code, statements and proofs ON THE VERIFIER's OWN DATA; no
prover is in this file, and no goal is stated.

  `slotWord cl j`     the coefficient with which the claim cl names slot j, as a word of the program:
                      the sum over the pairs of its form that name j. `slotWord_val`: read in the
                      field it is `slotCoef` (Johnson/Desc/K9/Honest/SlotsFew.lean)
  `notZero w`         all three words of w are below the prime, and not all are 0: then its reading is
                      not 0 (`notZero_val`). At `slotWord` the first half is always so
                      (`okE_slotWord`: a sum of the program has words below the prime)
  `liveAt cls j`      some claim THAT TAKES ITS OWN NUMBER (eqFirst = none) names slot j with a
                      coefficient that is `notZero`
  `plainAt cls j`     every claim that is added under a higher power (eqFirst = some) names slot j in
                      no pair
  `unnamedAt cls j`   no claim names slot j in any pair
  `slotsLive n merge cls`   **THE BOOL**: at each slot below n: at the merge's: `unnamedAt`; at every
                      other: `liveAt` and `plainAt`
  `coeff_plain`       below the plan's number n the coefficient of X^m in `slotPoly` is that of the one
                      claim with the number m, if that claim takes its own number; else 0
  `live_of_bool`      **where the claims' numbers stay below the plan's number: `liveAt` gives: the
                      polynomial is not 0; `plainAt` gives: its degree is at most n - 1**
  `unnamed_of_bool`   `unnamedAt` as the premise `unnamed` has it
  `liveAt_iff`        **ON THE FIELD's SIDE**: `liveAt l j` holds just if some claim of l that takes its own
                      number has a coefficient on slot j whose reading is not 0

WHAT IS NOT CLAIMED. That the Bool is true at any segment of the protocol. It is a sufficient
condition: a slot whose only claims are added under a higher power is counted as not live. Nothing on
any property.

-/
import Johnson.Desc.K9.Honest.SlotsFew
import OnBytes.Slice.ProgField
import OnBytes.Slice.SimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9H
open OnBytes OnBytes.Model Polynomial
open VerifiableInference.Desc.K9L (expo)

/-! ## The Bool -/

/-- The coefficient with which a claim names slot j, as a word. -/
def slotWord (cl : Claim) (j : Nat) : E :=
  cl.form.slots.toList.foldl (fun a x => if x.1 == j then addE a x.2 else a) zeroE

/-- The words are below the prime, and not all 0. -/
def notZero (w : E) : Bool := okE w && !isZeroE w

def liveAt (cls : List Claim) (j : Nat) : Bool :=
  cls.any fun cl => cl.eqFirst.isNone && notZero (slotWord cl j)

def unnamedIn (cl : Claim) (j : Nat) : Bool := cl.form.slots.toList.all fun x => x.1 != j

def plainAt (cls : List Claim) (j : Nat) : Bool :=
  cls.all fun cl => cl.eqFirst.isNone || unnamedIn cl j

def unnamedAt (cls : List Claim) (j : Nat) : Bool := cls.all fun cl => unnamedIn cl j

/-- **The claims are good on the slots below n.** -/
def slotsLive (n : Nat) (merge : Option Nat) (cls : List Claim) : Bool :=
  (List.range n).all fun j =>
    if merge == some j then unnamedAt cls j else liveAt cls j && plainAt cls j

/-! ## What it gives -/

section ring
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem foldl_val (j : Nat) : ∀ (l : List (Nat × E)) (a : E),
    ρ.val (l.foldl (fun a x => if x.1 == j then addE a x.2 else a) a) =
      ρ.val a + (l.map (slotValue ρ (unitAt K j))).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_val j l, List.map_cons, List.sum_cons]
    by_cases h : x.1 = j
    · have e : (unitAt K j).slot j = 1 := if_pos rfl
      simp only [slotValue, beq_iff_eq, h, if_true, ρ.add, e]
      ring
    · have e : (unitAt K j).slot x.1 = 0 := if_neg h
      simp only [slotValue, e, beq_iff_eq, h, if_false]
      ring

theorem slotWord_val (cl : Claim) (j : Nat) : ρ.val (slotWord cl j) = slotCoef ρ cl j := by
  unfold slotWord slotCoef
  rw [foldl_val, ρ.zero, zero_add]

theorem slotCoef_unnamed (cl : Claim) (j : Nat) (h : unnamedIn cl j = true) :
    slotCoef ρ cl j = 0 := by
  unfold slotCoef
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hne : x.1 ≠ j := by
    have := List.all_eq_true.1 h x hx
    simpa using this
  have e : (unitAt K j).slot x.1 = 0 := if_neg hne
  simp [slotValue, e]

/-- The coefficient of X^m, term by term. -/
theorem coeff_slotPoly (n j m : Nat) : ∀ (l : List Claim) (c : Nat),
    (slotPoly ρ n c l j).coeff m =
      sumFrom (fun i cl => if expo n i cl = m then slotCoef ρ cl j else 0) c l
  | [], _ => by simp [slotPoly, sumFrom]
  | cl :: l, c => by
    have h := coeff_slotPoly n j m l (c + 1)
    simp only [slotPoly, sumFrom] at h ⊢
    rw [coeff_add, h, coeff_monomial]

theorem sum_past (n j m : Nat) (hm : m < n) : ∀ (l : List Claim) (c : Nat), m < c →
    sumFrom (fun i cl => if expo n i cl = m then slotCoef ρ cl j else 0) c l = 0
  | [], _, _ => rfl
  | cl :: l, c, h => by
    have e : expo n c cl ≠ m := by
      unfold expo
      cases cl.eqFirst with
      | none => show c ≠ m; omega
      | some f => show n + f ≠ m; omega
    show (if expo n c cl = m then slotCoef ρ cl j else 0) + _ = 0
    rw [if_neg e, sum_past n j m hm l (c + 1) (by omega), add_zero]

/-- **Below the plan's number the coefficient of X^m is the one claim's with the number m.** -/
theorem coeff_plain (n j m : Nat) (hm : m < n) : ∀ (l : List Claim) (c : Nat), c ≤ m →
    (slotPoly ρ n c l j).coeff m =
      ((l[m - c]?).map fun cl => if cl.eqFirst.isNone then slotCoef ρ cl j else 0).getD 0
  | [], c, _ => by simp [slotPoly, sumFrom]
  | cl :: l, c, h => by
    rw [coeff_slotPoly]
    show (if expo n c cl = m then slotCoef ρ cl j else 0) + _ = _
    by_cases hc : c = m
    · subst hc
      rw [sum_past ρ n j c hm l (c + 1) (by omega), add_zero, Nat.sub_self]
      show _ = (if cl.eqFirst.isNone then slotCoef ρ cl j else 0)
      unfold expo
      cases cl.eqFirst with
      | none => simp
      | some f =>
        have : n + f ≠ c := by omega
        simp [this]
    · have e : expo n c cl ≠ m := by
        unfold expo
        cases cl.eqFirst with
        | none => exact hc
        | some f => show n + f ≠ m; omega
      rw [if_neg e, zero_add, ← coeff_slotPoly, coeff_plain n j m hm l (c + 1) (by omega)]
      have e2 : m - c = (m - (c + 1)) + 1 := by omega
      rw [e2, List.getElem?_cons_succ]

/-- The degree: where every claim under a higher power leaves slot j unnamed. -/
theorem degree_plain (n j : Nat) : ∀ (l : List Claim) (c : Nat), c + l.length ≤ n →
    plainAt l j = true → (slotPoly ρ n c l j).natDegree ≤ n - 1
  | [], _, _, _ => by simp [slotPoly, sumFrom]
  | cl :: l, c, hn, hp => by
    have hl : c + 1 + l.length ≤ n := by simpa [Nat.add_assoc, Nat.add_comm 1] using hn
    unfold plainAt at hp
    rw [List.all_cons, Bool.and_eq_true] at hp
    have h := degree_plain n j l (c + 1) hl hp.2
    show (monomial (expo n c cl) (slotCoef ρ cl j) + slotPoly ρ n (c + 1) l j).natDegree ≤ n - 1
    refine le_trans (natDegree_add_le _ _) (max_le ?_ h)
    cases he : cl.eqFirst with
    | none =>
      have e : expo n c cl = c := by unfold expo; rw [he]
      rw [e]
      exact le_trans (natDegree_monomial_le _) (by simp at hn; omega)
    | some f =>
      have hu : unnamedIn cl j = true := by simpa [he] using hp.1
      rw [slotCoef_unnamed ρ cl j hu, map_zero]
      simp

end ring

theorem notZero_val (w : E) (h : notZero w = true) : Reading.gl.val w ≠ 0 := by
  unfold notZero at h
  rw [Bool.and_eq_true] at h
  intro h0
  have hz : isZeroE w = true := (Slice.isZeroE_iff w h.1).2 h0
  rw [hz] at h
  exact nomatch h.2

theorem okE_add (a b : E) : okE (addE a b) = true := by
  rw [okE_triple, addE_triple]
  exact Slice.okE_addE _ _

theorem okE_foldl (j : Nat) : ∀ (l : List (Nat × E)) (a : E), okE a = true →
    okE (l.foldl (fun a x => if x.1 == j then addE a x.2 else a) a) = true
  | [], _, h => h
  | x :: l, a, h => by
    rw [List.foldl_cons]
    apply okE_foldl j l
    by_cases hx : (x.1 == j) = true
    · rw [if_pos hx]; exact okE_add _ _
    · rw [if_neg hx]; exact h

/-- The coefficient's words are below the prime. -/
theorem okE_slotWord (cl : Claim) (j : Nat) : okE (slotWord cl j) = true :=
  okE_foldl j _ zeroE rfl

/-- **`liveAt`, on the field's side.** -/
theorem liveAt_iff (l : List Claim) (j : Nat) :
    liveAt l j = true ↔ ∃ cl ∈ l, cl.eqFirst = none ∧ slotCoef Reading.gl cl j ≠ 0 := by
  unfold liveAt
  rw [List.any_eq_true]
  constructor
  · rintro ⟨cl, hcl, hb⟩
    rw [Bool.and_eq_true] at hb
    refine ⟨cl, hcl, by simpa using hb.1, ?_⟩
    rw [← slotWord_val]
    exact notZero_val _ hb.2
  · rintro ⟨cl, hcl, he, hne⟩
    refine ⟨cl, hcl, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨by simp [he], ?_⟩
    unfold notZero
    rw [okE_slotWord, Bool.true_and]
    cases hz : isZeroE (slotWord cl j) with
    | false => rfl
    | true =>
      exfalso
      apply hne
      rw [← slotWord_val, isZeroE_eq hz, Reading.gl.zero]

/-- **What the Bool gives at a slot that is not the merge's.** -/
theorem live_of_bool (n c j : Nat) (l : List Claim) (hn : c + l.length ≤ n)
    (h1 : liveAt l j = true) (h2 : plainAt l j = true) :
    slotPoly Reading.gl n c l j ≠ 0 ∧ (slotPoly Reading.gl n c l j).natDegree ≤ n - 1 := by
  refine ⟨fun h0 => ?_, degree_plain Reading.gl n j l c hn h2⟩
  obtain ⟨cl, hcl, hb⟩ := List.any_eq_true.1 h1
  rw [Bool.and_eq_true] at hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  have hm : c + i < n := by omega
  have hc := coeff_plain Reading.gl n j (c + i) hm l c (Nat.le_add_right _ _)
  rw [h0, coeff_zero, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi] at hc
  simp only [Option.map_some, Option.getD_some, hb.1, if_true] at hc
  exact notZero_val _ hb.2 ((slotWord_val Reading.gl _ j).trans hc.symm)

/-- `unnamedAt`, as the premise has it. -/
theorem unnamed_of_bool (l : List Claim) (j : Nat) (h : unnamedAt l j = true) :
    ∀ cl ∈ l, ∀ y ∈ cl.form.slots, y.1 ≠ j := by
  intro cl hcl y hy
  have h1 := List.all_eq_true.1 h cl hcl
  have h2 := List.all_eq_true.1 h1 y (Array.mem_toList_iff.2 hy)
  simpa using h2

end VerifiableInference.Desc.K9H

#print axioms VerifiableInference.Desc.K9H.slotWord_val
#print axioms VerifiableInference.Desc.K9H.coeff_plain
#print axioms VerifiableInference.Desc.K9H.degree_plain
#print axioms VerifiableInference.Desc.K9H.notZero_val
#print axioms VerifiableInference.Desc.K9H.okE_slotWord
#print axioms VerifiableInference.Desc.K9H.liveAt_iff
#print axioms VerifiableInference.Desc.K9H.live_of_bool
#print axioms VerifiableInference.Desc.K9H.unnamed_of_bool
