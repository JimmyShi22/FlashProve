-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/SlotsFew.lean (kind K9): STATEMENTS AND PROOFS ON THE VERIFIER's OWN TEXT; NO
PROVER IS IN THIS FILE, AND NO GOAL IS STATED: how many values of the batching's element chi make
the test "every sent scalar stands in a claim" (`First.Door.freeSlotOk`, the condition of
`K9.freeSlot`) say no behind the adding.

  `unitAt j`, `nought`   two worlds: the value under slot j is 1, all else 0; all is 0
  `slotCoef cl j`        the coefficient with which the claim cl names slot j, read in K: the sum
                         over the pairs of its form that name j
  `slotSum x n c l j`    the sum over a list of claims of x ^ exponent * that coefficient
  `slot_eval`            **behind the adding of a list of claims the coefficient on slot j is what it
                         was in front, plus slotSum at chi.** From the sealed algebra of the ledger
                         (`addAll_total`, Johnson/Desc/First/Batch/Law/Ledger.lean), taken at the two
                         worlds and subtracted
  `slotPoly n c l j`, `slotPoly_eval`   the same sum as a polynomial, and its value
  `few_roots`            n polynomials, those that are "live" not 0 and of degree at most d: at most
                         n * d elements of the field are a root of a live one
  `SlotsGood`            THE PREMISES, each under its name (below)
  `freeSlot_few`         **UNDER THEM AT MOST n * d ELEMENTS OF THE FIELD ARE READINGS OF A chi AT WHICH
                         THE ADDING RETURNS AND THE TEST SAYS NO**

THE PREMISES (`SlotsGood`). R x: x is a challenge of which something is said (for a caller: those
at which the verifier's text comes as far as the adding). F x, cls x: the ledger in front of the
adding and the list of claims, where x is drawn. Each premise is asked at the x with R x alone.
  chi       the ledger holds x as its batching element
  sized     it has one coefficient for each slot
  empty     every coefficient is the word 0 in front of the adding
  fixed     ON THE SLOTS UNDER TEST BUT THE MERGE's THE CLAIMS' COEFFICIENTS, NUMBERS AND EXPONENTS DO
            NOT HANG ON x: the polynomial is one and the same P j at every x
  live      P j is not the zero polynomial, and its degree is at most d
  unnamed   no claim names the merge's slot, in any pair of its form (also not with the coefficient 0)
WHAT IS COUNTED. READINGS IN THE FIELD, NOT WORDS: several triples of words can have one reading; whoever
counts challenges as they are drawn needs that a drawn element's words are below the prime, where the
reading is one-to-one. n * d counts the merge's slot with the others: one d too many where there is a
merge.
WHAT IS NOT CLAIMED. That the premises hold at any segment of the protocol: `fixed` is a law on the
other kinds' runs of claims; `live` hangs on what the claims' makers lay into a slot's coefficient:
the verifier's text names drawn elements and, at a layers' segment, values that were sent
(Johnson/Desc/First/Door/Sums.lean, its head); at n above
the ledger's number of slots the premises can still hold, but then the adding refuses at every x (a
claim that names a slot beyond is refused) and the count is 0: idle. Nothing
on how chi is drawn: a count of field elements, no probability. Nothing on soundness, on an honest prover
or on any other property.

-/
import Mathlib.Algebra.Polynomial.Roots
import Johnson.Desc.First.Batch.Law.Count
import Johnson.Desc.First.Batch.Law.SumsMeans
import Johnson.Desc.First.Door.Sums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9H
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (addList)
open VerifiableInference.Desc.K9L (expo claimValue claimsSum addAll_total addList_older addList_slot)
open VerifiableInference.Desc.First.Door (freeSlotOk)

section ring
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The world in which the value under slot j is 1 and all else is 0. -/
def unitAt (K : Type) [CommRing K] (j : Nat) : World K :=
  ⟨fun i => if i = j then 1 else 0, fun _ _ _ => 0⟩

/-- The world in which all is 0. -/
def nought (K : Type) [CommRing K] : World K := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- The coefficient with which a claim names slot j. -/
def slotCoef (cl : Claim) (j : Nat) : K :=
  (cl.form.slots.toList.map (slotValue ρ (unitAt K j))).sum

/-- The sum over a list of claims of x ^ exponent * the coefficient on slot j; c: the first claim's
number. -/
def slotSum (x : K) (n c : Nat) (l : List Claim) (j : Nat) : K :=
  sumFrom (fun i cl => x ^ expo n i cl * slotCoef ρ cl j) c l

theorem sumFrom_past (j : Nat) : ∀ (l : List E) (s : Nat), j < s →
    sumFrom (fun i v => ρ.val v * (unitAt K j).slot i) s l = 0
  | [], _, _ => rfl
  | v :: l, s, h => by
    have e : (unitAt K j).slot s = 0 := if_neg (by omega)
    show ρ.val v * (unitAt K j).slot s + _ = 0
    rw [e, sumFrom_past j l (s + 1) (by omega)]
    simp

theorem sumFrom_unit (j : Nat) : ∀ (l : List E) (s : Nat), s ≤ j →
    sumFrom (fun i v => ρ.val v * (unitAt K j).slot i) s l = ρ.val (l.getD (j - s) zeroE)
  | [], _, _ => by
    show (0 : K) = _
    rw [List.getD_nil, ρ.zero]
  | v :: l, s, h => by
    show ρ.val v * (unitAt K j).slot s + _ = _
    by_cases hs : s = j
    · subst hs
      have e : (unitAt K s).slot s = 1 := if_pos rfl
      rw [e, sumFrom_past ρ s l (s + 1) (by omega)]
      simp
    · have e : (unitAt K j).slot s = 0 := if_neg hs
      rw [e, sumFrom_unit j l (s + 1) (by omega)]
      have e2 : j - s = (j - (s + 1)) + 1 := by omega
      rw [e2, List.getD_cons_succ]
      simp

/-- In the unit world the slots' value is the coefficient on slot j. -/
theorem slotsValue_unit (LS : Array E) (j : Nat) :
    slotsValue ρ (unitAt K j) LS = ρ.val (LS.getD j zeroE) := by
  unfold slotsValue
  rw [sumFrom_unit ρ j LS.toList 0 (Nat.zero_le _)]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem sumFrom_zero {α : Type} (g : Nat → α → K) (h : ∀ i a, g i a = 0) :
    ∀ (l : List α) (s : Nat), sumFrom g s l = 0
  | [], _ => rfl
  | a :: l, s => by
    show g s a + _ = 0
    rw [h, sumFrom_zero g h l (s + 1)]
    simp

theorem slotsValue_nought (LS : Array E) : slotsValue ρ (nought K) LS = 0 :=
  sumFrom_zero _ (fun _ v => by show ρ.val v * (0 : K) = 0; simp) _ _

/-- The two worlds part in the slots alone. -/
theorem total_sub (F : Fork) (j : Nat) :
    F.total ρ (unitAt K j) - F.total ρ (nought K) = ρ.val (F.LS.getD j zeroE) := by
  have e : treesValue ρ (unitAt K j) F.trees = treesValue ρ (nought K) F.trees := rfl
  unfold Fork.total
  rw [e, slotsValue_unit, slotsValue_nought]
  ring

theorem claimValue_sub (cl : Claim) (j : Nat) :
    claimValue ρ (unitAt K j) cl - claimValue ρ (nought K) cl = slotCoef ρ cl j := by
  have e1 : (cl.form.ents.toList.map (Ent.value ρ (unitAt K j))).sum =
      (cl.form.ents.toList.map (Ent.value ρ (nought K))).sum := rfl
  have e2 : (cl.runs.toList.map (Run2.value ρ (unitAt K j))).sum =
      (cl.runs.toList.map (Run2.value ρ (nought K))).sum := rfl
  have e3 : (cl.form.slots.toList.map (slotValue ρ (nought K))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    show ρ.val y.2 * (0 : K) = 0
    simp
  unfold claimValue Aff.value slotCoef
  rw [e1, e2, e3]
  ring

theorem claimsSum_sub (x : K) (n : Nat) (j : Nat) : ∀ (l : List Claim) (c : Nat),
    claimsSum ρ (unitAt K j) x n c l - claimsSum ρ (nought K) x n c l = slotSum ρ x n c l j
  | [], _ => by simp [claimsSum, slotSum, sumFrom]
  | cl :: l, c => by
    have h := claimsSum_sub x n j l (c + 1)
    have h1 := claimValue_sub ρ cl j
    simp only [claimsSum, slotSum, sumFrom] at h ⊢
    rw [← h, ← h1]
    ring

/-- **Behind the adding the coefficient on slot j is what it was, plus the claims' sum at chi.** -/
theorem slot_eval (F G : Fork) (l : List Claim) (j : Nat) (hs : F.LS.size = F.ns)
    (h : addAll F l = some G) :
    ρ.val (G.LS.getD j zeroE) =
      ρ.val (F.LS.getD j zeroE) + slotSum ρ (ρ.val F.theta) F.planClaimsF F.nClaim l j := by
  have a := (addAll_total ρ (unitAt K j) l F G hs h).1
  have b := (addAll_total ρ (nought K) l F G hs h).1
  rw [← total_sub ρ G j, ← total_sub ρ F j, ← claimsSum_sub ρ _ _ j l _, a, b]
  ring

/-- The same sum as a polynomial. -/
noncomputable def slotPoly (n c : Nat) (l : List Claim) (j : Nat) : Polynomial K :=
  sumFrom (fun i cl => Polynomial.monomial (expo n i cl) (slotCoef ρ cl j)) c l

theorem slotPoly_eval (x : K) (n j : Nat) : ∀ (l : List Claim) (c : Nat),
    (slotPoly ρ n c l j).eval x = slotSum ρ x n c l j
  | [], _ => by simp [slotPoly, slotSum, sumFrom]
  | cl :: l, c => by
    have h := slotPoly_eval x n j l (c + 1)
    simp only [slotPoly, slotSum, sumFrom] at h ⊢
    rw [Polynomial.eval_add, h, Polynomial.eval_monomial]
    ring

end ring

section field
variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **The count**: at most n * d elements are a root of a live polynomial. -/
theorem few_roots (n d : Nat) (P : Nat → Polynomial K) (live : Nat → Prop)
    (h : ∀ j < n, live j → P j ≠ 0 ∧ (P j).natDegree ≤ d) :
    Prob.cnt (fun x : K => ∃ j < n, live j ∧ (P j).eval x = 0) ≤ n * d := by
  classical
  unfold Prob.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let U : Finset K := (Finset.range n).biUnion fun j => if live j then (P j).roots.toFinset else ∅
  have hsub : (Finset.univ.filter fun x : K => ∃ j < n, live j ∧ (P j).eval x = 0) ⊆ U := by
    intro x hx
    obtain ⟨j, hj, hl, h0⟩ := (Finset.mem_filter.1 hx).2
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, ?_⟩
    rw [if_pos hl, Multiset.mem_toFinset, Polynomial.mem_roots (h j hj hl).1]
    exact h0
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc (∑ j ∈ Finset.range n, (if live j then (P j).roots.toFinset else ∅).card)
      ≤ ∑ _j ∈ Finset.range n, d := by
        refine Finset.sum_le_sum fun j hj => ?_
        by_cases hl : live j
        · rw [if_pos hl]
          exact le_trans (Multiset.toFinset_card_le _)
            (le_trans (Polynomial.card_roots' _) (h j (Finset.mem_range.1 hj) hl).2)
        · rw [if_neg hl]
          simp
    _ = n * d := by simp

/-- **The premises**, each under its name: the file's head says each in words. -/
structure SlotsGood (n : Nat) (merge : Option Nat) (d : Nat) (P : Nat → Polynomial K)
    (R : E → Prop) (F : E → Fork) (cls : E → List Claim) : Prop where
  chi : ∀ x, R x → (F x).theta = x
  sized : ∀ x, R x → (F x).LS.size = (F x).ns
  empty : ∀ x, R x → ∀ j, (F x).LS.getD j zeroE = zeroE
  fixed : ∀ x, R x → ∀ j < n, merge ≠ some j →
    slotPoly ρ (F x).planClaimsF (F x).nClaim (cls x) j = P j
  live : ∀ j < n, merge ≠ some j → P j ≠ 0 ∧ (P j).natDegree ≤ d
  unnamed : ∀ x, R x → ∀ j < n, merge = some j → ∀ cl ∈ cls x, ∀ y ∈ cl.form.slots, y.1 ≠ j

/-- **Few values of chi fail the test.** -/
theorem freeSlot_few (n : Nat) (merge : Option Nat) (d : Nat) (P : Nat → Polynomial K)
    (R : E → Prop) (F : E → Fork) (cls : E → List Claim) (g : SlotsGood ρ n merge d P R F cls) :
    Prob.cnt (fun y : K => ∃ x G, ρ.val x = y ∧ R x ∧ addList (F x) (cls x) = .ok G ∧
      freeSlotOk n merge G = false) ≤ n * d := by
  refine le_trans (Prob.cnt_mono fun y hy => ?_)
    (few_roots n d P (fun j => merge ≠ some j) g.live)
  obtain ⟨x, G, rfl, hR, hG, hno⟩ := hy
  -- some slot below n answers otherwise than it should
  have hex : ∃ j < n, isZeroE (G.LS.getD j zeroE) ≠ (merge == some j) := by
    by_contra hc
    have hall : freeSlotOk n merge G = true := by
      unfold freeSlotOk
      rw [List.all_eq_true]
      intro j hj
      rw [beq_iff_eq]
      by_contra hne
      exact hc ⟨j, List.mem_range.1 hj, hne⟩
    rw [hall] at hno
    exact nomatch hno
  obtain ⟨j, hj, hne⟩ := hex
  by_cases hm : merge = some j
  · -- the merge's slot: no claim names it: the word 0 stays
    exfalso
    have e := addList_slot j (cls x) (F x) G hG (g.unnamed x hR j hj hm)
    rw [g.empty x hR j] at e
    apply hne
    have z : isZeroE zeroE = true := rfl
    rw [e, hm, z]
    simp
  · refine ⟨j, hj, hm, ?_⟩
    have hz : isZeroE (G.LS.getD j zeroE) = true := by
      have hb : (merge == some j) = false := by simpa using hm
      rw [hb] at hne
      simpa using hne
    have h0 : ρ.val (G.LS.getD j zeroE) = 0 := by rw [isZeroE_eq hz, ρ.zero]
    have hv := slot_eval ρ (F x) G (cls x) j (g.sized x hR) (addList_older _ _ _ hG)
    rw [h0, g.empty x hR j, ρ.zero, zero_add, g.chi x hR, ← slotPoly_eval, g.fixed x hR j hj hm] at hv
    exact hv.symm

end field

end VerifiableInference.Desc.K9H

#print axioms VerifiableInference.Desc.K9H.slot_eval
#print axioms VerifiableInference.Desc.K9H.slotPoly_eval
#print axioms VerifiableInference.Desc.K9H.few_roots
#print axioms VerifiableInference.Desc.K9H.freeSlot_few
