-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/LaidLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE: FROM
WHAT IS SENT TO WHAT LIES HIDDEN, FOR SCALARS THAT HAVE A ROUND TO THEMSELVES; AND THE VERIFIER'S
TWO TEXTS OF A SUMMAND ON SHOWN VALUES AGAINST PairLaw.lean'S (onK: a PairSum's summand in the
field).
WHAT IT IS NOT. No prover, no coin: that any round holds "value plus mask entry" is a premise here.
Nothing on whether the verifier accepts, on soundness, on completeness or on what a proof hides.
Nothing on canonical writing: equations in the field K. Mathlib and Johnson/Desc/Kinds/Law/ are in
the closure of its imports.
  hide_truth      CONDITIONAL. Scalars v are laid into a well-laid ledger as hidden scalars
                  (Johnson/Desc/Kinds/HeadParts.lean: hide); each reads as a value plus the mask
                  entry under its number: then in the world of every later ledger its variable is
                  worth the value.
  round_spec      what a return of one round's reading says. (Law/NormRule.lean's round_one, without
                  the classes that it carries.)
  batch_spec      what a return of sendThenBatch on its own round says: one round; its scalars; they
                  are laid by hide. (The lines of Law/NormRule.lean's batch_one, which concludes
                  another thing.) It bears the last name of a lemma of the library's on the same
                  return, Law.batch_spec (Law/NormHear.lean), which asks a well-laid ledger and
                  concludes yet another thing; inside this namespace the short name is this file's.
  batch_truth     CONDITIONAL. The same for sendThenBatch.
  onK_product     the summand of one product of the first two maps, in the field.
  product_on      the verifier's text "shown 0 * shown 1" reads as that summand on the readings.
  shown_endK      CONDITIONAL. At as many challenges as variables, where what is shown under each
                  number reads as the end value plus y times a mask entry, and as 0 beyond the maps,
                  the summand on the readings is PairLaw.lean's endK.
  onK_terms       the summand in the field is sumTerms (OnBytes/Desc/First/P1/PscProducts.lean).
  prSum_terms     the seven terms of prSum are tsP (Law/NormProducts.lean).
  summand_on      the verifier's text of the products' summand on four shown values
                  (OnBytes/Desc/First/P6: summand, under the powers of om), at one norm (NI = 1), as
                  Law/OpenedNorm.lean's prRow has it, reads as prSum's summand on the readings.
CALLED, OF THE LIBRARY: hide_unfold, hide_hidden, hidden_later, hideRun_ok, sized_of, vW_slot,
rd_summand, getD_zero, rd_one, rd_mul, rd_pow, rd_sumTo (Law/Base.lean), roundOf_spec
(Johnson/Desc/Part/MaskedSumShape.lean), and the small lemmas on a hearing's steps (bind_some,
need_some, pure_some, hide_some, round_some); of PairLaw.lean: onK_congr, ends_reads.

-/
import Mathlib
import Johnson.Desc.K6.Honest.TablesLaw
import Johnson.Desc.Kinds.Law.K06ClosedTruth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.P1 (sumTerms)
open Law (K rd worldE noEnt WellLaid)
open Law.Came (val)

/-! ## 1 From what is sent to what lies hidden -/

/-- **Scalars laid as hidden scalars.** x: the values. -/
theorem hide_truth {v : List E} {F0 F1 G : Fork} {A : Array Hid} (hW : WellLaid F0)
    (h : hide v F0 [] = some (A, F1, [])) (hL : Later F1 G) (mask : Nat → E) (x : List E)
    (hx : ∀ i, i < v.length →
      rd (v.getD i zeroE) = rd (x.getD i 0) + rd (mask (F0.next + i))) :
    ∀ i, i < v.length → val (worldE G mask noEnt) (A.getD i {}).var = rd (x.getD i 0) := by
  intro i hi
  obtain ⟨run, hc⟩ := Law.hide_unfold h
  obtain ⟨_, _, fill, _⟩ := OnBytes.PscRun.hideRun_ok
    ({ F0 with next := F0.next + v.length } : Fork) F1 _ _ _ (Law.sized_of hW) run
  have hf : OnBytes.PscRun.Filled F1 (F0.next + i) :=
    (fill i (by rw [List.size_toArray]; exact hi)).2.2.1
  have hvar : (A.getD i {}).var = Aff.slot (F0.next + i) := by
    rw [hc]
    simp [Array.getD, hi]
  rw [hvar]
  show Law.vW (worldE G mask noEnt) (Aff.slot (F0.next + i)) = _
  rw [Law.vW_slot]
  show rd (Law.hidden G mask (F0.next + i)) = _
  rw [Law.hidden_later mask hL hf, Law.hide_hidden hW h mask hi, hx i hi]
  ring

/-- What a return of one round's reading that leaves no round says. -/
theorem round_spec {n k : Nat} {F G : Fork} {p : List Fmt.RoundView} {x : List E × List E}
    (h : Hear.round n k F p = some (x, G, [])) :
    ∃ r, p = [r] ∧ Part.MaskedSum.roundOf n k r = some x := by
  cases p with
  | nil => cases h
  | cons r left =>
    have h' : (Part.MaskedSum.roundOf n k r).map (fun x => (x, F, left)) = some (x, G, []) := h
    cases hq : Part.MaskedSum.roundOf n k r with
    | none =>
      rw [hq] at h'
      cases h'
    | some y =>
      rw [hq] at h'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, _, rfl⟩ := h'
      exact ⟨r, rfl, hq⟩

/-- What a return of sendThenBatch that leaves no round says. -/
theorem batch_spec {n rows : Nat} {F Fa : Fork} {p : List Fmt.RoundView} {A : Array Hid} {g : E}
    (h : sendThenBatch n rows F p = some ((A, g), Fa, [])) :
    ∃ (r : Fmt.RoundView) (v gs : List E), p = [r] ∧ Part.MaskedSum.roundOf n 1 r = some (v, gs) ∧
      v.length = n ∧ hide v F [] = some (A, Fa, []) := by
  unfold sendThenBatch at h
  obtain ⟨vg, F1, l1, h1, k1⟩ := Law.bind_some h
  obtain ⟨v, gs⟩ := vg
  dsimp only at k1
  obtain ⟨A', F2, l2, h2, k2⟩ := Law.bind_some k1
  obtain ⟨g', F3, l3, h3, k3⟩ := Law.bind_some k2
  obtain ⟨_, rfl, rfl⟩ := Law.need_some h3
  obtain ⟨e, rfl, rfl⟩ := Law.pure_some k3
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hF : F = F1 := Law.Came.round_some h1
  subst hF
  obtain ⟨rfl, h2'⟩ := Law.hide_some h2
  obtain ⟨r, rfl, hr⟩ := round_spec h1
  exact ⟨r, v, gs, rfl, hr, (Part.MaskedSum.roundOf_spec hr).2.1, h2'⟩

/-- **A round of hidden scalars and one batching element.** x: the values. The premise on what the
round sent is asked at every reading of the round; batch_spec yields one. -/
theorem batch_truth {n rows : Nat} {F0 F1 G : Fork} {p : List Fmt.RoundView} {A : Array Hid} {g : E}
    (hW : WellLaid F0) (h : sendThenBatch n rows F0 p = some ((A, g), F1, [])) (hL : Later F1 G)
    (mask : Nat → E) (x : List E)
    (hx : ∀ (r : Fmt.RoundView) (v gs : List E), p = [r] →
      Part.MaskedSum.roundOf n 1 r = some (v, gs) → ∀ i, i < n →
        rd (v.getD i zeroE) = rd (x.getD i 0) + rd (mask (F0.next + i))) :
    ∀ i, i < n → val (worldE G mask noEnt) (A.getD i {}).var = rd (x.getD i 0) := by
  obtain ⟨r, v, gs, hp, hr, hl, hh⟩ := batch_spec h
  intro i hi
  exact hide_truth hW hh hL mask x (fun i hi => hx r v gs hp hr i (by rw [← hl]; exact hi)) i
    (by rw [hl]; exact hi)

/-! ## 2 The verifier's two texts of a summand on shown values -/

/-- The summand of one product of the first two maps. -/
theorem onK_product (s : PairSum) (hp : s.pairs = [(1, 0, 1)]) (v : Nat → K) :
    s.onK v = v 0 * v 1 := by
  unfold PairSum.onK
  rw [hp]
  simp [Law.rd_one]

/-- **"shown 0 * shown 1"** reads as that summand on the readings. -/
theorem product_on (s : PairSum) (hp : s.pairs = [(1, 0, 1)]) (sh : Nat → E) :
    rd (sh 0 * sh 1) = s.onK fun j => rd (sh j) := by
  rw [onK_product s hp, Law.rd_mul]

/-- **The summand on the end values as they are shown is the summand at the challenges**
(PairLaw.lean: endK). sh: what is shown under each number; beyond the maps it reads as 0. -/
theorem shown_endK (s : PairSum) (rs masks : List E) (y : E) (h : rs.length = s.z.length)
    (sh : Nat → E)
    (hv : ∀ j, j < s.maps.length →
      rd (sh j) = rd ((s.ends rs).getD j zeroE) + rd y * rd (masks.getD j zeroE))
    (h0 : ∀ j, s.maps.length ≤ j → rd (sh j) = 0) :
    (s.onK fun j => rd (sh j)) = s.endK rs masks y := by
  unfold PairSum.endK
  refine onK_congr s fun j => ?_
  by_cases hj : j < s.maps.length
  · rw [if_pos hj, hv j hj, ← Law.getD_zero, ← Law.getD_zero, ends_reads s rs j h]
  · rw [if_neg hj, h0 j (Nat.le_of_not_lt hj)]

/-- The summand in the field, as a sum of terms. -/
theorem onK_terms (s : PairSum) (v : Nat → K) :
    s.onK v = sumTerms (s.pairs.map fun p => (rd p.1, p.2.1, p.2.2)) v := by
  unfold PairSum.onK sumTerms
  rw [List.map_map]
  rfl

variable [Sizes] [Policy] [Request] [Token]

/-- The seven terms of the products' sum. c and pV play no part: the terms hang on om alone. -/
theorem prSum_terms (c : Law.NCells) (pV : Point) (om : E) :
    ((prSum c pV om).pairs.map fun p => (rd p.1, p.2.1, p.2.2)) = Law.tsP (rd om) := by
  show ((OnBytes.Desc.First.P6.rowProducts.zipIdx.map fun x => (om ^ x.2, x.1.1, x.1.2)).map
    fun p => (rd p.1, p.2.1, p.2.2)) = _
  unfold Law.tsP
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  show (rd (om ^ x.2), x.1.1, x.1.2) = _
  rw [Law.rd_pow]

/-- **The products' summand on four shown values**, in the verifier's text at one norm (NI = 1), as
Law/OpenedNorm.lean's prRow has it, reads as prSum's summand on the readings. c and pV play no part:
prSum takes them; its terms hang on om alone. -/
theorem summand_on (c : Law.NCells) (pV : Point) (om : E) (sh : Nat → E) :
    rd (sumTo 1 fun i => OnBytes.Desc.First.P6.summand (fun n => om ^ (7 * i + n))
      fun j => sh (4 * i + j)) = (prSum c pV om).onK fun j => rd (sh j) := by
  rw [Law.rd_sumTo, Finset.sum_range_one, onK_terms, prSum_terms]
  simp only [Nat.mul_zero, Nat.zero_add]
  exact Law.rd_summand (fun n => om ^ n) sh (rd om) fun n _ => Law.rd_pow om n

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.hide_truth
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.round_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.batch_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.batch_truth
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onK_product
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.product_on
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.shown_endK
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.onK_terms
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prSum_terms
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.summand_on
