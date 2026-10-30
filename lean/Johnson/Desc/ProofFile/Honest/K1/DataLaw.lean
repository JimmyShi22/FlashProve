-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/DataLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: WHERE NO COIN STANDS rowsR (Honest/K1/Coins.lean) LAYS WHAT THE CALLER's DATA SAYS.
Statements and proofs.

  no_word       a sampled message has no coin of step (2)
  no_pad        off the places of padInMain (Honest/RowData.lean) the four tests by which rowsR
                tells a pad's place do not all hold
  main_data_e, main_data_f   at a sampled message, at r < mainRows and j < ell, off padInMain's
                places: the main entry (r, j) is what data k r j says: over the extension field an
                element of it, or an element of the base field embedded; over the base field an
                element of it; else 0

The converse, that at a pad's place the coin stands whatever data says, is pad_coin_e and _f
(Honest/K1/CoinLaw.lean), at the places (mainRows - 1, ell - pad + i), i < pad. That these are
padInMain's members is read off the two texts: no statement here says it.

No test on the job is asked: the step from padInMain's places to rowsR's four tests holds also where
the pad is longer than its row.

Limits. A message without a sample is not spoken of (there a word with main rows holds coins at all
its entries). What is WRITTEN where: no sentence on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Desc.ProofFile.Honest.RowData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- A sampled message has no coin of step (2). -/
theorem no_word (codes : Codes) (s : OracleShape) (R : Option Ride) (ha : s.answers ≠ 0) :
    ((stepsOf codes s R).word != 0) = false := by
  have : (s.answers == 0) = false := beq_eq_false_iff_ne.2 ha
  simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false, bne_self_eq_false]

/-- Off padInMain's places rowsR's four tests do not all hold. -/
theorem no_pad (codes : Codes) (s : OracleShape) (R : Option Ride) (r j : Nat)
    (hp : (r, j) ∉ padInMain (codes.base.getD s.code default).ell s) :
    ((stepsOf codes s R).pad != 0 && r + 1 == s.mainRows &&
      decide ((codes.base.getD s.code default).ell - (stepsOf codes s R).pad ≤ j) &&
      decide (j < (codes.base.getD s.code default).ell)) = false := by
  by_contra hc
  have hc' : ((stepsOf codes s R).pad != 0 && r + 1 == s.mainRows &&
      decide ((codes.base.getD s.code default).ell - (stepsOf codes s R).pad ≤ j) &&
      decide (j < (codes.base.getD s.code default).ell)) = true := eq_true_of_ne_false hc
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hc'
  by_cases hz : (s.maskRows == 0 && s.answers != 0) = true
  · have hpad : (stepsOf codes s R).pad = (if s.mainDeg == 3 then 1 else 3) * s.answers := by
      simp only [stepsOf, hz, if_true]
    have hz' := hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hz'
    have hcond : (s.maskRows != 0 || s.mainRows == 0) = false := by
      have a : (s.maskRows != 0) = false := by rw [hz'.1]; rfl
      have b : (s.mainRows == 0) = false := beq_eq_false_iff_ne.2 (by omega)
      rw [a, b]
      rfl
    apply hp
    unfold padInMain
    rw [hcond]
    simp only [Bool.false_eq_true, if_false, List.mem_map, List.mem_range, Prod.mk.injEq]
    rw [hpad] at h2 h0
    exact ⟨j - ((codes.base.getD s.code default).ell -
      (if s.mainDeg == 3 then 1 else 3) * s.answers), by omega, by omega, by omega⟩
  · exact h0 (by simp only [stepsOf, hz, Bool.false_eq_true, if_false])

variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
  (cs : Cs (dueR P ride)) (k : Nat)

/-- **Over the extension field.** -/
theorem main_data_e (r j : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell)
    (ha : (shapeAt P k).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (P.codes.base.getD (shapeAt P k).code default).ell (shapeAt P k)) :
    (rowsR P ride data cs k).mainE r j =
      match data k r j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  have n1 : decide ((shapeAt P k).mainRows ≤ r) = false := decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false :=
    decide_eq_false (by omega)
  simp only [rowsR, h3, n1, n2, no_word P.codes (shapeAt P k) (ride k) ha,
    no_pad P.codes (shapeAt P k) (ride k) r j hp, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, if_false, Option.map_none]
  rcases data k r j with _ | (x | x) <;> rfl

/-- **Over the base field.** -/
theorem main_data_f (r j : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = false)
    (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell)
    (ha : (shapeAt P k).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (P.codes.base.getD (shapeAt P k).code default).ell (shapeAt P k)) :
    (rowsR P ride data cs k).mainF r j =
      match data k r j with
      | some (.inl x) => x
      | _ => 0 := by
  have n1 : decide ((shapeAt P k).mainRows ≤ r) = false := decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false :=
    decide_eq_false (by omega)
  simp only [rowsR, h3, n1, n2, no_word P.codes (shapeAt P k) (ride k) ha,
    no_pad P.codes (shapeAt P k) (ride k) r j hp, Bool.or_self, Bool.false_eq_true, if_false,
    Option.map_none]
  rcases data k r j with _ | (x | x) <;> rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.no_word
#print axioms ProofFile.Honest.K1.no_pad
#print axioms ProofFile.Honest.K1.main_data_e
#print axioms ProofFile.Honest.K1.main_data_f
