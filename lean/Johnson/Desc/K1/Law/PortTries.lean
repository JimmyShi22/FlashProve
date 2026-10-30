-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PortTries.lean: the tie at the row, general in the function that makes the row;
the kind's own function meets it; a function that makes the empty row fails it.

Main names: PortLaw, portLaw; toyS, toy_tie; emptyRow_fails.

What is not claimed. The law names no verifier: it is an equation on a function that makes a row.
The try stands at a shape with one entry, which is its pad. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

/-- **The tie's form at the main table**, general in the function that makes the row. -/
def PortLaw (row : Msg → Nat → List E → E → Nat → E → OnBytes.Row) : Prop :=
  ∀ (cs : Codes) (s : OracleShape), Tie cs s → ∀ (e o : Nat) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ), ReadsOne cs s z β ρ →
    ∀ x : Fin s.mainRows × Fin (pMain cs s).ell,
      coefAt (row (Msg.of cs s) o z β 0 y) o .main (x.1.val + 2 ^ k1 s * x.2.val) =
        (portOmZ cs s e).row () ρ (Sum.inl x)

theorem portLaw : PortLaw sampleRow :=
  fun _ _ h e o z β y ρ r x => coef_port_main h e o z β y ρ r x

/-- The small place's one shape. -/
def toyS : OracleShape := { code := 0, mainRows := 1, mainDeg := 3, answers := 1 }

theorem toy_tie : Tie toyP.codes toyS := by
  refine ⟨rfl, toy_len, ?_, ?_⟩
  · simp [toyP, toyS, Blk.shapeOk]
  · simp only [Msg.padFits, Msg.of, Msg.e, toyS, toyP]
    simp
    exact Nat.one_le_two_pow

theorem toy_bits : bitsZ toyP.codes toyS = 0 := by
  rw [← v_bitsZ]
  decide

/-- **A function that makes the empty row fails the tie**: at the pad the library's row has the
factor, which is not 0. -/
theorem emptyRow_fails : ¬ PortLaw fun _ _ _ _ _ _ => {} := by
  intro h
  have r : ReadsOne toyP.codes toyS [] (E.ofTriple (1, 0, 0)) (fun _ => 0, 1) :=
    ⟨by rw [toy_bits]; exact Nat.zero_le _, fun t => by
      have h1 := t.isLt
      have h2 := toy_bits
      omega, readE_one⟩
  have hx : (0 : Nat) < (pMain toyP.codes toyS).ell := by decide
  have e := h toyP.codes toyS toy_tie 0 0 [] (E.ofTriple (1, 0, 0)) zeroE _ r
    (⟨0, Nat.one_pos⟩, ⟨0, hx⟩)
  rw [coefAt_empty] at e
  have hp : padP toyP.codes toyS (Sum.inl (⟨0, Nat.one_pos⟩, ⟨0, hx⟩)) := by
    refine ⟨rfl, rfl, ?_⟩
    show (pMain toyP.codes toyS).ell ≤ 0 + eachZ toyS
    decide
  have e2 : (portOmZ toyP.codes toyS 0).row () ((fun _ => 0, 1) :
      (Fin (bitsZ toyP.codes toyS) → GE) × GEˣ) (Sum.inl (⟨0, Nat.one_pos⟩, ⟨0, hx⟩)) =
      ((1 : GEˣ) : GE) * wZ toyP.codes toyS ⟨_, hp⟩ := mat_pad _ _ hp
  have e3 := e.trans e2
  rw [wZ_one toyP.codes toyS (Or.inr rfl)] at e3
  simp at e3

end VerifiableInference.Desc.K1
