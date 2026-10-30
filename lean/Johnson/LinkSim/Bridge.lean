-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Bridge.lean: proofs of the three statements that connect a coin bijection to
exactness, and exactness to the link's clauses among the premises of index privacy.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  exactOfShift    proves Spec.exactOfShift (Johnson/LinkSim/SpecForm.lean): if bld returns the
                  symbols it is given, and outside U and the abort set a bijection from the honest
                  prover's coins onto the simulator's makes both runs disclose the same, the
                  simulator of that file's form satisfies ExactOff outside U. It uses
                  map_eq_of_bij (Johnson/LinkSim/Shift.lean) and dview_run_eq
                  (Johnson/LinkSim/SameView.lean).
  fieldsOfExact   proves Spec.fieldsOfExact (Johnson/LinkSim/Spec.lean): ExactOff outside U gives
                  the clause on the link's simulator, with any error term zL at least the
                  probability that a verifier message, its proof-of-work bits set to 0, is in U.
                  The other three clauses are premises and carry over unchanged.
  fieldsZero      proves Spec.fieldsZero (Johnson/LinkSim/Spec.lean): fieldsOfExact with U and Hid
                  empty, which gives the four clauses with both error terms zL and hL equal to 0.
                  The clauses on input oracles and on run values remain premises.

How it fits. Used in the proofs of homeExact and linkFieldsHome (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/Exact.lean applies exactOfShift, and linkFieldsHome applies fieldsZero.

Limits. All three statements are implications, for all parameters, and no particular honest prover
or simulator is given here.

Sources. It follows the pattern of Honest.HVZK.of_exact (Iop/InteractiveOracleProof.lean). A statement here is
covered by the note on sources in the head of Spec.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.SameView
import Johnson.LinkSim.Shift

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LinkSim
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Proves Spec.exactOfShift: if bld returns the symbols it is given, a coin bijection under which
both runs disclose the same, outside U and the abort set, gives ExactOff outside U for the simulator
made of the strategies. -/
theorem exactOfShift : Spec.exactOfShift := by
  intro X E Q Wt H valid Ks _ _ bld σ U hb hsh w x hv ρ hU hH
  by_cases hB : ρ ∈ H.Bad
  · have hw : ρ ∈ H.withheld w x := Or.inl hB
    unfold Honest.output simOfStrat
    rw [if_pos hw, if_pos hB]
  · have hw : ρ ∉ H.withheld w x := fun h => Or.elim h hB hH
    obtain ⟨φ, hφ, hs⟩ := hsh w x hv ρ hU hw
    unfold Honest.output simOfStrat
    rw [if_neg hw, if_neg hB]
    refine map_eq_of_bij φ hφ _ _ fun c => congrArg some ?_
    refine dview_run_eq Q x _ _ _ _ ρ (hs c) fun p hp => ?_
    exact (hb _ p _ (by unfold InteractiveOracleProof.extAns; rw [if_pos hp])).symm

/-- Proves Spec.fieldsOfExact: ExactOff outside U gives the link's clause on the simulator, with
error term zL bounding the probability that a verifier message with its proof-of-work bits set to 0
is in U. The other three clauses are premises and carry over unchanged. -/
theorem fieldsOfExact : Spec.fieldsOfExact := by
  intro I X lam L Bd aT aL a S W ok Gs U zL hL hE hU hext hrv hst
  refine ⟨hext, hrv, fun i r e r' e' hi he he' => le_trans ?_ hU, hst⟩
  refine (unif (Rho L.link.shape)).toOuterMeasure.mono fun ρ hρ => ?_
  by_contra hn
  refine hρ.2 ?_
  have h := hE (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ⟨hi, he, he', rfl⟩
    (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) hn hρ.1
  rw [hext] at h
  exact h

/-- Proves Spec.fieldsZero: ExactOff at all verifier messages and an empty Hid, with the clauses on
input oracles and on run values as premises, give the four link clauses with both error terms 0. -/
theorem fieldsZero : Spec.fieldsZero := by
  intro I X lam L Bd aT aL a S W ok Gs hE hH hext hrv
  refine fieldsOfExact I X lam L Bd aT aL a S W ok Gs ∅ 0 0 hE ?_ hext hrv ?_
  · show pr (unif (Rho L.link.shape)) (∅ : Set (Rho L.link.shape)) ≤ 0
    exact le_of_eq (pr_empty _)
  · intro i r e r' e' _ _ _
    rw [hH]
    show pr (unif (Rho L.link.shape)) (∅ : Set (Rho L.link.shape)) ≤ 0
    exact le_of_eq (pr_empty _)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.fieldsZero
#print axioms OnBytes.LinkSim.exactOfShift
#print axioms OnBytes.LinkSim.fieldsOfExact
