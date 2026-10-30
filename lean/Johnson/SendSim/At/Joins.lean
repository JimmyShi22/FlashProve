-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Joins.lean: two implications that carry exact from the level of rows to a Seated
side. Spec.rowsExact implies Spec.exactOut, and Spec.exactOut implies Spec.sendExactAt. It claims no
property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves.
  exactOut_of_rows    Spec.rowsExact implies Spec.exactOut, by what the sender discloses and the
                      simulator outputs coin by coin (showsAt, tellsAt).
  sendExactAt_of_out  Spec.exactOut implies Spec.sendExactAt, ExactAt at every
                      Seated side, with On := True and the bound budAt: such a side has one member,
                      which spends and carries nothing.
  rounds_fst          At a side σ that is Seated at J, the rounds of the member memberAt σ J are all
                      the rounds of σ's sub-protocol.

Limits. Implications only: their premises are named propositions that this file does not prove, so
it proves no equation between distributions by itself.

How it fits. Spec.rowsExact and Spec.sendExactAt are stated in Johnson/SendSim/At/Sim.lean,
Spec.exactOut in Johnson/SendSim/At/Member.lean; showsAt and tellsAt are proved in
Johnson/SendSim/At/Shows.lean. Johnson/SendSim/At/ExactAt.lean applies the two implications to the
theorem rowsExact (Johnson/SendSim/At/RowsExact.lean), which gives exactOut and sendExactAt.
rounds_fst is also used for the field fresh (Johnson/SendSim/At/JoinFresh.lean,
Johnson/SendSim/At/FreshWide.lean).
-/
import Johnson.SendSim.At.Shows

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- At a side σ that is Seated at J, the rounds of the member memberAt σ J are all the rounds of σ's
sub-protocol. -/
theorem rounds_fst {σ : Side S Cl V W X Pb} {J : SendJob W X} (h : Seated σ J) :
    (memberAt σ J).rounds.map (·.1) = σ.block.rounds := by
  have hfit := h.fits
  simp only [Side.fits, Side.half, Placed.rounds, h.row, Bool.and_eq_true, beq_iff_eq] at hfit
  have hr : σ.block.rounds.length = 2 := hfit.1.2.symm
  have ho : σ.block.oracles.length = 2 := hfit.2.trans hr
  obtain ⟨a₁, a₂, ha⟩ : ∃ a₁ a₂, σ.block.rounds = [a₁, a₂] := by
    match σ.block.rounds, hr with
    | [a₁, a₂], _ => exact ⟨a₁, a₂, rfl⟩
  obtain ⟨o₁, o₂, hoo⟩ : ∃ o₁ o₂, σ.block.oracles = [o₁, o₂] := by
    match σ.block.oracles, ho with
    | [o₁, o₂], _ => exact ⟨o₁, o₂, rfl⟩
  show ((σ.block.rounds.zip σ.block.oracles).take 2).map (·.1) = σ.block.rounds
  rw [ha, hoo]
  rfl

/-- Spec.rowsExact implies Spec.exactOut. The premise is proved as rowsExact in
Johnson/SendSim/At/RowsExact.lean. -/
theorem exactOut_of_rows (H : Spec.rowsExact) : Spec.exactOut := by
  intro S Cl V W X Pb φ σ J h m front ds asks hd hb
  have e1 : (fun c => σ.shows φ (memberAt σ J) (c, (), ()) m ds asks) = fun c =>
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks c)
      else none := funext fun c => showsAt S Cl V W X Pb φ σ J h m ds asks c hd
  have e2 : (fun c => (memberAt σ J).tells φ c m.st.input front ds asks) = fun c =>
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (fun _ _ _ => none) ds asks c)
      else none := funext fun c => tellsAt S Cl V W X Pb φ σ J h m.st.input front ds asks c hd
  rw [e1, e2]
  by_cases hf : sendFits J.P J.ride = true
  · simp only [hf, if_true]
    have := H J.P J.first J.ride (J.data m.st.input (frontOf m)) (fun _ _ _ => none) ds asks hf
      (h.draws ds hd).1 (h.draws ds hd).2 hb
    have c1 := congrArg (PMF.map some) this
    rw [PMF.map_comp, PMF.map_comp] at c1
    exact c1
  · have hf' : sendFits J.P J.ride = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, if_false]
    rfl

/-- Spec.exactOut implies Spec.sendExactAt, ExactAt at every Seated side, with On :=
True and the bound budAt. The premise is proved as exactOut in Johnson/SendSim/At/ExactAt.lean. -/
theorem sendExactAt_of_out (H : Spec.exactOut) : Spec.sendExactAt := by
  intro S Cl V W X Pb φ σ J chain firstTree h u hu ca m front ds asks _ _ hd hb _ _
  rw [members_seated h, List.mem_singleton] at hu
  subst hu
  rw [rounds_fst h] at hd
  have := H S Cl V W X Pb φ σ J h m front ds asks hd hb
  refine Eq.trans ?_ this
  have e : (fun c : Cs (dueR J.P J.ride) × Unit =>
      σ.shows φ (memberAt σ J) (c.1, c.2, ca) m ds asks) =
      (fun c => σ.shows φ (memberAt σ J) (c, (), ()) m ds asks) ∘ Prod.fst := rfl
  show (Prob.unif (Cs (dueR J.P J.ride) × Unit)).map (fun c =>
    σ.shows φ (memberAt σ J) (c.1, c.2, ca) m ds asks) = _
  rw [e]
  exact (PMF.map_comp Prod.fst _ _).symm.trans (congrArg (PMF.map _) Prob.map_fst_unif)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rounds_fst
#print axioms OnBytes.SendSim.At.exactOut_of_rows
#print axioms OnBytes.SendSim.At.sendExactAt_of_out
