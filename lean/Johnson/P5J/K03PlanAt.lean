-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03PlanAt.lean: the kind "lookup" (K3): `K3PlanR` (Johnson/Desc/First/Look/K3Base.lean:
what K03_law asks of the public parameters alone, second form) AT THE CONSTANT, FROM THE ONE HEAD
AND THE DOOR's TWO ROWS.

Main names:
  `k3PlanR_of_plan`: the first form `K3Plan` (K3Means.lean) at what `Dl.up` sends, with the door's
    row on the digits, gives `K3PlanR`: five fields are one text; dig is the row itself.
  `k03_planR_at`: under `AtMgA OnBytes.secondHashFunction …`, `K3Asks.digRow` and `K3Asks.headRow` at the
    constant's public parameters: `K3PlanR (At.X Zp) (K3Asks.sentOf Zp) 𝔇.l3 (k3FloorAt (At.X Zp))`:
    one call of `k03_plan_of` (Johnson/Desc/First/Look/K03PlanOf.lean).
  `k03_hDl_sentOf`: "what `K3Asks.sentOf Zp` sends is what the constant's parameters send".

Limits: the two rows are premises: tests with code on the public parameters; that the verifier's
door evaluates them is not shown here. At secondHashFunction alone. Nothing on soundness by itself; nothing on
hiding.


-/
import Johnson.Desc.First.Look.K03PlanOf
import Johnson.Desc.First.Look.K3Base
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- **The second form from the first and the door's row.** -/
theorem k3PlanR_of_plan {Cells Tok : Type} {X : Verify.Public} {Dl : Desc.K3Asks.Sent}
    {L : K3Letters Cells Tok} {pp floor : ℕ}
    (h : letI := k3SizesAt X
      K3Plan X Dl.up L pp floor)
    (hd : Desc.K3Asks.digRow X Dl = true) :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    K3PlanR X Dl L floor :=
  letI := k3SizesAt X
  letI := k3PolicyAt X
  ⟨hd, h.att, h.lay, h.head, h.head24, h.entries⟩

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem k03_hDl_sentOf (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (VerifiableInference.Desc.K3Asks.sentOf Zp).up = (h.toAtMg.𝔇 h.𝔇).sent := rfl

/-- **`K3PlanR` at the constant.** -/
theorem k03_planR_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hHead : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true) :
    letI := k3SizesAt (At.X Zp)
    letI := k3PolicyAt (At.X Zp)
    K3PlanR (At.X Zp) (VerifiableInference.Desc.K3Asks.sentOf Zp) (h.toAtMg.𝔇 h.𝔇).l3
      (k3FloorAt (At.X Zp)) := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have p := k03_plan_of h.toAtMg.scope h.toAtMg.reads O hDig hHead h.toAtMg.laid.planOk
    (h.toAtMg.𝔇 h.𝔇).l3
  rw [O.W] at p
  exact k3PlanR_of_plan p hDig

end P5J

#print axioms VerifiableInference.OnPublicFiles.k3PlanR_of_plan
#print axioms P5J.k03_hDl_sentOf
#print axioms P5J.k03_planR_at
