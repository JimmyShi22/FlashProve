-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/LabAtAll.lean: THE FIELD hLab OF WHAT IS STILL OWED FOR KIND K1's CONDITION
(`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED CONSTANT's HEAD,
IN THE FIELD's OWN TYPE: the closed test `labPB` (
Johnson/Desc/K1/Law/PlanesAtAll.lean: the output head's segment's list of arrays names the planes'
matrix's symbol array by the matrix's label) accepts. One statement with its proof: a call of
`names_tie_head` (Johnson/Desc/AtSeats/NamesTieHead.lean) at matrix 6: the head has four wide
matrices in scope, so the planes' matrix, number NHf + 2, is the seventh, an own one. PREMISE: the
head hA. A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed. That
the head can be met. Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.NamesTieHead
import Johnson.Desc.K1.Law.PlanesAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **The field hLab.** -/
theorem hLab_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    labPB Zp.made.p.built.links Zp.p.X = true := by
  have hX : Verify.publicOf Zl.pol Zl.KL (some Zl.lay) = .ok Zp.p.X := hA.pubOne
  have C := OnBytes.Road.Hd.core_of_scope hA.scope hA.reads hX
  have Bc := (OnBytes.Road.Hd.eleven_of_core hX C (OnBytes.Road.Hd.npOf Zp.p.X.hS)).1
  have hN : Zp.p.X.hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head).NHf
  unfold labPB
  rw [decide_eq_true_eq, hN]
  exact HeadNames.names_tie_head hA.scope hA.reads hA.laid.pub (μ := 4 + 2) (by omega)

end VerifiableInference.Desc.K1
