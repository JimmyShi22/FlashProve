-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13KindRow.lean: two small facts at the closed constant hA.𝔇. Kind K13's row
for the join of the kinds (Johnson/Desc/AtSeats/K13KindRowA.lean) calls both.



  smpReads_atAll   SmpReads hA.𝔇.smp: the closed reader of samples IS smpNamed (At.cs Zp) (At.seats Zp) by unfolding: smpReads_named.
  decBlind_atAll   DecBlind hA.𝔇.decT: the closed decoder reads the public part alone: by rfl.
What is not claimed. That the head hA can be met. No member of h.Kind. Nothing on soundness.

-/
import Johnson.Desc.Sound.KindEnd
import Johnson.Desc.AtSeats.K13LawAtThreeT
import Johnson.Desc.K13.Law.SmpNamedReads
import Johnson.Top.H0.Walk.ReachHands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn mgAll MgData CellsQ mgBase threeCap)
open Johnson.Desc.First.Walk.Tied (RchAt)

open Johnson.Desc.First.Walk.Tied (handsOn_map)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)

theorem smpReads_atAll : SmpReads hA.𝔇.smp :=
  smpReads_named (cs := P5J.At.cs Zp) (seats := P5J.At.seats Zp)

theorem decBlind_atAll : DecBlind hA.𝔇.decT := fun _ _ _ _ => rfl

end

end VerifiableInference.Desc.K13.Law
