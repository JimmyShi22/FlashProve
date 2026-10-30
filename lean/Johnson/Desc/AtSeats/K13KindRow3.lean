-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-



Johnson/Desc/AtSeats/K13KindRow3.lean: the premise hbase of kind K13's row for the join,
brought down to two small numbers.
hbase reads: the tree of the index masks' oracle message is sent in front of K13's place: hA.𝔇.N.index.1 < nTrees ((D.at …).ds₁.take (inFront355 cF)): a sum over some 48,270 rounds of the data.
  data_written   under the head the data ARE the written data of the full size: D = Johnson.G.writtenPFull: the proof of laidPOf_written (Johnson/Desc/Laid/ProofFullScope.lean), which spends «data» and «asks» alone:
                 both are fields of the head's LaidAt.
  hbase_atAll    so, by hbase_of (Johnson/HB/LLHARD/HBaseWritten.lean: the first round of the written data sends two trees, and a longer stretch sends no fewer): hbase, out of
                 hi : hA.𝔇.N.index.1 ≤ 1 · hn : 1 ≤ inFront355 cF.
ONE PREMISE ON THE DATA HAS GONE AND TWO ON THE PLAN HAVE COME: THE COUNT RISES BY ONE: what is won: neither reads the data; each is a small number off the public part (hi) or off the
description's first sub-protocols (hn).
What is not claimed. That any premise can be met. No member of h.Kind. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13KindRow2
import Johnson.HB.LLHARD.HBaseWritten
import Johnson.Desc.Laid.ProofFullScope

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
include hA

theorem data_written : D = Johnson.G.writtenPFull :=
  Except.ok.inj (hA.laid.data.symm.trans
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Zl hA.scope (LPFD.asks_written hA.laid.asks)).2.2)

theorem hbase_atAll (hi : hA.𝔇.N.index.1 ≤ 1) (hn : 1 ≤ inFront355 cF) :
    hA.𝔇.N.index.1 < nTrees ((D.at frS.P.T.a).ds₁.take (inFront355 cF)) := by
  rw [P5J.LaidAt.atDepth hA.scope hA.laid]
  have e := data_written hA
  subst e
  exact hbase_of hi hn

end

end VerifiableInference.Desc.K13.Law
