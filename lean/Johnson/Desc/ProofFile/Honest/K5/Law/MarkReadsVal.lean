-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarkReadsVal.lean: CONDITIONAL: WHAT THE SILENCE OF THE MARK
`mkReads` (Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean) GIVES AT THE STATE IN FRONT OF THE
BATCHING, AT VALUES: `Live2V` (Johnson/Desc/K5/Honest/Law/LiveValAt.lean) where `mkReads_live` has
`Live2`: the two tables' weights do not read 0; their lengths are not 0 and divide the plan's
matrices' numbers of rows.

Limits. As `mkReads_live` and `live_at_batchV`. No sentence on a measure stands here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkReads
import Johnson.Desc.K5.Honest.Law.LiveVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (readRounds Chal Reads Live2V live_at_batchV)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **WHAT THE MARK's SILENCE GIVES, AT VALUES.** Conditional: as `mkReads_live`. -/
theorem mkReads_liveV {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4)
    (hlen : ∀ n ∈ readRounds a.own (Att.P.parCOf a).geo, n < own.length)
    (hs : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test fr own = none) :
    Live2V (Att.P.parCOf a).geo a.mats s9 :=
  live_at_batchV h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 ⟨zk, own⟩ hc
    (mkReads_silent (2 * g + 1) zk hlen hs)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mkReads_liveV
