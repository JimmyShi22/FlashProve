-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchGJobs.lean: the closing of a segment (K10): the clause on data in the field stand of `TieByShared`
(Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean) at the base prover's own jobs of the shared kind (K1): `jobTwoAt`, the first
segment's opening, and `jobLaterAt`, a segment's moment 1 or 2 (AtFullSide/K1/RecordAtBase.lean), at the filling `widerRows`, the
base prover's readers and `witB`. In the terms of the premise hdata of `tieByShared_later_head` and `tieByShared_open_head`
(AtFullSide/K10/ShrHead.lean), but for the stand: of a stand these two read one fact, hfr: the challenges in front of the sending
have been heard.

  `pos_written`, `pos_bent`   the place that `shrPosLater` (ShrSeats.lean) states is the place by the written segment's first sending
  **`data_job_later`**, **`data_job_open`**   the clause

By `data_later_head`, `data_first_head` (Pay/XchGHead.lean); `plan_later`, `plan_two` (ScriptPublic.lean).

Limits. The hypothesis on the head and the maker's return are premises. The full size and the older hash alone. Shapes and which call
of the filling is read: nothing on what the data hold.
-/
import AtFullSide.K10.ScriptPublic
import AtFullSide.K10.ShrSeats
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchGHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K1 (noL)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest ProofFile.Honest.K10
open ProofFile.Honest.K1 (jobTwoAt jobLaterAt witB LocB)
open ProofFile.Honest.K2 (asRow)
open Johnson.Prover.Send (shapeAt)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The place that `shrPosLater` states is the place by the written segment's first sending. -/
theorem pos_written : ((List.range 25).all fun l => shrPosLater l == some (laterPos l)) = true := by
  decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: against the place one further on the test says no at every segment. -/
theorem pos_bent : ((List.range 25).any fun l => shrPosLater l == some (laterPos l + 1)) = false := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE CLAUSE ON DATA AT A LATER MOMENT's JOB.** -/
theorem data_job_later (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {l : Nat} (hl : l < 25) (d : Bool) {Qc : Par} (hQ : Qc.link = l) {c lo : Nat}
    (hpos : shrPosLater l = some c) (hlo : lo = c + (if d then 1 else 0)) {w : LocB W₀}
    {heard : List Fmt.Drawn} (hfr : 0 + roundsTo cF.blocksInOrder (noL l d) ≤ heard.length) {n : Nat}
    (hn : n < 1) (ca : CsAll (closeCarries ⟨Qc, borneAt A.Z Qc⟩)) (a : ProofFile.Honest.K2.Law.Laid) (nn : Nat)
    (hL : LotMember (fun v : LocB W₀ => ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩) (widerRows S A.Z A.G) A.Z
      A.G Qc w heard ca (lo + n) a nn) :
    a.1 = shapeAt (jobLaterAt S A.Z A.G l d).P n ∧
      a.2 = fun r i => asRow ((shapeAt (jobLaterAt S A.Z A.G l d).P n).mainDeg == 3)
        ((jobLaterAt S A.Z A.G l d).data (witB I A.Z w)
          { heard := heard.take (0 + roundsTo cF.blocksInOrder (noL l d)), own := (), seen := .bare [] } n r i) := by
  obtain rfl : n = 0 := by omega
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hc : c = laterPos l := by
    have t := beq_iff_eq.1 (List.all_eq_true.1 pos_written l (List.mem_range.2 hl))
    exact Option.some.inj (hpos.symm.trans t)
  have hidx : lo + 0 = laterPos l + tOf d := by
    rw [hlo, hc]
    rfl
  rw [hidx, eG] at hL
  obtain ⟨k1, k2⟩ := data_later_head h O hl d hQ _ S
    (fr := 0 + roundsTo cF.blocksInOrder (noL l d)) (by omega) hfr hL
  rw [plan_later h hA l d]
  refine ⟨k1, ?_⟩
  rw [k2, eG]
  rfl

/-- **THE CLAUSE ON DATA AT THE OPENING's JOB**, messages 0, 1, 2. -/
theorem data_job_open (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {Qc : Par} (hQ : Qc.link = 0) {w : LocB W₀}
    {heard : List Fmt.Drawn} (hfr : 0 + roundsTo cF.blocksInOrder 2 ≤ heard.length) {n : Nat}
    (hn : n < 3) (ca : CsAll (closeCarries ⟨Qc, borneAt A.Z Qc⟩)) (a : ProofFile.Honest.K2.Law.Laid) (nn : Nat)
    (hL : LotMember (fun v : LocB W₀ => ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩) (widerRows S A.Z A.G) A.Z
      A.G Qc w heard ca (0 + n) a nn) :
    a.1 = shapeAt (jobTwoAt S A.Z A.G).P n ∧
      a.2 = fun r i => asRow ((shapeAt (jobTwoAt S A.Z A.G).P n).mainDeg == 3)
        ((jobTwoAt S A.Z A.G).data (witB I A.Z w)
          { heard := heard.take (0 + roundsTo cF.blocksInOrder 2), own := (), seen := .bare [] } n r i) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [Nat.zero_add, eG] at hL
  obtain ⟨k1, k2⟩ := data_first_head h O hQ _ S (fr := 0 + roundsTo cF.blocksInOrder 2) hn hfr hL
  rw [plan_two h hA]
  refine ⟨k1, ?_⟩
  rw [k2, eG]
  rfl

end AtFullSide.K10

#print axioms AtFullSide.K10.pos_written
#print axioms AtFullSide.K10.pos_bent
#print axioms AtFullSide.K10.data_job_later
#print axioms AtFullSide.K10.data_job_open
