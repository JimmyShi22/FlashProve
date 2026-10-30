-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/KeptSeatsLeft.lean: code switching (K2): THE FIELD «keptSeats» OF T14Left
(Johnson/P1K2R/TiesOneFour.lean: the named test keptSeatsB at the constant's letters) FALLS: it
follows from T14Left's own head · pinned · cut · laidL · row, and «the structure of parameters'
description's first chain tells what the chain c tells».
  told_flat        what a list of sub-protocols tells, as one list, is the flattening of what each
                   tells
  t14_keptSeats    the field, by keptSeats_const
                   (Johnson/Top/H0/K2Ties/KeptSeatsConst.lean: by Lean's kernel at the 25 written
                   rows), at: AtWritten (at_written) · the
                   written cut (toldOf_of_cut) · the written sendings (sends_in_scope, under the
                   pin) · At.laid? Z, which is laidAtCodes Z.first.codes Z.made.proof.1 by its text
  t14_hG_at        hG at the term P5J.F0T o Z Np c: by the term's own text (rfl)
LEFT IN ITS PLACE, BY NAME: hG : oraclesOf G.first.blocksInOrder = oraclesOf c.blocksInOrder.
LIMITS. A join. The 25th written row keeps no member: there the test accepts idly (by report, not
shown here). No premise is shown met at a real value: no example. No soundness is claimed.
-/
import Johnson.P1K2R.TiesOneFour
import Johnson.Top.H0.K2Ties.KeptSeatsConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription oraclesOf)
open VerifiableInference.Desc.First.K2Ties (at_written toldFull toldOf_of_cut keptSeats_const)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open P5J (LaidAt)
open ProofFile (Cl)

theorem told_flat {St Cl' : Type} (bs : List (Block St Cl')) :
    oraclesOf bs = (VerifiableInference.Desc.First.toldOf bs).flatten := by
  unfold oraclesOf VerifiableInference.Desc.First.toldOf
  rw [List.flatMap_def]
  simp

theorem t14_keptSeats {Xi : Type} {G : FileDescription Xi} {Pb : VerifierAndGoals.PublicFiles} {Dw : WholeD}
    {rn : LPFD.Full.RunPF} {Z : ProofFile.Pub} {Np : H2U.Places4} {c : Chain First.S Cl}
    (hS : VerifierAndGoals.InScope Pb = true)
    (La : LaidAt OnBytes.secondHashFunction Pb.pol Pb.lay Pb.KL Dw rn Z Np c)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hG : oraclesOf G.first.blocksInOrder = oraclesOf c.blocksInOrder)
    {L : Laid} (hl : laidAtCodes Z.first.codes Z.made.proof.1 = some L) {m : ℕ} {r : SwRow}
    (hr : tableFullLit[m]? = some r) :
    keptSeatsB G r.cs L (P5J.At.seats Z) 83 r.lo (seatOld (P5J.At.N Z c) m r) r.kept
      (K2.oldsAt (m + 1)) = true :=
  keptSeats_const (at_written hS La hy)
    (by rw [hG, told_flat, toldOf_of_cut hcut])
    (by rw [VerifiableInference.PlanWritten.Joined.sends_in_scope hS La.pub hy]; rfl) hl hr

/-- hG at the term `P5J.F0T o Z Np c`. -/
theorem t14_hG_at (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4) (c : Chain First.S Cl) :
    oraclesOf (P5J.F0T o Z Np c).first.blocksInOrder = oraclesOf c.blocksInOrder := rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.told_flat
#print axioms VerifiableInference.Desc.First.K2Caller.t14_keptSeats
#print axioms VerifiableInference.Desc.First.K2Caller.t14_hG_at
