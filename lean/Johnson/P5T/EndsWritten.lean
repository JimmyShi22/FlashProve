-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/EndsWritten.lean: the head's named test `endsThere` (Johnson/P5J/GroupsPaid.lean: the
index masks' message's seat and W's are seats of entries with a sample) AT THE WRITTEN VALUES OF THE
FULL SIZE, and in the goals' scope. A definition and five statements with their proofs.

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM AND ITS TIE: the first chain's seats · `psFull` · the
numbers' fields index and w · `N0Full`'s (Johnson/P5T/PlanSeatsFull.lean): both by `seats_in_scope`
(Johnson/P5T/PlanSeatsTie.lean): compiled. The chain cF falls out: the two fields are the core's, by
the make.

  `endsAt ps N`: the test's own text at two letters.
  `ends_written`: (W). `ends_rejects`: (N): without the entries of W's sending, and without those of
    the first sending, it rejects.
  `ends_in_scope`: (Z): `endsThere Z cF = true` from: the scope; the public part is made; the
    verifier's test `madePinnedAt` accepts; the value is laid.
  `laid_of_at`: the structure `LaidAt` (Johnson/P5J/LaidOpens.lean) gives back "the value is laid".
  `ends_at_name`: **the same in the letters of the law that asks the test**: from the scope,
    `LaidAt` and ONE PREMISE MORE: hy, an accept of `madePinnedAt`: no field of `LaidAt` pays it
    today: it is a row of the verifier's list of thirteen tests (ProofAsksFirstThirteenTests.lean): where that
    list is laid, the field `asks` pays it.
    (Where this and lean/THEOREM.md differ, the page holds.)
By evaluations in Lean's kernel (`decide +kernel`): the first two. The counts that make them say
something: `psFull_whole`, `psFull_roles`.

Limits. Nothing on soundness.
-/
import Johnson.P5T.PlanSeatsTie
import Johnson.P5J.GroupsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.PlanWritten (madePinnedAt)

/-- The test's own text, at a list of seats and at numbers: the index masks' message's seat and W's
are seats of entries with a sample. -/
def endsAt (ps : List PSeat) (N : Numbers) : Bool :=
  ((ps.filter (·.smpd)).map (·.seat)).contains N.index &&
    ((ps.filter (·.smpd)).map (·.seat)).contains N.w

/-- **(W)** At the written values it accepts. -/
theorem ends_written : endsAt psFull N0Full = true := by decide +kernel

/-- **(N)** Without the entries of W's sending it rejects; and without those of the first. -/
theorem ends_rejects :
    (endsAt (psFull.filter fun p => p.label != "W") N0Full,
      endsAt (psFull.filter fun p => p.send != 0) N0Full) = (false, false) := by decide +kernel

/-- **(Z)** In the goals' scope the head's named test accepts, at every chain cF. -/
theorem ends_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (cF : Chain P5J.TS ProofFile.Cl) :
    P5J.At.endsThere Z cF = true := by
  show endsAt (planSeats Z Z.D.1) (numbersOf (planSeats Z Z.D.1)) = true
  rw [(seats_in_scope hW h hy hl).1]
  exact ends_written

/-- What "laid, at the term's letters" holds gives back "the value is laid". -/
theorem laid_of_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (L : P5J.LaidAt o pol lay KL D r Zp Np cF) : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r) := by
  rw [L.run]
  exact LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks

/-- **The head's named test, in the letters of the law that asks it.** hy: an accept of the
verifier's test on the sizes, the lists of rounds and the sendings. -/
theorem ends_at_name {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (hZ : VerifierAndGoals.InScope Z = true) (_hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    P5J.At.endsThere Zp cF = true :=
  ends_in_scope hZ L.pub hy (laid_of_at L) cF

end P5T

#print axioms P5T.ends_written
#print axioms P5T.ends_rejects
#print axioms P5T.ends_in_scope
#print axioms P5T.laid_of_at
#print axioms P5T.ends_at_name
