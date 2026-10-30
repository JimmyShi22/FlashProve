-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/FoldFactsPaid.lean: THE FOLD's FACTS ON THE LEDGERS, ON "K13.pileWithin" AND ON
"K13.oneRow", AT THE PROOF FILE's SEAT, WITH THEIR LAST PREMISE BROUGHT DOWN TO ONE TEST WITH CODE: the
IOP as written in Lean passes its whole test on the list of rounds: F.planOk = true.

  flat_planOk      F.planOk = true gives every sub-protocol's own test: by FileDescription.planOk_ok
                   (Johnson/Desc/RunLaws.lean), its clause blocks₁: NO RUN IS ASKED. The road is that of
                   planOk_of_file (in a file that is not in this library), taken at
                   the letters of descPure_flat.
  ledgers_paid, within_paid   the two theorems of Johnson/Desc/AtSeats/StatementSeat.lean and WithinSeat.lean at it.

What is not claimed. That F.planOk = true at any files (LPFD.Full.laidPOf_ok gives it from the laid form's
return). Of "K13.pileMasks". Nothing on soundness.
-/
import Johnson.Desc.AtSeats.WithinSeat
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (LedgersFit WithinFact)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The whole test gives each sub-protocol's own. -/
theorem flat_planOk {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {c : Chain S ProofFile.Cl} {F : FileDescription ProofFile.Inst}
    (e : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    (hF : F.planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  subst e
  exact fun b hb => (((FileDescription.planOk_ok _).1 hF).blocks₁ b hb).1

/-- **Every ledger is in order at every reached state of the first chain.** -/
theorem ledgers_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → LedgersFit a.2.st := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := descPure_reach_ledgers h
  exact ⟨Z, A, B, c, hZ, e, k (flat_planOk e hF)⟩

/-- **"K13.pileWithin" and "K13.oneRow" accept at every reached state of the first chain.** -/
theorem within_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → WithinFact a.2 := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := descPure_reach_within h
  exact ⟨Z, A, B, c, hZ, e, k (flat_planOk e hF)⟩

#print axioms flat_planOk
#print axioms ledgers_paid
#print axioms within_paid

end Meaning.K2
