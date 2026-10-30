-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/TidyPaid.lean: THE FIELD "tidy" OF THE STRUCTURE OF
FACTS ALONG THE FOLD (FoldFacts, Johnson/Desc/First/FoldFacts.lean), AT THE PROOF FILE's SEAT, IN
THAT STRUCTURE's OWN LETTERS, WITH ALL THREE OF descPure_reach_tidy's PREMISES STRUCK BY CALLS, BUT
FOR ONE TEST WITH CODE.
  flat_planOkT   F.planOk = true gives every sub-protocol's own test on the list of rounds: the
  FileDescription.planOk_ok (Johnson/Desc/RunLaws.lean), its clause blocks₁ (the road of planOk_of_file,
  which is declared nowhere in this library, and of Johnson/Desc/AtSeats/FoldFactsPaid.lean)
  tidy_paid      at Reach over c.blocksInOrder: the code table's lengths are in order by lengthsOk_of_pub
  (carried: Johnson/Desc/AtSeats/Fit/LengthsOfPub.lean): the maker of the public part refuses
  otherwise
  tidy_field     **∀ k a, RchAt F k a → a.1.2.failed = none → tidy4B a.1.2.st = true**: FoldFacts'
  field at Rch := RchAt F · at_ := (·.1); the fence "no mark" is not spent
hK2 (kind K2's sub-protocol with rounds keeps "tidy"): PAID:
tidyK2 (Johnson/ToldDescR/TidyK2.lean), called.
LEFT, ONE: F.planOk = true (a test with code; LPFD.Full.laidPOf_ok gives it from the laid form's
return: not called).
"REACHED" IS AN EXISTENTIAL: the rounds and columns are bound inside "there are": the conclusion
reads the state alone.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.TidyStart
import Johnson.ToldDescR.TidyK2
import Johnson.Desc.AtSeats.Fit.LengthsOfPub
import Johnson.Desc.RunLaws
import Johnson.Desc.Means.TestsBack
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Means (Tidy tidy4B tidy4B_iff)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Fits)
open VerifiableInference.Desc.Ground (By TidyStay)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw)
open ProofFile (Pub)

theorem flat_planOkT {o : ProofFile.SecondHashFunctionArgument} {Z : Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {c : Chain S ProofFile.Cl} {F : FileDescription ProofFile.Inst}
    (e : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    (hF : F.planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  subst e
  exact fun b hb => (((FileDescription.planOk_ok _).1 hF).blocks₁ b hb).1

theorem tidy_paid
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → Tidy a.2.st := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := descPure_reach_tidy ToldDesc.tidyK2 h
  exact ⟨Z, A, B, c, hZ, e, k (flat_planOkT e hF)
    (VerifiableInference.Desc.K13.Law.lengthsOk_of_pubT hZ)⟩

theorem tidy_field
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hF : F.planOk = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ (Str : Type) (k : ℕ) (a : (ProofFile.InstPub × S) × Str),
          RchAt (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) k a →
          a.1.2.failed = none → tidy4B a.1.2.st = true := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := tidy_paid h hF
  exact ⟨Z, A, B, c, hZ, e, fun _ n a hr _ => tidy4B_iff.2 (k n a.1 (rchAt_raw hr))⟩

end Meaning.K2
