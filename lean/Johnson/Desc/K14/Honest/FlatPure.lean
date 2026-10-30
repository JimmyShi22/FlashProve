-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/FlatPure.lean: the shared chain's list AT WHAT onlineDescription RETURNS
(Johnson/Desc/ProofFile/OnlineDescription.lean: the proof file's IOP as written in Lean) is the carried
chain's list at the planner's own parameters; so it has the form FlatOf
(Johnson/Desc/K14/Honest/FlatForm.lean).

Main names:
  flat_pure           **both**, by the library's shared_flat_pure and flat_retype_all
                      (Johnson/Desc/K14/Law/SharedFlat.lean), which write one list. What is returned
                      is written as the library writes it (fileDescBy): the types of a FileDescription's
                      states are fields of it

So whoever lays the shared chain's list as the carried chain's, at the planner's chains, at p14Of of
them and of the places' numbers, at the library's two proximity tests and closing and at the file's
type of claims, has laid the IOP's own shared list.

What is assumed: that the kind's text makes its eight at these parameters.

What is not claimed. Nothing on a run. Nothing on any property.

-/
import Johnson.Desc.K14.Honest.FlatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14.Law (shared_flat_pure flat_retype_all seatN)

/-- **At what onlineDescription returns, the shared chain's list is the carried chain's list**, at the
planner's own parameters; so it has the form FlatOf. What is returned is written as the library
writes it (fileDescBy): the types of a FileDescription's states are fields of it. -/
theorem flat_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) c ∧
      ∀ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
        blocks (p14Of Z.p.chains (beforePointOf N)) = some [b1, b2, b3, b4, b5, b6, b7, b8] →
        (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
          c).shared.blocksInOrder = ((chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N)) (tests N)
                     last).retype (Cl' := ProofFile.Cl)).blocksInOrder ∧
        FlatOf (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
          c).shared.blocksInOrder Z.p.chains b1 b2 b3 b4 b5 b6 b7 b8 := by
  obtain ⟨Z, N, B', c, hZ, hN, hF, hl⟩ := shared_flat_pure h
  refine ⟨Z, N, B', c, hZ, hN, hF, fun b1 b2 b3 b4 b5 b6 b7 b8 hb => ?_⟩
  have e : (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
      c).shared.blocksInOrder = ((chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N)) (tests N)
                 last).retype (Cl' := ProofFile.Cl)).blocksInOrder :=
    (hl b1 b2 b3 b4 b5 b6 b7 b8 hb).trans
      (flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb).symm
  exact ⟨e, e ▸ flatOf_carried _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.flat_pure
