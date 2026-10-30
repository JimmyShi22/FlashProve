-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/K14Sits.lean: THE KIND SITS: IN THE PROOF FILE's WRITTEN DESCRIPTION THE
ENTRIES OF THE SHARED CHAIN's LIST OF BLOCKS AT THE KIND's EIGHT PLACES ARE THE CONSTANTS OF WHICH
THE KIND's LAWS SPEAK, AT THE PLAN's NUMBERS, UNDER ONE WRAPPER. Theorems.

OBJECT: whatever onlineDescription (Johnson/Desc/ProofFile/OnlineDescription.lean) returns. NO LETTER STANDS FOR THE
DESCRIPTION: F is onlineDescription's own value at the three public files.
  seatN Z N     the shared seat at the places' numbers N: sharedSeatAt's own term.
  shared_seat_of_pure   where onlineDescription returns F: the public part Z is made, the places' numbers N
                are made, and F IS fileDescBy at seatN Z N (by descPure_parts,
                Johnson/Desc/ProofFile/Law/PureMade.lean, and sharedSeatAt's text).
  k14_sits      **the row's sentence**: at that F, for k = 0 … 7: the entry 1 + k of the shared
                chain's list of blocks is b.retype, b the k-th of blocks (p14Of c before): THE
                CONSTANT OF EVERY LAW OF THE KIND ON THE SHARED CHAIN. c := the planner's chains;
                before := beforePointOf N: the plan's numbers.
  k14_sits_decides   and that entry decides as b does, and has b's rounds (rfl).
THE WRAPPER: retype alone: it carries a block to the description's type of claims; the decision, the
rounds and the name stand; the test on the plan asks beside that the block states no claim. NO OTHER
NAME OR PLACE, NO GUARD OF A MARK: the shared chain has no lot, no link and no maker's dress.
Entry 0 is the chain's front block; entries 9, 10, 11 are the two proximity tests and the end:
another kind's rows.
What is not claimed. That blocks (p14Of …) is some list: a premise (where it is none the chain holds
one block that fails its test on the plan: blocksOr). THE KIND's SECOND PART, at the last chain: not
here. THE KEY FILE's description: not here. That a maker's PIECE holds the entry: piece_retype_at
(Johnson/Desc/K14/Law/FlatRetype.lean). Nothing on soundness.

-/
import Johnson.Desc.K14.Law.FlatRetype
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Seat (tests last)
open VerifiableInference.OnPublicFiles

/-- The seat at places' numbers N. -/
def seatN (Z : ProofFile.Pub) (N : H2U.Places4) : ProofFile.SharedSeat :=
  sharedSeatOf Z.p.chains (beforePointOf N) (fun _ => tests N) [] last
    (OkD.AtC.beside Z.p.X Z.p.chains)

/-- Where onlineDescription returns a description, it is the maker's record at our seat. -/
theorem shared_seat_of_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) c := by
  obtain ⟨Z, _, _, c, A, B', hZ, -, -, -, -, -, hA, -, rfl⟩ := ProofFile.Law.descPure_parts h
  have hA' : sharedSeatAt Z = some A := hA
  unfold sharedSeatAt at hA'
  split at hA'
  · rename_i N hN
    obtain rfl := Option.some.inj hA'
    exact ⟨Z, N, B', c, hZ, hN, rfl⟩
  · cases hA'

/-- **The kind sits.** -/
theorem k14_sits {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) c ∧
      ∀ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
        blocks (p14Of Z.p.chains (beforePointOf N)) = some [b1, b2, b3, b4, b5, b6, b7, b8] →
        ∀ (k : Nat) (b : Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][k]? = some b →
          (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
            c).shared.blocksInOrder[1 + k]? = some (b.retype (Cl' := ProofFile.Cl)) := by
  obtain ⟨Z, N, B', c, hZ, hN, hF⟩ := shared_seat_of_pure h
  exact ⟨Z, N, B', c, hZ, hN, hF, fun b1 b2 b3 b4 b5 b6 b7 b8 hb k b hk =>
    flat_retype_get Z.p.chains (p14Of Z.p.chains (beforePointOf N)) b1 b2 b3 b4 b5 b6 b7 b8
      (tests N) last hb k b hk⟩

/-- The entry decides as the constant does, and has its rounds. -/
theorem k14_sits_decides (b : Block St Unit) :
    (b.retype (Cl' := ProofFile.Cl)).decide = b.decide ∧ (b.retype (Cl' := ProofFile.Cl)).rounds = b.rounds :=
  retype_decide b

end Desc.K14.Law
