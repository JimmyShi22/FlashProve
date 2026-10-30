-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/LinkAtLaw.lean: `ProofFile.onlineFirstChainAt` AND `ProofFile.linkAt` (LinkAt.lean) ARE THE
SEATED DESCRIPTION's OWN FIRST CHAIN AND LINKS. Statements with their proofs.

  `chainOfSeat_older`: the first chain does not read the stand-in for the second hash function: rfl.
  **`descPure_chain`**: onlineDescription o pol lay KL = .ok F gives Z, c, A, B with: the public part is Z;
    onlineFirstChainAt Z = .ok c; F = fileDescBy … A B … c. NO PREMISE BUT onlineDescription's RETURN. By
    `descPure_parts` (Law/PureMade.lean).
  `first_of`, `linkAt_of`, `flat_of`: at such a value: its first chain is c (rfl); linkAt Z m is
    that chain's link number m; its first chain's flat list is c.blocksInOrder.
Limits. Facts on the description's text. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.LinkAt
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)

/-- The first chain does not read the stand-in for the second hash function. -/
theorem chainOfSeat_older (Z : Pub) (o o' : SecondHashFunctionArgument) :
    chainOfSeat Z (pureSeat o Z) = chainOfSeat Z (pureSeat o' Z) := rfl

/-- **The seated description's first chain is `onlineFirstChainAt`'s.** -/
theorem descPure_chain {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
      pureRoad.pub o pol lay KL = .ok Z ∧ onlineFirstChainAt Z = .ok c ∧ onlineSharedChain Z = some A ∧
      onlineLastChain Z = some B ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c := by
  obtain ⟨Z, B₀, base, c, A, B, hZ, hB, -, -, hb, hc, hA, hB', hE⟩ := descPure_parts h
  refine ⟨Z, c, A, B, hZ, ?_, hA, hB', hE⟩
  show chainOfSeat Z (pureSeat emptySecondHashFunction Z) = .ok c
  rw [chainOfSeat_older Z emptySecondHashFunction o]
  unfold chainOfSeat partsOf
  rw [hB]
  show ((partsAt (pureSeat o Z) B₀).base.bind fun base =>
    chainBy Z base (partsAt (pureSeat o Z) B₀).frames (partsAt (pureSeat o Z) B₀).road) = .ok c
  rw [hb]
  exact hc

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat)
  (c : Chain S Cl)

theorem first_of : (fileDescBy o mk Z A B (fun s => s) (startS Z) c).first = c := rfl

theorem linkAt_of (h : onlineFirstChainAt Z = .ok c) (m : Nat) : linkAt Z m = c.links[m]? := by
  unfold linkAt
  rw [h]
  rfl

theorem flat_of : (fileDescBy o mk Z A B (fun s => s) (startS Z) c).first.blocksInOrder = c.blocksInOrder := rfl

end ProofFile.Law

#print axioms ProofFile.Law.chainOfSeat_older
#print axioms ProofFile.Law.descPure_chain
#print axioms ProofFile.Law.linkAt_of
