-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/LinkAtOpen.lean: LINK NUMBER m OF THE PROOF FILE's FIRST CHAIN "OFF THE
PUBLIC PART" (ProofFile.linkAt, Johnson/Desc/ProofFile/LinkAt.lean) IS LINK NUMBER m OF THE CHAIN c OF AN
OPENING OF THE IOP AS WRITTEN IN LEAN (IM.Open, Johnson/IMR/SeatOpen.lean). General in
the letter o for our second, non-standard hash (built on BLAKE2b's compression function).

  `chainOfSeat_open`: at an opening: chainOfSeat Z (pureSeat o Z) = .ok c: its fields made, places
    and chain, step by step.
  `chainOfSeat_idle`: the chain does not read the seat's field older: at the stand-in emptySecondHashFunction it
    is the chain at o: by unfolding. KIN: that file's head names a lemma
    (chainOfSeat_older, Law/LinkAtLaw.lean).
  **`linkAt_open`**: at an opening, every m: ProofFile.linkAt Z m = c.links[m]?. Premise: O.
WHO SPENDS IT: the line lk of the structure K4Fill (Johnson/Road/K4/K4RowWideScope.lean), where the
composed meaning's parameter lk is fun m => ProofFile.linkAt Z m.
Limits. That there is an opening is shown by no theorem. K04_law, the law of K4's sub-protocol
itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Desc.ProofFile.LinkAt
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At an opening the chain off the seat is the opening's. -/
theorem chainOfSeat_open (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ProofFile.chainOfSeat Z (ProofFile.pureSeat o Z) = .ok c := by
  unfold ProofFile.chainOfSeat ProofFile.partsOf
  rw [O.made]
  show ((ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).base.bind fun base =>
    ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road) = .ok c
  rw [O.places]
  exact O.chain

/-- The chain does not read the seat's field older. -/
theorem chainOfSeat_idle (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) :
    ProofFile.chainOfSeat Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) = ProofFile.chainOfSeat Z (ProofFile.pureSeat o Z) :=
  rfl

/-- **At an opening: the link off the public part is the opening's chain's.** -/
theorem linkAt_open (O : IM.Open o pol lay KL F Z Bs base c A B) (m : ℕ) :
    ProofFile.linkAt Z m = c.links[m]? := by
  unfold ProofFile.linkAt ProofFile.onlineFirstChainAt
  rw [chainOfSeat_idle o Z, chainOfSeat_open O]
  rfl

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.chainOfSeat_open
#print axioms OnBytes.Road.K4.Riders.chainOfSeat_idle
#print axioms OnBytes.Road.K4.Riders.linkAt_open
