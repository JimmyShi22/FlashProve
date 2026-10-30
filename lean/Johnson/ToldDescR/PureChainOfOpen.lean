-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/PureChainOfOpen.lean: no soundness is claimed.
Cut out of MergeAtLinkAt.lean, so that a statement on another kind need not import K11's files.
  **pureChainAt_of_open**   IM.Open o pol lay KL F Z Bs base c A B ⇒ ProofFile.onlineFirstChainAt Z = .ok c: the chain that ProofFile.linkAt reads (Johnson/Desc/ProofFile/LinkAt.lean) is the opened value's first chain; every o. The walk is the one inside descPure_chain (Johnson/Desc/ProofFile/Law/LinkAtLaw.lean); here from the own fields of the opening IM.Open (made · places · chain): that opening holds no return of onlineDescription to call descPure_chain at.
  linkAt_of_open          so: ProofFile.linkAt Z m = c.links[m]?, at every m (linkAt_of, LinkAtLaw.lean)
No member. Nothing on soundness.
-/
import Johnson.IMR.SeatOpen
import Johnson.Desc.ProofFile.Law.LinkAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)

section
variable {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The chain that `linkAt` reads is the opened value's first chain. -/
theorem pureChainAt_of_open {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) : ProofFile.onlineFirstChainAt Z = .ok c := by
  show ProofFile.chainOfSeat Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) = .ok c
  rw [ProofFile.Law.chainOfSeat_older Z ProofFile.emptySecondHashFunction o]
  unfold ProofFile.chainOfSeat ProofFile.partsOf
  rw [O.made]
  show ((ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).base.bind fun base =>
    ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road) = .ok c
  rw [O.places]
  exact O.chain

theorem linkAt_of_open {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (m : ℕ) : ProofFile.linkAt Z m = c.links[m]? :=
  ProofFile.Law.linkAt_of Z c (pureChainAt_of_open O) m

end

end ToldDesc

#print axioms ToldDesc.pureChainAt_of_open
#print axioms ToldDesc.linkAt_of_open
