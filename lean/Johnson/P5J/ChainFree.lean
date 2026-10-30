-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ChainFree.lean: THE PROOF FILE's FIRST CHAIN READS NO SECOND HASH. Three theorems.
  chain_free: from the maker's opening at ANY o (IM.Open, Johnson/IMR/SeatOpen.lean): ProofFile.onlineFirstChainAt Z = .ok c (Johnson/Desc/ProofFile/LinkAt.lean: the maker of the chain off the public part, which stands at an idle stand-in for that hash): by unfolding: the seat's field "older" is read by the description's public data alone.
  LaidAt.chain: so under LaidAt the chain's letter IS onlineFirstChainAt's value (and ProofFile.linkAt Zp m is cF.links[m]?).
Limits. An unfolding. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidOpens
import Johnson.Desc.ProofFile.LinkAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain FileDescription Block)
open OnBytes.Maker (WholeD)

/-- **The first chain reads no second hash.** -/
theorem chain_free {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) : ProofFile.onlineFirstChainAt Z = .ok c := by
  have h1 : ProofFile.baseOf Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) = .ok Bs := O.made
  have h2 : (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).base = .ok base := O.places
  have h3 : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).road = .ok c := O.chain
  unfold ProofFile.onlineFirstChainAt ProofFile.chainOfSeat ProofFile.partsOf
  rw [h1]
  show ((ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).base.bind fun base =>
    ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).road) = _
  rw [h2]
  exact h3

/-- Under LaidAt the chain's letter is that maker's value. -/
theorem LaidAt.chain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (L : LaidAt o pol lay KL D r Zp Np cF) :
    ProofFile.onlineFirstChainAt Zp = .ok cF := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact chain_free O

/-- The chain's links off the public part are the letter's. -/
theorem LaidAt.linkAt {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (L : LaidAt o pol lay KL D r Zp Np cF)
    (m : ℕ) : ProofFile.linkAt Zp m = cF.links[m]? := by
  unfold ProofFile.linkAt
  rw [L.chain]
  rfl

end P5J

#print axioms P5J.chain_free
#print axioms P5J.LaidAt.chain
#print axioms P5J.LaidAt.linkAt
