-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LaidOpens.lean: THE CARRIAGE TO THE VALUE: WHERE THE PROOF FILE's VALUE IS LAID, WHAT THE ROWS AT THE SEATED TERM TAKE OF THE MAKER AND OF THE DESCRIPTION's OWN TESTS IS THERE, AT ONE TERM (NOT the tests on the plan that no text of the value asks: fullShapeB above all). One structure, three theorems. (The door is handed the second hash function: lawsAsk o pol lay KL F D. The field opened: the whole opening of the maker, for whoever needs the chain's own making.) A joint build of files of several kinds.

Why. The rows at the seated term (Johnson/P5J/AtTerm.lean · TieAtStart.lean and what is assembled over them) stand at F0T o Zp Np cF, a schema of four letters, under: Zp is the plain road's public part · the description's own test on the plan · its rounds' data · the three flat lists' heads. The verifier's own value says "laid" (LPFD.Full.proofDataAndDecisionOfPublicFiles … = .ok (D, r)).
  LaidAt o pol lay KL D r Z N c: at these letters: the places are made of Z · Z is the plain road's public part of the three files · the maker returns JUST THE TERM · planOk · data = D · the decision r is the term's, laid on the requests · every test of the door says yes.
  laid_opens: **proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r) → ∃ Z N c, LaidAt o pol lay KL D r Z N c.** By the value's own law (laidPOf_ok) and the opening of the maker (descPure_open, over seat_open).
  laid_opensK: at the second hash function itself: beside: publicOf pol KL (some lay) = .ok Z.p.X: the rows' scope_public at X := Z.p.X · lay := some lay.
  LaidAt.heads: the three flat lists are a first block and a rest (free by the make of a chain's flat list): as terms.
SO: InScope · "the value is laid" · the named tests on the plan are what is left in front of whatever stands at the term.

Limits. The full size's value (LPFD.Full). It opens; it pays no law. D is the data that the value holds: that it is the frame's (D.at a) is not said here. No member is shown here; that the value is laid is proved at `VerifierAndGoals.storedPublicFiles` (the library's written copy of the full-size public files, not the release's files), at the second hash function (`OnBytes.secondHashFunction`): `AtFullSide.Top.theProofLaid_zFull_returns` (AtFullSide/Top/LiveAtFull.lean, a side library).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtTerm
import Johnson.Desc.Sound.PieceLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (FileDescription Chain Block)
open OnBytes.Maker (WholeD)
open Desc.K14.Law (descPure_open secondAt seatZ)

/-- **What "laid" holds, at the term's letters.** -/
structure LaidAt (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (D : WholeD) (r : LPFD.Full.RunPF) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain TS ProofFile.Cl) : Prop where
  places : H2U.placesOfMade Z.made = .ok N
  pub : ProofFile.pubPlain o pol lay KL = .ok Z
  value : ProofFile.onlineDescription o pol lay KL = .ok (F0T o Z N c)
  planOk : (F0T o Z N c).planOk = true
  data : (F0T o Z N c).data "proof file" = .ok D
  run : r = ((F0T o Z N c).pull LPFD.Full.instanceAsPlainRecord).run
  asks : ∀ t ∈ LPFD.lawsAsk o pol lay KL (F0T o Z N c) D, t.2 = true
  /-- the program's public data of the files, at the letter o, is the public part's -/
  publicO : VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Z.p.X
  /-- the whole opening of the maker (the structure IM.Open, Johnson/IMR/SeatOpen.lean): the seat has no fault and lacks nothing · the places · the chain's own making -/
  opened : ∃ Bs base, IM.Open o pol lay KL (F0T o Z N c) Z Bs base c (seatZ Z N) (secondAt Z N)

/-- **Where the value is laid, it opens at one term.** -/
theorem laid_opens {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) : ∃ Z N c, LaidAt o pol lay KL D r Z N c := by
  obtain ⟨F, hF, hp, hD, ha, hr⟩ := LPFD.Full.laidPOf_ok h
  obtain ⟨Z, Bs, base, c, N, hN, O⟩ := descPure_open o pol lay KL F hF
  have e : F = F0T o Z N c := O.desc
  subst e
  exact ⟨Z, N, c, hN, O.pub, hF, hp, hD, hr, ha, O.W ▸ O.publicO, Bs, base, O⟩

/-- **At the second hash function itself: scope_public's form**: publicOf pol KL (some lay) = .ok Z.p.X. -/
theorem laid_opensK {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction pol lay KL = .ok (D, r)) :
    ∃ Z N c, LaidAt OnBytes.secondHashFunction pol lay KL D r Z N c ∧
      OnBytes.Model.Verify.publicOf pol KL (some lay) = .ok Z.p.X := by
  obtain ⟨F, hF, hp, hD, ha, hr⟩ := LPFD.Full.laidPOf_ok h
  obtain ⟨Z, Bs, base, c, N, hN, O⟩ := descPure_open OnBytes.secondHashFunction pol lay KL F hF
  have e : F = F0T OnBytes.secondHashFunction Z N c := O.desc
  subst e
  exact ⟨Z, N, c, ⟨hN, O.pub, hF, hp, hD, hr, ha, O.W ▸ O.publicO, Bs, base, O⟩, O.W ▸ O.public⟩

/-- The three flat lists' heads, as terms. -/
theorem LaidAt.heads (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain TS ProofFile.Cl) :
    (∃ b l, (F0T o Z N c).first.blocksInOrder = b :: l) ∧ (∃ b l, (F0T o Z N c).shared.blocksInOrder = b :: l) ∧
      ∃ b l, (F0T o Z N c).second.blocksInOrder = b :: l :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

end P5J

#print axioms P5J.laid_opens
#print axioms P5J.laid_opensK
#print axioms P5J.LaidAt.heads
