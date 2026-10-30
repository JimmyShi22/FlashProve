-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean: A PIN ON THE LIST OF Johnson/Desc/Laid/ProofAsks.lean.
This file writes out a list of thirteen entry tests and checks that it is a prefix of the verifier's
list (`lawsAsk`): one of these that is taken out or moved makes it fail, as long as this file is not
turned with that one. It holds the tests by name: a change inside a test's own definition it does
not see.

  asksAt2             the thirteen tests, written out
  asksAt2_prefix      **they are a prefix of the list `lawsAsk`**
  yes_at2             a yes of the list `lawsAsk` is a yes of these thirteen

-/
import Johnson.Desc.Laid.ProofAsks
import Johnson.Desc.Laid.AsksFirstLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- Thirteen entry tests, written out. -/
def asksAt2 (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (_D : OnBytes.Maker.WholeD) : List (String × Bool) :=
  [("the rounds declared for these public files are not the rounds written in the verifier",
    _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F),
   ("an attention segment's lookup has more scalars than the segment has slots left",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.masks o pol lay KL),
   ("the attention lookups are not the usual four with one shift",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.usual o pol lay KL),
   ("the attention lookups' numbers do not fit the segment's sizes",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.calls o pol lay KL),
   ("an attention segment's numbers are not those of its sizes",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.nums o pol lay KL),
   ("one of six sizes of an attention segment's tables is 0",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.pos o pol lay KL),
   ("an attention segment's pieces do not lie in the lookups as described",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.units o pol lay KL),
   ("an attention segment is too large, or a round's count of bad challenges cannot be weighed \
      or is above its share",
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.held o pol lay KL),
   ("the sizes, the list of rounds, the layout, the oracle messages or the sub-proofs' shapes \
      planned for these public files are not those written into the verifier",
    _root_.VerifiableInference.Desc.Door.atFull
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.PlanWritten.madeRow),
   ("the IOP's division into sub-protocols at these public files is not the one written into \
      the verifier",
    _root_.VerifiableInference.Desc.Door.atFull
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      (_root_.VerifiableInference.PlanWritten.cutRow F)),
   ("the public files do not lay the digits of an approximate range proof where its lookup \
      reads them",
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.digEntry),
   ("the public files do not lay an attention step's cells where its lookup reads them",
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.readsEntry),
   ("the public files do not give a call of the output head's lookup room for its keys",
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.headEntry)]

/-- **These thirteen are a prefix of the list `lawsAsk`.** -/
theorem asksAt2_prefix (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (D : OnBytes.Maker.WholeD) :
    asksAt2 o pol lay KL F D <+: _root_.LPFD.lawsAsk o pol lay KL F D := by
  unfold asksAt2 _root_.LPFD.lawsAsk
  simp

/-- A yes of the list `lawsAsk` is a yes of these thirteen. -/
theorem yes_at2 {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : _root_.LPFD.firstNo (_root_.LPFD.lawsAsk o pol lay KL F D) = none) :
    _root_.LPFD.firstNo (asksAt2 o pol lay KL F D) = none := by
  obtain ⟨m, hm⟩ := asksAt2_prefix o pol lay KL F D
  exact _root_.LPFD.asksYes_append _ m (hm ▸ h)

end LPFD

#print axioms LPFD.asksAt2_prefix
#print axioms LPFD.yes_at2
