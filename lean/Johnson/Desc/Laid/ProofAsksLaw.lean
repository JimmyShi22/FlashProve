-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofAsksLaw.lean: what a yes of all the tests of Johnson/Desc/Laid/ProofAsks.lean
gives: a law for each test. Each law
is stated from "every test of `lawsAsk` says yes", so that it stands word for word when a test is
appended.

  asks_written        where every test of `lawsAsk` says yes, the written plan's test says yes
  asks_guard          and so do the seven tests of the attention segments' guard

-/
import Johnson.Desc.Laid.ProofAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- Where every test says yes, the written plan's test says yes. -/
theorem asks_written {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true :=
  h ("the rounds declared for these public files are not the rounds written in the verifier",
      _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F) (by simp [_root_.LPFD.lawsAsk])

/-- Where every test says yes, the seven tests of the attention segments' guard say yes. -/
theorem asks_guard {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.First.Att.P.K5Asks.masks o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.usual o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.calls o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.nums o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.pos o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.units o pol lay KL = true ∧
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.held o pol lay KL = true :=
  ⟨h ("an attention segment's lookup has more scalars than the segment has slots left",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.masks o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("the attention lookups are not the usual four with one shift",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.usual o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("the attention lookups' numbers do not fit the segment's sizes",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.calls o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("an attention segment's numbers are not those of its sizes",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.nums o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("one of six sizes of an attention segment's tables is 0",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.pos o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("an attention segment's pieces do not lie in the lookups as described",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.units o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk]),
    h ("an attention segment is too large, or a round's count of bad challenges cannot be weighed \
      or is above its share",
      _root_.VerifiableInference.Desc.First.Att.P.K5Asks.held o pol lay KL)
      (by simp [_root_.LPFD.lawsAsk])⟩

end LPFD

#print axioms LPFD.asks_written
#print axioms LPFD.asks_guard
