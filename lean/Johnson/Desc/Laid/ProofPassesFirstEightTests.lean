-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofPassesFirstEightTests.lean: A PIN ON THE VALUE, FOR THE EIGHT TESTS OF `asksAt1`.
It is compiled with the library, and so at every change of
Johnson/Desc/Laid/ProofAsks.lean.
Where ProofAsksFirstEightTests.lean pins the list `LPFD.lawsAsk`, this file pins WHAT THE VALUE ASKS: a yes of
the value itself, at either size, gives a yes of every test of the list `asksAt1`, and of the
written plan's test by name. So it fails to compile if the value's text comes to ask another list
than the pinned one through a name that has come to mean another constant. It is a check by the
kernel on terms: it does not see other code laid for a term to run, nor a macro or an elaborator
that turns how this very file is read, nor this file turned with the value, nor inside a test.

  Full.laid_at1 | Small.laid_at1        what is laid of a description: every test of
                                        `asksAt1` has said yes
  Full.laid_written | Small.laid_written  what is laid of a description: the written plan's test has
                                          said yes
  Full.laidPOf_written1 | Small.laidPOf_written1  the like from the three files: the description
                                                  that was made has passed the written plan's test

-/
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Laid.ProofSmallLaw
import Johnson.Desc.Laid.ProofAsksFirstEightTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- Every test of `asksAt1` says yes: the written plan's test says yes. -/
theorem written_of_at1 {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ asksAt1 o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true :=
  h ("the rounds declared for these public files are not the rounds written in the verifier",
      _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F) (by simp [asksAt1])

/-- **What is laid of a description, at the full size: every test of `asksAt1` has said yes.**
-/
theorem Full.laid_at1 {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    {r : _root_.LPFD.Full.RunPF} (h : _root_.LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F = .ok (D, r)) :
    ∀ t ∈ asksAt1 o pol lay KL F D, t.2 = true := fun t ht =>
  ((_root_.LPFD.Full.laidOfDesc_iff o pol lay KL F D r).1 h).2.2.1 t
    ((asksAt1_prefix o pol lay KL F D).subset ht)

/-- The written plan's test has said yes. -/
theorem Full.laid_written {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {D : OnBytes.Maker.WholeD} {r : _root_.LPFD.Full.RunPF}
    (h : _root_.LPFD.Full.proofDataAndDecisionOfDescription o pol lay KL F = .ok (D, r)) :
    _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true :=
  written_of_at1 (Full.laid_at1 h)

/-- From the three files: the description that was made has passed the written plan's test. -/
theorem Full.laidPOf_written1 {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : _root_.LPFD.Full.RunPF} (h : _root_.LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, _root_.ProofFile.onlineDescription o pol lay KL = .ok F ∧
      _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true := by
  obtain ⟨F, hd, hp, hD, hs, hr⟩ := _root_.LPFD.Full.laidPOf_ok h
  exact ⟨F, hd, written_of_at1 fun t ht => hs t ((asksAt1_prefix o pol lay KL F D).subset ht)⟩

/-- **What is laid of a description, at the small size: every test of `asksAt1` has said
yes.** -/
theorem Small.laid_at1 {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    {r : _root_.LPFD.Small.RunPS} (h : _root_.LPFD.Small.laidOfDesc o pol lay KL F = .ok (D, r)) :
    ∀ t ∈ asksAt1 o pol lay KL F D, t.2 = true := fun t ht =>
  ((_root_.LPFD.Small.laidOfDesc_iff o pol lay KL F D r).1 h).2.2.1 t
    ((asksAt1_prefix o pol lay KL F D).subset ht)

/-- The written plan's test has said yes. -/
theorem Small.laid_written {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {D : OnBytes.Maker.WholeD} {r : _root_.LPFD.Small.RunPS}
    (h : _root_.LPFD.Small.laidOfDesc o pol lay KL F = .ok (D, r)) :
    _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true :=
  written_of_at1 (Small.laid_at1 h)

/-- From the three files: the description that was made has passed the written plan's test. -/
theorem Small.laidPOf_written1 {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : _root_.LPFD.Small.RunPS} (h : _root_.LPFD.Small.laidPOf o pol lay KL = .ok (D, r)) :
    ∃ F, _root_.ProofFile.onlineDescription o pol lay KL = .ok F ∧
      _root_.VerifiableInference.PlanWritten.seatPinnedProof pol F = true := by
  obtain ⟨F, hd, hp, hD, hs, hr⟩ := _root_.LPFD.Small.laidPOf_ok h
  exact ⟨F, hd, written_of_at1 fun t ht => hs t ((asksAt1_prefix o pol lay KL F D).subset ht)⟩

end LPFD

#print axioms LPFD.Full.laid_at1
#print axioms LPFD.Full.laid_written
#print axioms LPFD.Full.laidPOf_written1
#print axioms LPFD.Small.laid_at1
#print axioms LPFD.Small.laid_written
#print axioms LPFD.Small.laidPOf_written1
