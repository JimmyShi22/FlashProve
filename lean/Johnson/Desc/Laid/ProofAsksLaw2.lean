-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/ProofAsksLaw2.lean: WHAT A YES OF THE TWO PINS OF THE ENTRY TESTS' SECOND PART
(ProofAsks.lean) GIVES. A law file.

  asks_made     where every entry test accepts, the row on the planner's sizes, list of rounds and
                oracle messages accepts
  asks_cut      and the row on the IOP's division into sub-protocols
  asks_dig | asks_reads | asks_head   and the lookups' three rows, which read the public parameters
  asks_rest     these three at the maker's own public plan
  asks_pins     **so at the public plan Z that the maker of the IOP as written returns, if Z stands
                at
                the full size's key, both bare tests accept: `madeRow Z` and `cutRow F Z`**

What the bare tests' yes gives is their files' to say (PlanWritten/MadeTestLaws.lean,
Goal/Numbers/MadeInScope.lean; PlanWritten/CutTestLaws.lean). Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofAsks
import Johnson.Desc.Laid.DoorHeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- Where every test accepts, the row «made» accepts. -/
theorem asks_made {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.atFull
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.PlanWritten.madeRow = true :=
  h ("the sizes, the list of rounds, the layout, the oracle messages or the sub-proofs' shapes \
      planned for these public files are not those written into the verifier",
      _root_.VerifiableInference.Desc.Door.atFull
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        _root_.VerifiableInference.PlanWritten.madeRow) (by simp [_root_.LPFD.lawsAsk])

/-- Where every test accepts, the row «cut» accepts. -/
theorem asks_cut {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.atFull
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      (_root_.VerifiableInference.PlanWritten.cutRow F) = true :=
  h ("the IOP's division into sub-protocols at these public files is not the one written into \
      the verifier",
      _root_.VerifiableInference.Desc.Door.atFull
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        (_root_.VerifiableInference.PlanWritten.cutRow F)) (by simp [_root_.LPFD.lawsAsk])

/-- Where every test accepts, the row «dig» accepts. -/
theorem asks_dig {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.digEntry = true :=
  h ("the public files do not lay the digits of an approximate range proof where its lookup \
      reads them",
      _root_.VerifiableInference.Desc.Door.every
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        _root_.VerifiableInference.Desc.K3Asks.digEntry) (by simp [_root_.LPFD.lawsAsk])

/-- Where every test accepts, the row «reads» accepts. -/
theorem asks_reads {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.readsEntry = true :=
  h ("the public files do not lay an attention step's cells where its lookup reads them",
      _root_.VerifiableInference.Desc.Door.every
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        _root_.VerifiableInference.Desc.K3Asks.readsEntry) (by simp [_root_.LPFD.lawsAsk])

/-- Where every test accepts, the row «head» accepts. -/
theorem asks_head {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.K3Asks.headEntry = true :=
  h ("the public files do not give a call of the output head's lookup room for its keys",
      _root_.VerifiableInference.Desc.Door.every
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        _root_.VerifiableInference.Desc.K3Asks.headEntry) (by simp [_root_.LPFD.lawsAsk])

/-- **At the maker's own public plan, at the full size's key, both bare tests accept.** -/
theorem asks_pins {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hk : _root_.VerifiableInference.Desc.Door.atFullKey Z = true) :
    _root_.VerifiableInference.PlanWritten.madeRow Z = true ∧
      _root_.VerifiableInference.PlanWritten.cutRow F Z = true := by
  obtain ⟨Z₁, h₁, t₁⟩ := _root_.VerifiableInference.Desc.Door.atFull_yes (asks_made h)
  obtain ⟨Z₂, h₂, t₂⟩ := _root_.VerifiableInference.Desc.Door.atFull_yes (asks_cut h)
  have e₁ : Z₁ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₁).symm.trans hZ)
  have e₂ : Z₂ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₂).symm.trans hZ)
  subst e₁
  subst e₂
  exact ⟨t₁ hk, t₂ hk⟩

/-- **At the maker's own public plan the three rows that are asked at every size accept.** -/
theorem asks_rest {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    _root_.VerifiableInference.Desc.K3Asks.digEntry Z = true ∧
      _root_.VerifiableInference.Desc.K3Asks.readsEntry Z = true ∧
      _root_.VerifiableInference.Desc.K3Asks.headEntry Z = true := by
  obtain ⟨Z₁, h₁, t₁⟩ := _root_.VerifiableInference.Desc.Door.every_yes (asks_dig h)
  obtain ⟨Z₂, h₂, t₂⟩ := _root_.VerifiableInference.Desc.Door.every_yes (asks_reads h)
  obtain ⟨Z₃, h₃, t₃⟩ := _root_.VerifiableInference.Desc.Door.every_yes (asks_head h)
  have e₁ : Z₁ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₁).symm.trans hZ)
  have e₂ : Z₂ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₂).symm.trans hZ)
  have e₃ : Z₃ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₃).symm.trans hZ)
  subst e₁
  subst e₂
  subst e₃
  exact ⟨t₁, t₂, t₃⟩

end LPFD

#print axioms LPFD.asks_made
#print axioms LPFD.asks_cut
#print axioms LPFD.asks_dig
#print axioms LPFD.asks_reads
#print axioms LPFD.asks_head
#print axioms LPFD.asks_pins
#print axioms LPFD.asks_rest
