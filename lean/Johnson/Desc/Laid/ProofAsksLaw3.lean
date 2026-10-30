-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/ProofAsksLaw3.lean: WHAT A YES OF THE ONE ROW OF THE ENTRY TESTS' THIRD PART
(ProofAsks.lean) GIVES. A law file.

  asks_rows      where every entry test accepts, row 14 accepts
  asks_rowsMade  **so at the public plan Z that the maker of the IOP as written returns, the bare
                 test accepts: `rowsMadeB Z`**: at every size

What the bare test's yes gives is its files' to say
(Johnson/Desc/First/Link/Law/RowsRunLaws.lean: `rowsRead_of_yes`). Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofAsks
import Johnson.Desc.Laid.DoorHeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference
open VerifiableInference.Desc (FileDescription)

variable {o : ProofFile.SecondHashFunctionArgument}

/-- Where every test accepts, row 14 accepts. -/
theorem asks_rows {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    _root_.VerifiableInference.Desc.Door.every
      (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
      _root_.VerifiableInference.Desc.LinkJoin.rowsMadeB = true :=
  h ("the plan for these public files is not consistent: its rounds, its oracle messages with \
      their samples and challenges, or their decoding radii cannot be derived again from its \
      sizes, or one shape of oracle message has two radii",
      _root_.VerifiableInference.Desc.Door.every
        (_root_.VerifiableInference.Desc.Door.planOf o pol lay KL)
        _root_.VerifiableInference.Desc.LinkJoin.rowsMadeB) (by simp [_root_.LPFD.lawsAsk])

/-- **At the maker's own public plan the bare test accepts.** -/
theorem asks_rowsMade {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {D : OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    _root_.VerifiableInference.Desc.LinkJoin.rowsMadeB Z = true := by
  obtain ⟨Z₁, h₁, t₁⟩ := _root_.VerifiableInference.Desc.Door.every_yes (asks_rows h)
  have e₁ : Z₁ = Z :=
    Except.ok.inj ((_root_.VerifiableInference.Desc.Door.planOf_some.1 h₁).symm.trans hZ)
  subst e₁
  exact t₁

end LPFD

#print axioms LPFD.asks_rows
#print axioms LPFD.asks_rowsMade
