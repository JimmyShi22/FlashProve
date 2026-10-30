-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/BookAtConst.lean.
WHAT IT DOES NOT SHOW. No soundness. NO LAW OF ANY SUB-PROTOCOL. NOTHING ON fenceFit: that test is
not true by the numbers' make: it ties the plan's seats to the telling and has content
(Desc/First/FenceFitTold.lean's own head). AND THIS YES CARRIES NO CONTENT: at these numbers the
test bookFit compares a thing with itself (Desc/First/BookFitTold.lean, Limit (2)): what is shown is
that NO DEBT HIDES in that premise at the closed constant, not that anything about a run holds.
WORDS. "The closed constant": the table's files' parameters and meaning at their head AtMgA
(Law/DAtConst.lean: dAt). "The telling": what each sub-protocol of the first chain tells (toldOf).
LETTERS. No "there is". General in the head's letters, the second hash function o too. Kind-free.
OBJECT. The test First.bookFit at the closed constant's numbers, the driver's list of places and the
first chain's own telling.
USER. Every kind's law at the closed constant that takes that test's yes as a premise. First: the
next token's (Law/K07KindOfFacts.lean: book).
WHAT IT IS. AT THE CLOSED CONSTANT bookFit's YES IS A THEOREM, BY THE NUMBERS' MAKE. The table's
files' numbers are (…).withTold ps (told cF) (P5J/LettersAt.lean: At.N), with ps the driver's list
and told cF the chain's own telling, each by definition; bookFit_withTold says yes
at every such filling where no place stands twice; that the driver's list has no
repeat is ProofFile.Law.flatPlaces_nodup
(Desc/ProofFile/Law/KindPlaces.lean).
book_at_const: the statement.

-/
import Johnson.Desc.Kinds.Law.DAtConst
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull toldOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- **AT THE CLOSED CONSTANT THE TEST bookFit SAYS YES, BY THE NUMBERS' MAKE.** -/
theorem book_at_const (h : P5J.AtMgA o Z D r Zp Np cF x) :
    VerifiableInference.Desc.First.bookFit (dAt h).N PS (toldOf cF.blocksInOrder) = true :=
  VerifiableInference.Desc.First.bookFit_withTold _ PS (toldOf cF.blocksInOrder)
    (ProofFile.Law.flatPlaces_nodup linksFull true)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.book_at_const
