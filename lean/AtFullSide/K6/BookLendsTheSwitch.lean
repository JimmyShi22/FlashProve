-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K6/BookLendsTheSwitch.lean: CONDITIONAL, UNDER THE LIBRARY's HYPOTHESIS h ON THE PUBLIC
FILES AND "THE MAKER RETURNS": THE BOOK OF A RETURN OF THE MAKER LENDS THE FIRST PART OF EVERY
WRITTEN CODE SWITCH WHAT THE PART's TEXT ASKS (the public test lendsPart accepts); AND THE GROUND OF
THAT RETURN IS THE BLANK GROUND OF THE PUBLIC PART. Two short theorems; calls alone. No kind but the
code switch is named in the statements.

WHAT IT IS NOT. lendsPart asks name, count and that the owners' cuts fit: it holds as well at a book
that lends another owner's coins of that count. So "handed something" is not "handed its own coins,
once". That the maker returns at any filling is a premise. The part number 0 of each place and the
chain number 0 alone. The library's hypothesis h holds at the full size and the format's second
hash function alone. Closed facts that Lean's kernel decided by evaluation at written values lie beneath.
Nothing on soundness, on completeness or on what a proof hides.

WHAT IT IS. Under h the book of every return of the maker, at whatever filling, is the book at the
library's written description (makers_book_one, AtFullSide/K14/MakersBookOne.lean), and there the
test accepts at every written place of a code switch (switch_lends_at_written,
AtFullSide/K14/SwitchesLend.lean). The index's type, the type of the stored tables' randomness and
the filling are parameters.

WORDS. The maker is the function that makes the prover, its book of coins and its ground from the
public files and a filling (the choice of the prover's sides).
-/
import Johnson.Desc.ProofFile.Honest.AtHead
import AtFullSide.K14.MakersBookOne
import AtFullSide.K14.SwitchesLend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2.Law (placesW)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL on h and on "the maker returns". **The ground of a return of the maker is the blank
ground of the public part.** -/
theorem groundOfAReturnIsBlank (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
  have e := (atPure_ok makerReturns).2.1
  rw [(atPure_at_laid h.laid makerReturns).1] at e
  exact e

/-- CONDITIONAL on h, on "the maker returns" and on "p is a written place of a code switch". **The
book of a return of the maker lends the switch's first part what the part's text asks**: the public
test accepts. It asks name, count and that the owners' cuts fit: it holds as well at a book that
lends another owner's coins of that count. -/
theorem bookLendsTheSwitch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {p : K2.SwitchPlace}
    (placeIsWritten : p ∈ placesW) :
    lendsPart A.B (A.B.rowsOf 0) (lookDue A.B 0) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
      true := by
  obtain ⟨B, atWritten, -, -, -, atEveryReturn⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨sameBook, -⟩ := atEveryReturn _ _ _ _ _ P A makerReturns
  rw [sameBook]
  exact AtFullSide.K14.switch_lends_at_written atWritten placeIsWritten

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.groundOfAReturnIsBlank
#print axioms ProofFile.Honest.K6.Term.bookLendsTheSwitch
