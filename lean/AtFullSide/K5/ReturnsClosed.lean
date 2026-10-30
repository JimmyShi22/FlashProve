-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/ReturnsClosed.lean: THREE LAWS OF OURS THAT HAD ONE CLOSED SENTENCE ON THE WRITTEN
BOOK AS A PREMISE (hB: the book's maker bookWhole returns a book at the library's written
description), WITH THAT PREMISE MET BY ITS AUTHORS' THEOREM
`AtFullSide.K14.bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean). Three theorems;
no definition; one call each.

  `atPure_returns_fullIn_closed`  h, hl ⊢ the frame's maker onlineProverFromPublicFiles returns at the filling
                                  `widerFillAt fullIn o' S O`
  `atPure_returns_fill_closed`    h, hl, fP ⊢ it returns at a filling P, P a letter
  `hT_at_maker_closed`            h, hA, hg ⊢ K5's test on the book holds at the book of whatever A
                                  the maker returns, at whatever filling

By: `atPure_returns_fullIn_of_written`
(Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsFromWritten.lean), `atPure_returns_fill`
(…/K5/Law/ReturnsFill.lean), `hT_at_maker_of_written` (AtFullSide/K5/MaskRowAtMaker.lean).

Why in this side library. The theorem that meets hB stands here, over evaluations in Lean's kernel
at the full size: no file of the main library can call it. So what spends these three stands here
too.

Limits. ALL THAT IS NEW HERE IS AS GOOD AS `bookWhole_returns_written`: it rests on many evaluations
in Lean's kernel at written values, which were printed off the goals' stored full-size public files;
on the merges of `mergesByName`, which the frame's own text calls a guess; on the makers' texts as
they lie beneath this file. THAT bookWhole RETURNS SAYS THAT THE BOOK's ELEVEN OWN TESTS ACCEPT, AND
NO MORE: nothing on the tests on owners that stand outside the eleven (`ownersClearBy`), on
`carriesWhole`, on how many positions are opened; the eleven read the book's entries, rows and cuts
and the description, not the parts' texts. It is a fact at the written description and at no other;
the written sendings rest on labels on one print. ALL LIMITS OF AtFullSide/K14/BookWholeWritten.lean
HOLD HERE. THAT THE MAKER RETURNS AT A FILLING IS NO WORD ON WHETHER ITS PROVER CAN PLAY: what it
asks of a filling forbids halves that stray, it asks for none. The first law names one written
filling, with no thread about it: it does not carry over to a wider one; the second does. The head h
is a hypothesis, and so is the library's test hl; fP and hA are premises. All limits of the three
files that are called hold, but that hB is a premise. The full size alone; at the earlier hash
`OnBytes.secondHashFunction`.
Nothing is claimed on soundness, completeness or hiding.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K5.MaskRowAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFromWritten
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- **onlineProverFromPublicFiles RETURNS AT `widerFillAt fullIn`.** CONDITIONAL: h: the head; hl: the library's test on
the head's public files. -/
theorem atPure_returns_fullIn_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt fullIn o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  atPure_returns_fullIn_of_written h hl AtFullSide.K14.bookWhole_returns_written o' S O

/-- **onlineProverFromPublicFiles RETURNS AT A FILLING P, P A LETTER.** CONDITIONAL: h; hl; fP: what the maker asks of
the filling. -/
theorem atPure_returns_fill_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (P : OnlineProverParts W₀ Rc Tr X₀ X)
    (fP : ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks P Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G :=
  atPure_returns_fill h hl AtFullSide.K14.bookWhole_returns_written P fP

/-- **K5's TEST ON THE BOOK, AT THE MAKER's BOOK.** CONDITIONAL: h; hA: the maker returns A at a
filling P; g is below 12. -/
theorem hT_at_maker_closed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {g : ℕ} (hg : g < 12) :
    oneStretch (rowEntries A.B ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072) :=
  hT_at_maker_of_written h hA AtFullSide.K14.bookWhole_returns_written hg

end AtFullSide.K5

#print axioms AtFullSide.K5.atPure_returns_fullIn_closed
#print axioms AtFullSide.K5.atPure_returns_fill_closed
#print axioms AtFullSide.K5.hT_at_maker_closed
