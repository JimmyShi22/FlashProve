-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtUPure.lean: kind K14: **WHERE THE FRAME's MAKER onlineProverFromPublicFiles
(Honest/AtPure.lean) YIELDS A: A's PUBLIC PART AND DESCRIPTION ARE THE LIBRARY's OWN, AND AT A's OWN
BOOK AND ORDER OF PLACES THE ENTRIES AT THE PART AT "send o_u" ARE THE FOUR, AND THE SHORT TEST, THE
TEST ON THE ORDER AND THE OWNER's TEST ACCEPT** (MaskAtBook, Honest/K14/BookAtU.lean, at the parts 0
and 1 of the folded row's proximity test): for all public files Z that pass the library's test
InScope and every public part Zp of which the library's LaidAt holds, at the format's own earlier
hash. One statement with its proof; no definition. A join: calls alone.

  maskAtBook_at_atPure   by the frame's atPure_book (Honest/AtPureBook.lean),
                  sends_written_at_files (Honest/K14/BookAtPure.lean) and maskAtBook_at_written
                  (Honest/K14/BookAtUHead.lean): none of the book's own tests is used

What is assumed. THAT onlineProverFromPublicFiles YIELDS: that carries all that the maker asks: among it that bookWhole
returns, and so that the book passes its own eleven tests: of these nothing is used here · InScope
Z, LaidAt.
What is not claimed. That onlineProverFromPublicFiles yields at any file, at any filling: in this file's own light the
statement may be empty. Another earlier hash than the format's own. Nothing on what is or is not
hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookAtPure
import Johnson.Desc.ProofFile.Honest.K14.BookAtUHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)

variable {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Where onlineProverFromPublicFiles yields A: all that is shown of a book at this owner holds of A's own book, at A's
own order of places.** -/
theorem maskAtBook_at_atPure (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.Z = Zp ∧ A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      MaskAtBook ⟨qAt Zp Np, a⟩ A.B (orderOf A.F)
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 1 } := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok h
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans L.pub)
  have eF : A.F = F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans L.value)
  obtain ⟨k0, k1, k2, e, p0, p1, p2, hs, hB⟩ := atPure_book h
  obtain ⟨En, hl⟩ := sends_written_at_files scope L hs
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, -, rfl, -⟩ := hl
  rw [eF] at hB ⊢
  exact ⟨eZ, rfl, maskAtBook_at_written scope L a hB⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.maskAtBook_at_atPure
