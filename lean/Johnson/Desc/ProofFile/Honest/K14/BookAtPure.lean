-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookAtPure.lean: kind K14: **WHERE THE FRAME's MAKER onlineProverFromPublicFiles
(Honest/AtPure.lean) YIELDS A, at the format's own earlier hash, for all public files Z that pass
the library's test InScope and every public part Zp of which the library's LaidAt holds: THE TEST
FOR THE PART AT "send o_omega" (spOwner, Honest/K14/FreshOwner.lean) ACCEPTS A's OWN BOOK AT A's OWN
ORDER OF PLACES.** Statements with their proofs; no definition. Joins: calls.

  (the frame's atPure_book, Honest/AtPureBook.lean, is called: where the maker yields A: the
                  library's list of the seven chains' sendings has returned seven, and A's book is
                  what bookWhole returned at A's description, the last three of these and the merges
                  by name)
  sends_written_at_files   **what the library's list returns at such files is the written lists,
                  but for the fourth of the seven, of which nothing is said**: by the library's
                  sends_tie (Johnson/LPFE1R/RadiiAt.lean: the sendings do not hang
                  on the digest), made_in_scope (Johnson/Goal/Numbers/MadeInScope.lean),
                  pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean) and sendsWhole_all
                  (Johnson/AtFull/Sends/SendsWhole.lean)
  spOwner_ok_at_atPure   **the closing statement**: A's public part is Zp; A's description is the
                  proof file's IOP as written in Lean; spWholeB and the owner's test accept A.B

What is assumed. THAT onlineProverFromPublicFiles YIELDS: of that premise is used: that the public part and the
description are the maker's (atPure_ok), that the library's list of sendings has returned, and that
bookWhole has returned A's book at that list; of the last: Honest/K14/SharedSendsWritten.lean's
head. (THE PREMISE CARRIES MORE: bookWhole hands a book on only where it passes all eleven of its
own tests, and the maker asks more behind it: none of THAT is used) · InScope Z, LaidAt.
Kin. The library's sends_of_laid (Johnson/Top/H0/Opts/SendsOfLaid.lean): where protocolDataWellFormed accepts,
sendsOf returns seven, the fifth the public part's own: it has the return that
sends_written_at_files assumes.
What is not claimed. That onlineProverFromPublicFiles yields at any file, at any filling: NOT SHOWN HERE: BY THIS FILE
THE CLOSING STATEMENT MAY BE EMPTY. (Another kind's writers state that it yields at one filling,
under the library's head, a public test on the files and the premise that bookWhole returns at the
written description: atPure_returns_fullIn_of_written; this library may not hold it.) "ALL PUBLIC
FILES THAT PASS InScope" IS ONE SIZE: in scope, under LaidAt, the proof chain's codes and shape are
the written ones (numbers_at_files' proof, Honest/K14/BookAtOmegaHead.lean, rewrites by just that).
The like at "send o_u": not here: maskAtBook_at_atPure (Honest/K14/BookAtUPure.lean). Another
earlier hash than the format's own. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.AtPureBook
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten
import Johnson.LPFE1R.RadiiAt
import Johnson.AtFull.Sends.SendsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open Johnson.G (keySendsFull proofSendsFull)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)

variable {W₀ Rc Tr X₀ X : Type}

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **What the library's list of sendings returns at such files is the written lists**, but for the
fourth of the seven, of which nothing is said. -/
theorem sends_written_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {sends : List Johnson.G.ChainSends} (hs : Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok sends) :
    ∃ En, sends = [keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2, En, proofSendsFull.1,
      proofSendsFull.2.1, proofSendsFull.2.2] := by
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have h1 := VerifiableInference.Desc.LinkJoin.sends_tie L.pub hs
  have h2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope scope L.pub
    (P5J.pins_of_laid scope L).1)
  exact ⟨En, Except.ok.inj (h1.symm.trans h2)⟩

/-- **WHERE onlineProverFromPublicFiles YIELDS A: spWholeB AND THE OWNER's TEST ACCEPT A's OWN BOOK AT A's OWN ORDER OF
PLACES.** -/
theorem spOwner_ok_at_atPure (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.Z = Zp ∧ A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧ spWholeB ⟨qAt Zp Np, a⟩ A.B = true ∧
      (spOwner ⟨qAt Zp Np, a⟩).ok A.B (orderOf A.F) { place := sendPlace 5, part := 0 } = true := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok h
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans L.pub)
  have eF : A.F = F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans L.value)
  obtain ⟨k0, k1, k2, e, p0, p1, p2, hs, hB⟩ := atPure_book h
  obtain ⟨En, hl⟩ := sends_written_at_files scope L hs
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, -, rfl, -⟩ := hl
  rw [eF] at hB ⊢
  exact ⟨eZ, rfl, spOwner_ok_at_written scope L a hB⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sends_written_at_files
#print axioms ProofFile.Honest.K14.spOwner_ok_at_atPure
