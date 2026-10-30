-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AtPureBookAtHead.lean: NO KIND IS NAMED IN ITS STATEMENT. UNDER
THE LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis), at the format's second hash function: WHERE THE FRAME's
MAKER `onlineProverFromPublicFiles` (Honest/AtPure.lean) YIELDS A AT THE HEAD's FILES: A's BOOK IS WHAT THE MAKER OF THE
BOOK OF COINS `bookWhole` (Honest/BookWhole.lean) RETURNS AT THE HEAD's DESCRIPTION, AT THE PUBLIC
PART's OWN THREE LISTS OF SENDINGS, AT THE MERGES BY NAME. One statement with its proof: calls; no
definition; nothing is evaluated. General in the filling. PUBLIC DATA ALONE.

Main name: `atPure_book_at_head`.

Why. The frame's laying of a thread under the head (`lettersHead`, Honest/Thread/FirstHead.lean, and
its likes) has the book as a free letter: it stands in the types of the laying's own result, of the
Script and of a run's coins alone, and nothing says which book it is. Laws of several kinds
therefore ask, as a premise, "`bookWhole` returns the thread's book". `onlineProverFromPublicFiles` yields a prover
together with a book. At that book the premise follows from "`onlineProverFromPublicFiles` yields". WHAT IS WON IS WHICH
BOOK, NOT THAT `bookWhole` RETURNS: its return is one of the clauses of "`onlineProverFromPublicFiles` yields".

How. The frame's `atPure_book` (Honest/AtPureBook.lean): where `onlineProverFromPublicFiles` yields A, the library's list
of the seven chains' sendings has returned seven, and A's book is what `bookWhole` returned at A's
description and the last three. A's description is the head's (the frame's `atPure_ok`,
Honest/AtPureLaw.lean; the head's field on the value). What the library's list returns at such files
is the written lists, but for the fourth (the library's `sendsWhole_all`,
Johnson/AtFull/Sends/SendsWhole.lean; `sends_tie`, Johnson/LPFE1R/RadiiAt.lean; `made_in_scope`,
Johnson/Goal/Numbers/MadeInScope.lean; `pins_of_laid`, Johnson/Goal/Skeleton/PinsOfLaid.lean); so
are the public part's own three (`sends_in_scope`, MadeInScope.lean).

Limits. CONDITIONAL ON h AND hA. THAT `onlineProverFromPublicFiles` YIELDS IS A PREMISE HERE: it is had with no premise
at the stored full-size files, at the fillings `widerFillAtC fullIn …` (`readyInput_at_zFull`,
AtFullSide/K5/ItemAtFull.lean). Under h the public part, the ground and the description are had;
beside the
book's return hA asks: that the library's list of sendings returns seven lists (had where the
library's test `protocolDataWellFormed` accepts: `sends_of_laid`, Johnson/Top/H0/Opts/SendsOfLaid.lean; that test
is no field of h); three tests on the filling (no half stands at no place of its chain); that the
filling's dummy is in range. What the book holds is not said. That a Script is laid over A's book is
not said: a thread at that book can be spoken of only where one is. OF A THREAD AT A's PROVER
NOTHING IS SAID: the statement has no thread in it, and the filling is a letter. At the list
`mergesByName`: the maker's guess which masked sumchecks are merges. The full size and the earlier
hash alone. This file's imports reach Johnson/Goal/. It is called, among others, in
E2E/ReplyShareAtTheG.lean and AtFullSide/K2/LendAtPure.lean.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.AtPureBook
import Johnson.P5J.MgAtAll
import Johnson.LPFE1R.RadiiAt
import Johnson.AtFull.Sends.SendsWhole
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open P5J (TS)

variable {W₀ Rc Tr X₀ X : Type}
  {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- hA (`onlineProverFromPublicFiles` YIELDS A, at the head's files) IS A PREMISE. **UNDER THE HEAD: A's BOOK IS WHAT
`bookWhole` RETURNS AT THE HEAD's DESCRIPTION AND THE PUBLIC PART's OWN THREE LISTS OF SENDINGS.**
General in the filling. CONDITIONAL on h. -/
theorem atPure_book_at_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok A.B := by
  obtain ⟨k0, k1, k2, e, p0, p1, p2, hs, hb⟩ := ProofFile.Honest.atPure_book hA
  obtain ⟨-, -, hF, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have h1 := VerifiableInference.Desc.LinkJoin.sends_tie h.laid.pub hs
  have h2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1)
  have hl := Except.ok.inj (h1.symm.trans h2)
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := hl
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1]
  rw [eF] at hb
  exact hb

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.atPure_book_at_head
