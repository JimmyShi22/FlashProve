-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FormsAtLetters.lean: THE PREMISE ON THE FIELD "forms" OF
Honest/K3/Law/Thread/ExchangeDigitsText.lean's `exchange_digits_text` (hF) AT THE FIRST CHAIN'S
LETTERS LAID AT THE LIBRARY'S OWN (`lettersAt`, Honest/Thread/FirstAt.lean): it holds there, at
every input, AT SEVEN LETTERS THAT DO NOT HANG ON THE INPUT: those of the library's own data. One
theorem.

  `formsText_lettersAt`   UNDER the library's head h alone

WHY IT IS TYPED. The premise binds its seven letters in front of "at every input", while these
letters' meaning of the items is made of data that hang on the input. The input enters two fields of
the data alone; none of the seven reads them. Here Lean says so.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

Limits. AT THE FULL SIZE ALONE (the letters stand there alone). The head is a premise. One premise
of one theorem. Nothing on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormsAtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the first chain's letters laid at the library's own the field "forms" of the items' meaning
has the premise's text at every input, at the seven letters of the library's own data.** -/
theorem formsText_lettersAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr Xo : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    FormsText ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w)
      h.𝔇.runs h.𝔇.Rd h.𝔇.N.sent h.𝔇.N.group h.𝔇.ah (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt :=
  formsText_mgAll _ _

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.formsText_lettersAt
