-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveAtLastThreadLaid.lean: the linear claim's second part ("K14,
second part", the first member of a proof file's last chain): THE STRUCTURE FiveAtBorder
(Honest/Thread/FiveAtBorder.lean) AT THE MEMBER 0 OF THE TERM lastThread
(Honest/Thread/TheFirstThread.lean), WHERE THE MEANINGS OF THE ITEMS ev AND dot ARE LAID: ev as
evAll (Honest/K14/EvAtLastStart.lean: every open row of the request's own group at the first chain's
last state holds), dot as the library's dotI (Johnson/Desc/Third/Law/Row0DotOm.lean) at the
library's readers of Omega and of W. One theorem: five_at_lastThread_door
(Honest/K14/FiveAtLastThread.lean) with its premises hEv and hDot shown by second_hEv and
second_hDot (Honest/K14/EvAtLastStart.lean, DotAtLastStart.lean).

TWO LIMITS THAT A READER MUST KNOW FIRST (Honest/K14/SecondFour.lean's head has them at length).
(1) NEITHER THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS THE ITEMS ev AND dot, which ExchangeS takes
from the invariant in front of the
member: laying their meanings says what is to be shown where the chain is entered, and shows
nothing. (2) BehindS AND ExchangeS HOLD VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and
neither this file nor any file that it imports evaluates that test at a state.

WHAT STAYS A PREMISE. hE, hDt: the two layings, equations on the field meaning of LastThreadParts.
hPin₁, hPin: on the same field: a pin that holds at the tables at hand still holds when rounds are
added to them; asked at every table, number and handed part. hr, late: the field rides is doorRider
and clauses that begin at border 2 or later.

What is not claimed. That any premise holds. That the thread's invariant holds at any state. Nothing
on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.FiveAtLastThread
import Johnson.Desc.ProofFile.Honest.K14.DotAtLastStart
import Johnson.Desc.ProofFile.Honest.K14.EvAtLastStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.Sound (wordsShared)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (gOfS dotI wvW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)

variable {W₀ Rc Tr X₀ X : Type}

/-- **FiveAtBorder at the member 0 of lastThread, where ev is evAll and dot is dotI.** BehindS and
ExchangeS hold vacuously wherever fillZ's test at border 0 is false; ExchangeS takes the items ev
and dot from the invariant in front, and AcceptedS takes secondDoor's tests from it. hE, hDt: the
two layings. hPin₁, hPin: a pin still holds when rounds are added. hr, late: the form of the field
rides. -/
theorem five_at_lastThread_laid {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hE : ∀ inp, (parts.meaning inp).ev = evAll (P5J.At.arr A.Z) fun q => q.2)
    (hDt : ∀ inp, (parts.meaning inp).dot = dotI (ToldDesc.p14At A.Z).S (fun q => gOfS q.2)
      (fun d v => wordsShared (P5J.At.arr A.Z) (treesFirst files) d.st d.book v)
      (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q => q.2) q))
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ ridersOf (doorRider _ (ToldDesc.p14At A.Z) :: cs) b v s)
    (late : ∀ c ∈ cs, 2 ≤ c.lo) :
    FiveAtBorder (lastThread h first reads parts w) Said fall 0 :=
  five_at_lastThread_door h first reads parts w Said fall
    (second_hEv parts.meaning (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds (fun q => q.2)
      (P5J.At.arr A.Z) (treesFirst files) (treesShared files) hE)
    (second_hDot parts.meaning (ToldDesc.p14At A.Z) (LLT25.c2 h.places).rounds (fun q => q.2)
      (P5J.At.arr A.Z) (treesFirst files) hDt)
    hPin₁ hPin hr late

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.five_at_lastThread_laid
