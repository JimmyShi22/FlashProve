-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FourAtLastThread.lean: the linear claim's second part ("K14,
second part", the first member of a proof file's last chain): PlaysS, BehindS, ExchangeS AND
RidesPastS (Honest/Thread/PaysS.lean) AT THE MEMBER 0 OF THE TERM lastThread
(Honest/Thread/TheFirstThread.lean): the last chain's thread at a return of the maker onlineProverFromPublicFiles, at any
filling. One theorem: second_four_open (Honest/K14/SecondFourAtLast.lean) at that term's letters:
its form is fillZ at the first chain's own last state, its order "the statement is in order", its
keeps kpSecond, its one item of its own the library's closed sentence rowsOpen.

TWO LIMITS THAT A READER MUST KNOW FIRST (Honest/K14/SecondFour.lean's head has them at length).
(1) NEITHER THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS THE ITEMS ev AND dot, which ExchangeS takes
from the invariant in front of the
member. (2) BehindS AND ExchangeS HOLD VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and
neither this file nor any file that it imports evaluates that test at a state.

WHAT STAYS A PREMISE. hEv, hDot: on the field meaning of LastThreadParts: the item ev gives that
every open row of the own group in front holds of wordsLast's words; the item dot gives the semantic
(Dot) at Omega's and W's readers. hPin₁, hPin: on the same field: a pin that holds at the tables at
hand still holds when rounds are added to them: asked at every table, number and handed part, so the
two are stronger than the statement. hr, h₀, hst, hl: the clause of BehindS on the field rides,
handed on to the caller.

What is not claimed. That any premise holds. That the thread's invariant holds at any state. That
treesFirst and treesShared are the thread's own counts of trees. The fifth statement, AcceptedS.
Nothing on completeness, soundness or hiding. Terms. letter, border: lean/GLOSSARY.md. A thread is
the invariant along a chain with its parameters (Honest/Thread/Thr.lean). A member is a sub-protocol
of a chain's blocksInOrder list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondFourAtLast
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K14
open VerifiableInference.Desc.Sound (wordsLast)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold DotSem omWW wvW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)
open VerifierAndGoals.AtTheName (dpZ)

variable {W₀ Rc Tr X₀ X : Type}

/-- What the library's value of the last chain's own item (P5J.L0.mlAt) hands the closed sentence
rowsOpen as the number of the first chain's trees. Nothing here ties it to the thread's own count of
these trees, which is the description's. -/
noncomputable abbrev treesFirst (files : VerifierAndGoals.PublicFiles) : ℕ :=
  ((dpZ files).at OnBytes.Slice.frS.P.T.a).t₁

/-- What it hands rowsOpen as the number of the shared chain's trees; likewise tied to nothing here.
-/
noncomputable abbrev treesShared (files : VerifierAndGoals.PublicFiles) : ℕ :=
  ((dpZ files).at OnBytes.Slice.frS.P.T.a).t₂

/-- **PlaysS, BehindS, ExchangeS and RidesPastS at the member 0 of lastThread.** BehindS and
ExchangeS hold vacuously wherever fillZ's test at border 0 is false; ExchangeS takes the items ev
and dot from the invariant in front. hEv: ev gives that every open row of the own group in front
holds of wordsLast's words. hDot: dot gives the semantic (Dot) at Omega's and W's readers. hPin₁,
hPin: a pin still holds when rounds are added. hr, h₀, hst, hl: on the field rides. -/
theorem four_at_lastThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hEv : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).ev a y v →
      RowsHold OnBytes.Model.Reading.gl s
        (wordsLast (P5J.At.arr A.Z) (treesFirst files) (treesShared files) s v))
    (hDot : ∀ inp a e s y v, h.lastForm.shape 0 a e s = true → (parts.meaning inp).dot a e y v →
      DotSem OnBytes.Model.Reading.gl (ToldDesc.p14At A.Z)
        (omWW (P5J.At.arr A.Z) (treesFirst files) (ToldDesc.p14At A.Z) (fun q => q.2)
          (a.1, a.2, e))
        (wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q => q.2) a) s v)
    (hPin₁ : ∀ inp a b q E ps v,
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin₁ a b q ((lastThread h first reads parts w).strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v,
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs E) v →
      (parts.meaning inp).pin a b e ((lastThread h first reads parts w).strs (E.add ps)) v)
    {R₀ : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop}
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, parts.rides b v s ↔ R₀ b v s ∧ ridersOf cs b v s)
    (h₀ : ∀ blk, (lastThread h first reads parts w).bs[0]? = some blk → ∀ k s m E ds y cols s',
      ThrS (lastThread h first reads parts w) Said 0 k s m E → drawsFit blk.rounds ds = true →
      (lastThread h first reads parts w).Stepped blk k s m E ds y cols s' →
      R₀ (0 + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ 0 → 0 + 1 ≤ c.hi → StaysBy (lastThread h first reads parts w) 0 c)
    (hl : ∀ c ∈ cs, c.lo = 0 + 1 → LaysAtS (lastThread h first reads parts w) Said 0 c) :
    PlaysS (lastThread h first reads parts w) Said 0 ∧
      BehindS (lastThread h first reads parts w) Said 0 ∧
      ExchangeS (lastThread h first reads parts w) Said 0 ∧
      RidesPastS (lastThread h first reads parts w) Said 0 :=
  second_four_open A.Z h.places h.firstChain A.H h.sharedNumbers parts.taken parts.ends parts.table
    parts.fixed 0 h.description.t₁ h.description.t₂ _ parts.rides parts.keeps w _ (P5J.At.arr A.Z)
    (treesFirst files) (treesShared files) parts.meaning _ rfl Said hEv hDot hPin₁ hPin hr h₀ hst hl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.four_at_lastThread
