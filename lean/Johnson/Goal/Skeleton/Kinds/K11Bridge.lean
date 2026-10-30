-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/Kinds/K11Bridge.lean: the kind K11 (the merge; one place, 346): its files'
own premises, gathered into one proposition under the head `P5J.AtMgA`, give the kind's field in the
form in which a kind's law is counted, `P5J.AtMgA.Kind h 𝔏 .K11` (Johnson/P5J/RowsAtAll.lean).
K11's files' condition is called by its full name (Lean takes the
bare name for the definition that is being made).


  `AtMgA.K11Cond h 𝔏`: the three premises of `K11.k11_kind` (Johnson/K11R/KindAtMg.lean)
    that stand behind the three lists' heads, to the letter: tm (the test `k11AtRB Zp 24` accepts),
    hc (the first chain's rows are the written rows), and K: at every opening, at the two members
    that tm's places name, there are posI, ni, R, Wa with `K11.K11Cond` (Johnson/K11R/LawAtMg.lean)
    at the form's own condition beside the promise, `h.toAtMg.rch`. It reads no letter of 𝔏.
  `k11_kind_all`: the three lists' heads are 𝔏's → `h.K11Cond 𝔏` → `h.Kind 𝔏 .K11`. One call.

Limits. IT PAYS NOTHING. No member of the condition is known:
that `K11.K11Cond`'s fields can be met together is shown nowhere. At
Johnson/K11R/LawAtMg.lean, `K11.K11Cond` holds, by a reading of its fields,
no piece's law and no clause of a tie.
At `OnBytes.secondHashFunction` alone. No soundness is claimed.

-/
import Johnson.P5J.RowsAtAll
import Johnson.K11R.KindAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/K11R/KindAtMg.lean. -/
namespace K11

open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.Walk.Tied (RchAt)
open P5J (AtMgA mgAtAll TS F0T Free)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The merge's files' premises behind the lists' heads, at the closed constant and the form's
own condition beside the promise.** -/
def _root_.P5J.AtMgA.K11Cond (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (_𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  k11AtRB Zp 24 = true ∧
  VerifiableInference.PlanWritten.cutOf (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder =
    VerifiableInference.PlanWritten.cutFirstFull ∧
  ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
    ∀ (pM : ℕ × ℕ) (xM xI : Mem),
    maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some pM →
    xAt (P5J.At.ms Zp Z.lay) pM = some xM →
    xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI →
    ∃ (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ) (Wa : S → Prop),
      _root_.K11.K11Cond
        (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h
        Bs h.toAtMg.rch xM xI posI ni R Wa

/-- **The field.** -/
theorem _root_.P5J.k11_kind_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K11Cond 𝔏) : h.Kind 𝔏 KindName.K11 :=
  k11_kind h 𝔏 q₁ q₂ q₃ C.1 C.2.1 C.2.2

end K11

#print axioms P5J.k11_kind_all
