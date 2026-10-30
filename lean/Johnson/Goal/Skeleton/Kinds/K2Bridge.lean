-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/Kinds/K2Bridge.lean: the kind K2 (code switching): its files' own named
condition, under the head `P5J.AtMgA`, gives the kind's field in the form in which a kind's law is
counted, `P5J.AtMgA.Kind h 𝔏 .K2` (Johnson/P5J/RowsAtAll.lean). The condition stands at
`h.rchU` (Johnson/Goal/Skeleton/Kinds/Unmarked.lean): "reached, at a typed instance's public part,
and no mark": it asks less than at `h.toAtMg.rch`, and a field that asks a fact of every reached
state (hFk) is no more asked at marked states, where no payer is known.
`frameAt` is written with its full name and `k02_counted` is told its frame.

  `AtMgA.K2Cond h 𝔏`: at every place of the kind (25 on the first chain), of the piece that stands
    there: `K2PlaceOwes` (Johnson/Top/H0/K2Ties/Counted.lean) at D := h.toAtMg.𝔇 h.𝔇, Mg₀ := mgBase,
    the written lists, 𝔏.c₀, and Rch := h.rchU. But for Rch this is the premise of
    `k02_kind` (Johnson/Top/H0/K2Ties/KindIs.lean) to the letter.
  `k02_kind_all`: `h.K2Cond 𝔏` → `h.Kind 𝔏 .K2`: `k02_counted`, which is general in the condition
    beside the promise, and `AtMgA.kind_of_unmarked`.
  `k02_kind_bare`: the same end from K2's files' premise at bare "reached": `k02_kind` and
    `AtMgA.kind_of_reached`.

Limits. IT PAYS NOTHING. NO MEMBER OF THE CONDITION IS KNOWN. `K2PlaceOwes` says: there are some
forty letters with "the piece is written out", "it holds the strict reading of B, lifted", "no
accept at a marked state" and `K2AllOwes` (74 fields, as counted in K2's files). As read from
those files, no field is one of the conclusion's ties, but some (hHands, hPP, hshN, hσ, hAt)
are clauses at an accept, near to what the second and third ties conclude. At `OnBytes.secondHashFunction`
here, as the top's head is. No soundness is claimed.

-/
import Johnson.Goal.Skeleton.Kinds.Unmarked
import Johnson.Top.H0.K2Ties.KindIs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/Top/H0/K2Ties/KindIs.lean. -/
namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker (WholeD)
open OnBytes.Flat (numsFull)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (RchAt)
open P5J (AtMg TS colsAt F0T Free fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The code switch's named condition, at the closed constant and at reached states without a
mark.** -/
def _root_.P5J.AtMgA.K2Cond (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  ∀ i q a, (h.toAtMg.row 𝔏)[i]? = some q → P5J.At.ps[i]? = some a → a.kind = KindName.K2 →
    K2PlaceOwes (F := VerifiableInference.Desc.Sound.frameAt (D.at OnBytes.Slice.frS.P.T.a)
        (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.rchU fullLinks P5J.At.ps 𝔏.c₀ i q

/-- **The field.** -/
theorem _root_.P5J.k02_kind_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (_q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K2Cond 𝔏) : h.Kind 𝔏 KindName.K2 :=
  h.kind_of_unmarked 𝔏 KindName.K2
    (k02_counted (F := VerifiableInference.Desc.Sound.frameAt (D.at OnBytes.Slice.frS.P.T.a)
        (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.rchU fullLinks P5J.At.ps 𝔏.c₀ P5J.At.tokOf
      (h.toAtMg.row 𝔏) C)

/-- The same end from K2's files' premise at bare "reached". -/
theorem _root_.P5J.k02_kind_bare (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (H : ∀ i q a, (h.toAtMg.row 𝔏)[i]? = some q → P5J.At.ps[i]? = some a →
      a.kind = KindName.K2 →
      K2PlaceOwes (h.toAtMg.𝔇 h.𝔇) mgBase (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) fullLinks
        P5J.At.ps 𝔏.c₀ i q) : h.Kind 𝔏 KindName.K2 :=
  h.kind_of_reached 𝔏 KindName.K2 (k02_kind h.toAtMg h.𝔇 𝔏 H)

end VerifiableInference.Desc.First.K2Caller

#print axioms P5J.k02_kind_all
#print axioms P5J.k02_kind_bare
