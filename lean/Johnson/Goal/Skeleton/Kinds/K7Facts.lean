-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/Kinds/K7Facts.lean: the kind K7 (the next token; one place, 338): SEVEN
NAMED PREMISES, NONE OF THEM A PART OF THE CONCLUSION, gathered into one proposition under the head
`P5J.AtMgA`, give the kind's field in the form in which a kind's law is counted,
`P5J.AtMgA.Kind h 𝔏 .K7` (Johnson/P5J/RowsAtAll.lean).

  `AtMgA.K7Facts h 𝔏`: the seven premises of `k07_kind_of_facts`
    (Johnson/Desc/Kinds/Law/K07KindOfFacts.lean) that stand behind the head and the three lists'
    heads, to the letter:
    two tests with code on public data: book (`bookFit`), fenceT (`fenceFit`);
    two closed facts: hs (the place whose switch opens group 24 stands at the head), hb (the base of
    the piece at 338 is at most the number of the first chain's trees);
    three facts at 338, along `h.rch` ("reached, at a typed instance's public part"), AT STATES
    WITHOUT A MARK ALONE: bookInOrder, bookFits, rowsSent (the letters of three fields of
    `FoldFacts`).
  `k07_kind_facts`: the three lists' heads are 𝔏's → `h.K7Facts 𝔏` → `h.Kind 𝔏 .K7`. One call.

Beside Johnson/Goal/Skeleton/Kinds/K7Left.lean [not in this library]: there the third premise is
`K7Carry`, the fifth tie of the conclusion at the item "carry 23". As read from K7's files,
that premise is a theorem under book, hs, hb and the three facts: here these stand in its place.

Limits. IT PAYS NOTHING ITSELF. No member of the condition is known in Lean: it follows from the
head and the three equations (`k7Facts_of_head`, Johnson/Desc/Kinds/Law/K07KindOfHead.lean; how each
of the seven is had is told there and in K07KindOfHs.lean beside it), but that there is a head is
proved at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side
library AtFullSide/Top/); at other files: evaluated, not proved. This file proves none of the seven:
book, fenceT, hs, hb and the three facts along "reached" are premises here. Under the head each is a
theorem (six: Johnson/Desc/Kinds/Law/K07KindOfHs.lean; hs: Johnson/Loose/H2K12/HsAtAll.lean).
fenceT's payer and hs's stand over the entry tests' rows madeRow and cutRow
(Johnson/Desc/Laid/ProofAsks.lean), and the written division that hs's payer spends rests on prints
of Lean's evaluator (K07KindOfHead.lean's head). hb reads 𝔏 through the piece at 338; the other six
read no letter of 𝔏. At `OnBytes.secondHashFunction` alone. The full size alone. No soundness is claimed.

-/
import Johnson.Desc.Kinds.Law.K07KindOfFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/Desc/Kinds/Law/K07KindOfFacts.lean. -/
namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (KindName Chain)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First.K2 (par9)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The next token's kind's seven named premises, at the closed constant.** None is a part of the
conclusion. -/
def _root_.P5J.AtMgA.K7Facts (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  First.bookFit (dAt h).N (flatPlacesOf linksFull true) (toldOf cF.blocksInOrder) = true ∧
  First.fenceFit (dAt h).N linksFull (flatPlacesOf linksFull true) = true ∧
  (ProofFile.pAtK2 Zp 23).stands = .head ∧
  (∀ q, (h.toAtMg.row 𝔏)[338]? = some q → q.base ≤ D.t₁) ∧
  (∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Zp 23)).firstTree a.1.2 =
      true) ∧
  (∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) ∧
  ∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
    ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size

/-- **The field.** -/
theorem _root_.P5J.k07_kind_facts (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K7Facts 𝔏) : h.Kind 𝔏 KindName.K7 := by
  obtain ⟨book, fenceT, hs, hb, bookInOrder, bookFits, rowsSent⟩ := C
  exact _root_.VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_facts h 𝔏 q₁ q₂ q₃ book
    fenceT hs hb bookInOrder bookFits rowsSent

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms P5J.k07_kind_facts
