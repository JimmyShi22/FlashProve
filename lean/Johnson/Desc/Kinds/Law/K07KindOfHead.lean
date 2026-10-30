-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07KindOfHead.lean. WHAT IT DOES NOT SHOW. No soundness. A MEMBER OF THE HEAD
IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction, WITH fixedConfigurationDigest IN THE DIGEST's PLACE; SIDE LIBRARY
AtFullSide/Top/); SO WHAT RESTS ON THE HEAD COUNTS AS PROVED THERE ALONE. NO STATE IS SHOWN BY A
THEOREM AT WHICH THE PROMISE, "REACHED" AND "NO MARK" HOLD TOGETHER AT THIS PLACE: FIVE OF THE SEVEN
TIES (Desc/Sound/ChainOfPromisesR.lean: TiedAtR) MAY HOLD IDLY. THIS LAW IS "SURE" (AT EVERY
TRANSCRIPT; NO CHALLENGE IS SPENT): IN ITS NAMED FORM (Law/K7Tied.lean: k7_own) THE CONDITION IN
FRONT IN ITS GoodIn IS THE PROMISE AND "REACHED" THEMSELVES: WERE THESE EMPTY AT ITS PLACE, GoodIn
TOO WOULD BE IDLE, WITH THE FIVE (not the two ties on the mark and on "decodes"). Two of its payers
stand over at least lawsAsk's rows madeRow and cutRow (Desc/Laid/ProofAsks.lean): fenceT's
(P5J.LaidAt.fence) and "the first chain's division into sub-protocols is the written one"
(P5J.pins_of_laid's second half, spent inside hs_atAll). THAT WRITTEN DIVISION RESTS ON PRINTS OF
LEAN's EVALUATOR; the entry test compares it at a run (hs_atAll's own file's words). Content only at
an L under q₁, q₂, q₃. At the second hash function itself alone. The full size alone. WHAT IT IS.
hs FALLS: THE NEXT TOKEN's KIND's LAW FROM THE HEAD. Law/K07KindOfHs.lean paid six of the seven
premises of k07_kind_of_facts from the head and kept hs ("the place whose switch opens group 24
stands at the head"). H2K12.hs_atAll (Johnson/Loose/H2K12/HsAtAll.lean) has hs under the head alone.
  k07_kind_of_head   the head and q₁ q₂ q₃ give AtMgA.Kind h L at the kind K7
  k7Facts_of_head    the same give AtMgA.K7Facts h L (Goal/Skeleton/Kinds/K7Facts.lean)
LETTERS. No "there is" in the statements. No free letter but the head's own and L. USER. The kinds'
join calls k07_kind_of_head; k7Facts_of_head has no caller.
-/
import Johnson.Desc.Kinds.Law.K07KindOfHs
import Johnson.Loose.H2K12.HsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (KindName Chain)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE NEXT TOKEN's LAW, IN THE COUNTED FORM, FROM THE HEAD ALONE.** -/
theorem k07_kind_of_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    h.Kind L KindName.K7 :=
  k07_kind_of_hs h L q₁ q₂ q₃ (H2K12.hs_atAll h)

/-- **The skeleton's proposition, from the head alone.** -/
theorem k7Facts_of_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    h.K7Facts L :=
  k7Facts_of_hs h L q₁ q₂ q₃ (H2K12.hs_atAll h)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7Facts_of_head
