-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07KindOfHs.lean.
WHAT IT DOES NOT SHOW. No soundness. NO HEAD IS SHOWN: NO EXAMPLE IN LEAN SHOWS THAT THE HEAD AND hs
CAN BE MET TOGETHER: NOTHING COUNTS AS PROVED. The payer of fenceT stands over at least lawsAsk's
rows madeRow and cutRow (Desc/Laid/ProofAsks.lean). hs STAYS A PREMISE (the place whose switch opens
group 24 stands at the head). Content only at an L under q₁, q₂, q₃. At the second hash function
itself alone. The full size alone.
WHAT IT IS. THE CALL THAT GATHERS THE NEXT TOKEN's KIND's PAYMENTS: of the seven premises of
k07_kind_of_facts (Law/K07KindOfFacts.lean) six are paid from the head; hs alone stays. Two
theorems; calls alone.
  k07_kind_of_hs   the head, q₁ q₂ q₃ and hs give AtMgA.Kind h L at the kind K7
  k7Facts_of_hs    the same give the skeleton's proposition AtMgA.K7Facts h L
                   (Goal/Skeleton/Kinds/K7Facts.lean)
THE PAYERS. book: book_at_const (Law/BookAtConst.lean). fenceT: P5J.LaidAt.fence
(Johnson/P5T/CoreAtMg.lean). hb: P1L20.whole_atAll's second clause at 338
(Johnson/P1L20R/FrameFourAll.lean). bookInOrder, bookFits, rowsSent: IM.facts338_at_head
(Johnson/IMR/Facts338.lean).
LETTERS. No "there is" in the statements. No free letter but the head's own and L.
USER. The kinds' join.


-/
import Johnson.Desc.Kinds.Law.K07KindOfFacts
import Johnson.Desc.Kinds.Law.BookAtConst
import Johnson.Goal.Skeleton.Kinds.K7Facts
import Johnson.P5T.CoreAtMg
import Johnson.P1L20R.FrameFourAll
import Johnson.IMR.Facts338

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

/-- **THE NEXT TOKEN's LAW, IN THE COUNTED FORM, FROM THE HEAD AND hs ALONE.** -/
theorem k07_kind_of_hs (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hs : (ProofFile.pAtK2 Zp 23).stands = .head) :
    h.Kind L KindName.K7 :=
  k07_kind_of_facts h L q₁ q₂ q₃ (book_at_const h) (P5J.LaidAt.fence h.laid h.scope) hs
    (fun q hq => (P1L20.whole_atAll h L q₁ q₂ q₃).2 338 q hq)
    (IM.facts338_at_head h).1 (IM.facts338_at_head h).2.1 (IM.facts338_at_head h).2.2

/-- **The skeleton's proposition, from the head and hs alone.** -/
theorem k7Facts_of_hs (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hs : (ProofFile.pAtK2 Zp 23).stands = .head) :
    h.K7Facts L :=
  ⟨book_at_const h, P5J.LaidAt.fence h.laid h.scope, hs,
    fun q hq => (P1L20.whole_atAll h L q₁ q₂ q₃).2 338 q hq,
    (IM.facts338_at_head h).1, (IM.facts338_at_head h).2.1, (IM.facts338_at_head h).2.2⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_hs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7Facts_of_hs
