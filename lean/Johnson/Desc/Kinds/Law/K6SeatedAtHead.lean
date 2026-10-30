-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/K6SeatedAtHead.lean: WHAT A SEAT AND THE IOP AS WRITTEN IN LEAN LAY AROUND
THE OUTPUT HEAD's SEATED CONSTANT (Seated, Johnson/Desc/Sound/K6Tied.lean: lot · narrows · unmarked
· piece · back), AT THE ONE HEAD OF A COUNTED STATEMENT (P5J.AtMg | AtMgA), at the format's second
hash function OnBytes.secondHashFunction, at the piece number 341 of the head's own row. STATED AND PROVED:
CALLS AND TIES: no new mathematics.
Why. The output head's law reads of its premise Object61 (Johnson/Desc/Sound/Border62.lean) three
things alone: Seated (by seated_of_object), Seated's first field, and a closed fact on the list of
places. Seated is had here without a letter for the driver's socket.
  k6_core_at_mg    there are bef, bS, B with: seatedClaims (At.X Zp) 24 bef = some bS ·
                   cF.blocksInOrder[341]? = some B · B.Narrows bS · a yes of B bears no mark. By IM.k6_of
                   (Johnson/IMR/K6Seat.lean: link 24's fourth sub-protocol in front of the batching
                   is the seated constant, marked, alone, behind the driver's guard) · IM.k6_at_341
                   (Johnson/IMR/FlatScope.lean) · IM.alone_underR · IM.yes_alone
                   (Johnson/IMR/SeatForm.lean); the base's public parameters are carried to At.X Zp
                   by IM.Open.W.
  **k6_seated_at_mg**   at an L whose three lists are the IOP's own (q₁ q₂ q₃): there are bef, bS,
                   B, ONE TRIPLE FOR EVERY q, with cF.blocksInOrder[341]? = some B and: every q that is entry
                   341 of h.row L has Seated (At.X Zp) .two _ q 24 bef B bS. piece and back by
                   atRow_lift | atRow_more | atRow_in (Law/RowAtConst.lean · RowLenAtConst).
  k6_seated_at_head  the same at h : AtMgA … x.
  **seated_at_head**  THE FORM THAT Law/K06AtHead.lean CALLS: ∀ q, (h.toAtMg.row L)[341]? = some q →
                   ∃ bef B bS, Seated (At.X Zp) .two _ q 24 bef B bS.
Limits. It pays Seated, NOT Object61 as typed: nothing is said of the driver's socket or of
firstChain. At OnBytes.secondHashFunction alone; the full size alone. At another L nothing is said. A member of
the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on
soundness or on hiding.

-/
import Johnson.IMR.K6Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.Sound.K6Tied
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **The seated constant, the 341st sub-protocol, and the two facts between them.** -/
theorem k6_core_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim),
      seatedClaims (P5J.At.X Zp) 24 bef = some bS ∧ cF.blocksInOrder[341]? = some B ∧ B.Narrows bS ∧
        ∀ s rs gs t, B.decide s rs gs = .ok t → t.failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', ms, e1, e2, _, hsc, hla, _, _, _⟩ := IM.k6_of h.scope h.reads O
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  exact ⟨ms, b', b, eW ▸ hsc, (IM.k6_at_341 h.scope h.reads O e1 e2).1, IM.alone_underR hla,
    fun s rs gs t hy => ((IM.yes_alone hla (by decide) s t rs gs).1 hy).2.1⟩

/-- **Seated, at the piece number 341 of the head's own row.** -/
theorem k6_seated_at_mg (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim), cF.blocksInOrder[341]? = some B ∧
      ∀ q, (h.row L)[341]? = some q → Seated (P5J.At.X Zp) .two _ q 24 bef B bS := by
  obtain ⟨bef, bS, B, h1, h2, h3, h4⟩ := k6_core_at_mg h
  exact ⟨bef, bS, B, h2, fun q hq => ⟨h1, h3, h4, atRow_lift h L q₁ q₂ q₃ 341 q B hq h2,
    (atRow_more h L q₁ q₂ q₃ 341 q hq (atRow_in h 341 (by decide))).1.back⟩⟩

/-- **The same at the head.** -/
theorem k6_seated_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim), cF.blocksInOrder[341]? = some B ∧
      ∀ q, (h.toAtMg.row L)[341]? = some q → Seated (P5J.At.X Zp) .two _ q 24 bef B bS :=
  k6_seated_at_mg h.toAtMg L q₁ q₂ q₃

/-- **The form that Law/K06AtHead.lean calls.** -/
theorem seated_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    ∀ q, (h.toAtMg.row L)[341]? = some q →
      ∃ (bef : List (ℕ × ℕ)) (B bS : Block S Claim), Seated (P5J.At.X Zp) .two _ q 24 bef B bS := by
  obtain ⟨bef, bS, B, _, H⟩ := k6_seated_at_head h L q₁ q₂ q₃
  exact fun q hq => ⟨bef, B, bS, H q hq⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_core_at_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_seated_at_mg
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_seated_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seated_at_head
