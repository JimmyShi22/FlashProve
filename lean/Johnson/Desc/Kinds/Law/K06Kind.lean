-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Kind.lean: THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT
HEAD, IN A FORM IN WHICH THE JOIN TAKES A KIND'S LAW: h.Kind (the closed parameters) L
K6 (Johnson/P5J/RowsAtMg.lean: AtMg.Kind): under the join's one head AtMgA and ONE NAMED
CONDITION, K6Cond (Law/K06AtConst.lean), at the join's own frame, at bare "reached" (RchAt), at
its own row of pieces (h.row L). GENERAL IN THE LETTER o FOR THE SECOND HASH FUNCTION. What falls at
the second hash function itself: Law/K06AtHead.lean.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  k06_kind: AtMgA → K6Cond at these terms → h.Kind (dAt h) L K6.
  cond_of_row: K6Cond ITSELF, GENERAL IN "REACHED", at an L whose three lists are the IOP's own: its
      three fields on the maker's piece and the list of sub-protocols are paid (RowAtConst.lean);
      its two on fold facts are drawn from AtMgR.
      Left: AtMgR · cF.links[24]? = some Lk · 342 < cF.blocksInOrder.length · K6StateMg · Seated at the piece
      · K6LeftMg.
  k06_kind_fold, k06_kind_row: the kind's share at bare "reached" from cond_of_fold and from
      cond_of_row: two calls each.
Seated stands for its Object61 · AtMgR takes the laid list alone.


How. k06_at_const at Fr := the join's frame, Rch := RchAt, l := h.row L, c₀ := L.c₀, tokOf := its
At.tokOf. That its list of sorts, its list of places, its extractor and its meaning are K6's files':
by definition: Lean checks it in the one line of the proof.
THE COUNTED FORM AtMgA.Kind h L K6 (P5J/RowsAtAll.lean: at "reached, at a typed
instance's public part") is reached by Goal/Skeleton/Kinds/K6Bridge.lean from K6Cond
at that fence: cond_of_row serves there as it is.
What it does not say. THAT AtMgA OR K6Cond CAN BE MET: NO EXAMPLE. K6Cond CAN HOLD ONLY AT AN L
WHOSE FIRST ROW IS THE DESCRIPTION'S OWN FLAT LIST: whoever joins
takes ONE such L, never "for all L" as a hypothesis. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Kinds.Law.RowAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **THE KIND'S SHARE, IN THE JOIN'S OWN FORM.** -/
theorem k06_kind (h : P5J.AtMgA o Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (piece6 : ℕ) (Lk : Link S Claim) (Lp : K12.Door.Laid) (Mm : List OracleShape)
    (C : K6Cond h _ piece6 Lk (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF)) Lp
        Mm (h.toAtMg.row L)) :
    h.toAtMg.Kind (dAt h) L .K6 :=
  k06_at_const h _ piece6 Lk _ Lp Mm _ L.c₀ P5J.At.tokOf C

/-- **THE CONDITION AT AN L WHOSE THREE LISTS ARE THE IOP'S OWN, GENERAL IN "REACHED": the three
fields on the maker's piece and on the list of sub-protocols are paid** (in
Law/RowAtConst.lean), at the numbering and the list that the row itself bears; the two on fold facts
are drawn from AtMgR. -/
theorem cond_of_row (h : P5J.AtMgA o Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T o Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T o Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T o Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hlen : 341 + 1 < cF.blocksInOrder.length)
    (piece6 : ℕ) (Lk : Link S Claim)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (Lp : K12.Door.Laid) (hF : P5J.AtMgR o Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (hlink : cF.links[24]? = some Lk)
    (hstate : K6StateMg (dAt h) Sound.mgBase
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) piece6 Lk Rch)
    (hseat : ∀ q, (h.toAtMg.row L)[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim),
      Seated (P5J.At.X Zp) .two _ q 24 bef B bS)
    (hleft : K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) x Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) piece6 Lk Rch Lp (K12.Door.msgsOfChain
            Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_of_fold h _ piece6 Lk _ Lp _ hF hlink hstate (fun q hq => by
    obtain ⟨bef, bS, B, Hs⟩ := hseat q hq
    obtain ⟨m, c⟩ := atRow_more h.toAtMg L q₁ q₂ q₃ 341 q hq hlen
    exact ⟨bef, bS, B, _, _, Hs, ⟨m, atRow_blocks h.toAtMg, c⟩, hleft⟩)

/-- The kind's share, the fold facts drawn from AtMgR: two calls. -/
theorem k06_kind_fold (h : P5J.AtMgA o Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (piece6 : ℕ) (Lk : Link S Claim) (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR o Z Dw r Zp Np cF
      (Johnson.Desc.First.Walk.Tied.RchAt
        (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
          (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T o Zp Np cF))
      (fun a => a.1) Lp)
    (hlink : cF.links[24]? = some Lk)
    (hstate : K6StateMg (dAt h) Sound.mgBase
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) piece6 Lk
      (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF)))
    (hpiece : ∀ q, (h.toAtMg.row L)[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim)
      (numD : Fmt.TreeSource → Nat) (bs : List (Block (ProofFile.InstPub × S) Claim)),
        Seated (P5J.At.X Zp) .two _ q 24 bef B bS ∧
        K6RowMg _ numD bs q ∧
        K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
          (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at
              OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) x
          (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF)) Lp
          (K12.Door.msgsOfChain Zp.made.proof.1) bs) :
    h.toAtMg.Kind (dAt h) L .K6 :=
  k06_kind h L piece6 Lk Lp _ (cond_of_fold h _ piece6 Lk _ Lp _ hF hlink hstate hpiece)

/-- The kind's share at bare "reached", from cond_of_row: two calls. -/
theorem k06_kind_row (h : P5J.AtMgA o Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T o Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T o Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T o Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T o Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hlen : 341 + 1 < cF.blocksInOrder.length)
    (piece6 : ℕ) (Lk : Link S Claim) (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR o Z Dw r Zp Np cF
      (Johnson.Desc.First.Walk.Tied.RchAt
        (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
          (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T o Zp Np cF))
      (fun a => a.1) Lp)
    (hlink : cF.links[24]? = some Lk)
    (hstate : K6StateMg (dAt h) Sound.mgBase
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) piece6 Lk
      (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF)))
    (hseat : ∀ q, (h.toAtMg.row L)[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim),
      Seated (P5J.At.X Zp) .two _ q 24 bef B bS)
    (hleft : K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) x
      (Johnson.Desc.First.Walk.Tied.RchAt (P5J.F0T o Zp Np cF)) Lp (K12.Door.msgsOfChain
          Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    h.toAtMg.Kind (dAt h) L .K6 :=
  k06_kind h L piece6 Lk Lp _
    (cond_of_row h L q₁ q₂ q₃ hlen piece6 Lk _ Lp hF hlink hstate hseat hleft)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_of_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_fold
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_row
