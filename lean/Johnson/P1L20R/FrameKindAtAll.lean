-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameKindAtAll.lean: THE SHARE OF THE KIND "frame" ON THE FIRST CHAIN, IN THE FORM IN
WHICH A KIND's LAW IS COUNTED AT THE SEATED TERM: P5J.AtMgA.Kind h L KindName.frame
(Johnson/P5J/RowsAtAll.lean), L: the tower's free letters.

  FrameOwedAll      WHAT STANDS IN FRONT, a field a debt, in the seated term's own letters (the row
                    of pieces h.toAtMg.row L, the extractor h.toAtMg.ex L, the condition
                    h.toAtMg.rch)
  frame_kind_atAll  at the format's own second hash function: from the head h, the three flat lists'
                    heads at L's letters, and FrameOwedAll: h.Kind L KindName.frame

What Lean holds by this file: the seated term's letters ARE the letters of frame_law_atAll
(FrameLawAtAll.lean): the two lists of the segments' sorts; the written list of places; the seated
description and the maker's value; the tower's row of pieces and threeCap's; the tower's extractor
and the table's own at the constant's parameters.

Limits. No field of FrameOwedAll is shown here. A member of the head is proved at storedPublicFiles and zGap
alone (at secondHashFunction; side library AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameLawAtAll
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K2Caller (rest)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The first chain's frame of oracles at the tower's data. -/
abbrev FrAll (D : WholeD) : Frame :=
  frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT STANDS IN FRONT OF THE FRAME's LAW AT THE SEATED TERM.** -/
structure FrameOwedAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop where
  /-- the description's data are the tower's -/
  data : ∃ file, (F0T OnBytes.secondHashFunction Zp Np cF).data file = .ok (D.at frS.P.T.a)
  /-- the OOD-sampled oracle messages whose pin is open in front of each of the 51 sit in trees
  below the piece's base -/
  low : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q →
    LowAt (dmOf h).N (openL9 k) q.base
  /-- the files' whole data, as the sentence on the carried word reads them -/
  whole : ∃ Dw, ProofFile.wholeAt Zp = some Dw ∧
    ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → q.base ≤ Dw.t₁
  /-- the book holds no more trees than the piece's base -/
  size : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → ∀ p s y,
    InAt9 (dmOf h) (KnTight 0) k (p, s) y → s.book.trees.size ≤ q.base
  /-- the carried word's sentence over "laid", where the next code switch does not stand at a link
  -/
  carryElseLaid : ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[14 * l + 1]? = some q → ∀ m,
    openP9 (14 * l + 1 + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
    GoesBack (StepRel (Yes (layFront l)) q.base (InAt9 (dmOf h) (KnTight 0) (14 * l + 1)))
      ((dmOf h).cr1 m)
  /-- the like over "cleared" -/
  carryElseClear : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (h.toAtMg.row L)[clearIx l]? = some q → ∀ m,
    openP9 (clearIx l + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
    GoesBack (StepRel (Yes f.clear) q.base (InAt9 (dmOf h) (KnTight 0) (clearIx l)))
      ((dmOf h).cr1 m)
  /-- the constant's numbers of trees and messages do not move across the 51 -/
  still : NoneBetween (dmOf h).N (flatPlacesOf linksFull true) 0 ∧
    (∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
    ∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (clearIx l)
  /-- of every statement that is reached in front of one of the 51 numbers and bears no mark: the
  book is in order from tree 0 on, it fits, the carried rows name messages that have a place -/
  kn : ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
    KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2)
  /-- the seal's tie (other files' to show) -/
  sealTie : ∀ q, (h.toAtMg.row L)[357]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch 357 (q.withMap (h.toAtMg.ex L 357))
  /-- the 25 ties behind the batching (other files' to show) -/
  behindTies : ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[behindIx l]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch (behindIx l)
      (q.withMap (h.toAtMg.ex L (behindIx l)))

set_option maxHeartbeats 4000000 in
/-- **THE KIND "frame" AT THE SEATED TERM.** -/
theorem frame_kind_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FrameOwedAll h L) : h.Kind L KindName.frame := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨file, hD⟩ := W.data
  obtain ⟨Dw, hW, hBase⟩ := W.whole
  exact frame_law_atAll h.scope h.reads O hD h.laid.planOk q₁ q₂ q₃ h L.e₁ L.e₂ L.e₃ L.dW L.wEnd
    L.c₀ P5J.At.tokOf W.low Dw hW hBase W.size W.carryElseLaid W.carryElseClear W.still
    h.toAtMg.rch W.kn W.sealTie W.behindTies

end

end P1L20

#print axioms P1L20.frame_kind_atAll
