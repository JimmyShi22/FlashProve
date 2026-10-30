-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Seat.lean: OF THE BATCHING KIND's ONE NAMED CONDITION AT THE CLOSED CONSTANT
(`AtMgA.K9Cond`, K09Kind.lean) ALL THAT SPEAKS OF THE SEAT IS PAID: that each of a link's four
pieces holds the sub-protocol that stands at its number of the first chain's flat list, lifted over
the public part; and that the table's extractor lays nothing at these numbers. WHAT IS LEFT IS THE
LAWS ALONE (`AtMgA.K9Laws`). Definitions, theorems, evaluations.

What is said.
  `k9Lays_links`: the kernel's yes: at the written list `fullLinks` the rows at the numbers of each
    link's batching, of the two places behind it and of the shutting lay nothing (100 numbers).
    `k9Lays_bent`: a negative test: asked of all 358 numbers of the list the test says no.
    `lays_at`. `AtMg.ex_id`: **where the row lays nothing the seated extractor is the identity.**
    `AtMgA.K9Laws h 𝔏`: at every link, at the pieces and at the sub-protocols that stand at the
    four numbers: there are five relations with `ThreeAsksR` at every public part, and there are the
    shutting's two numbers with `ShutOwesR` at every public part. `k9Cond_of_laws`: **`h.K9Cond 𝔏`
    from `h.K9Laws 𝔏`**, the three flat lists' heads, and «no fewer pieces than places».
    `k09_kind_of_laws`: **so `h.Kind 𝔏 .K9`.**

Limits. BOOK-KEEPING AND TWO EVALUATIONS. `K9Laws` IS THE DEBT: no member is known. The three
equations on the flat lists' heads and the length are premises, as in the tower's own rows. Nothing
on soundness.

-/
import Johnson.P5J.K09Kind
import Johnson.Desc.Sound.ExtQAtId
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start flatPlacesOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt ThreeAsksR ShutOwesR atRec)
open Johnson.Desc.First.Walk.Tied (block_at)

set_option maxRecDepth 1000000 in
/-- **AT THE 100 NUMBERS THE ROWS LAY NOTHING.** -/
theorem k9Lays_links : ((List.range 25).all fun m => [0, 1, 2, 4].all fun j =>
    laysNothingAt fullLinks (flatPlacesOf fullLinks true)
      (batchAt fullLinks (flatPlacesOf fullLinks true) m + j)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: not every row of the written list lays nothing. -/
theorem k9Lays_bent : ((List.range 358).all fun k =>
    laysNothingAt fullLinks (flatPlacesOf fullLinks true) k) = false := by
  decide +kernel

theorem lays_at {m j : ℕ} (hm : m < fullLinks.length) (hj : j ∈ [0, 1, 2, 4]) :
    laysNothingAt fullLinks At.ps (batchAt fullLinks At.ps m + j) = true :=
  List.all_eq_true.1 (List.all_eq_true.1 k9Lays_links m (List.mem_range.2 hm)) j hj

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHERE THE ROW LAYS NOTHING THE SEATED EXTRACTOR IS THE IDENTITY.** -/
theorem AtMg.ex_id (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (k : ℕ) (hk : laysNothingAt fullLinks At.ps k = true) :
    ∀ a b w, h.ex 𝔏 k a b w = w :=
  fun a b w => by
    unfold AtMg.ex exF
    exact extQAt_id_of_test _ _ _ _ _ _ _ _ _ _ _ _ k hk a b w

/-- **THE LAWS ALONE.** -/
def AtMgA.K9Laws (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  ∀ m < fullLinks.length,
    (∀ qb qq qe B₁ B₂ B₃, (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m]? = some qb →
      (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m + 1]? = some qq →
      (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m + 1 + 1]? = some qe →
      (F0T o Zp Np cF).first.blocksInOrder[batchAt fullLinks At.ps m]? = some B₁ →
      (F0T o Zp Np cF).first.blocksInOrder[batchAt fullLinks At.ps m + 1]? = some B₂ →
      (F0T o Zp Np cF).first.blocksInOrder[batchAt fullLinks At.ps m + 1 + 1]? = some B₃ →
      ∃ R0 R1 R1' R2 R3 : ProofFile.InstPub → TS × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
                (D.at frS.P.T.a).key₁ 0).E.Str → Wit (CellsM numsFull) At.Tok MsgT → Prop, ∀ z,
        ThreeAsksR (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
          (At.N Zp cF) (mgAtAll h) fullLinks At.ps
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (batchAt fullLinks At.ps m)
          (atRec qb (below B₁)) (atRec qq (below B₂)) (atRec qe (below B₃)) (R0 z) (R1 z) (R1' z)
          (R2 z) (R3 z) z) ∧
    ∀ qs B₅, (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m + 4]? = some qs →
      (F0T o Zp Np cF).first.blocksInOrder[batchAt fullLinks At.ps m + 4]? = some B₅ →
      ∃ pw piece, ∀ z,
        ShutOwesR (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
          (At.N Zp cF) (mgAtAll h) fullLinks At.ps
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) z
          (batchAt fullLinks At.ps m + 4) pw piece B₅ (atRec qs (below B₅))

/-- **THE CONDITION FROM THE LAWS ALONE.** -/
theorem k9Cond_of_laws (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hlen : At.ps.length ≤ (h.toAtMg.row 𝔏).length) (L : h.K9Laws 𝔏) : h.K9Cond 𝔏 := by
  have hT := h.toAtMg.ofDesc 𝔏 q₁ q₂ q₃
  refine ⟨hlen, fun m hm qb qq qe hb hq he => ?_, fun m hm qs hs => ?_⟩
  · obtain ⟨B₁, h1⟩ := block_at hT hb
    obtain ⟨B₂, h2⟩ := block_at hT hq
    obtain ⟨B₃, h3⟩ := block_at hT he
    obtain ⟨R0, R1, R1', R2, R3, H⟩ := (L m hm).1 qb qq qe B₁ B₂ B₃ hb hq he h1 h2 h3
    exact ⟨B₁, B₂, B₃, R0, R1, R1', R2, R3, OfDesc.pieceAt hT hb h1, OfDesc.pieceAt hT hq h2,
      OfDesc.pieceAt hT he h3, h.toAtMg.ex_id 𝔏 _ (lays_at (j := 0) hm (by simp)),
      h.toAtMg.ex_id 𝔏 _ (lays_at (j := 1) hm (by simp)),
      h.toAtMg.ex_id 𝔏 _ (lays_at (j := 2) hm (by simp)), H⟩
  · obtain ⟨B₅, h5⟩ := block_at hT hs
    obtain ⟨pw, piece, H⟩ := (L m hm).2 qs B₅ hs h5
    exact ⟨pw, piece, B₅, OfDesc.pieceAt hT hs h5,
      h.toAtMg.ex_id 𝔏 _ (lays_at (j := 4) hm (by simp)), H⟩

/-- **SO THE FIELD.** -/
theorem k09_kind_of_laws (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hlen : At.ps.length ≤ (h.toAtMg.row 𝔏).length) (L : h.K9Laws 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind h 𝔏 (k9Cond_of_laws h 𝔏 q₁ q₂ q₃ hlen L)

end P5J

#print axioms P5J.k9Lays_links
#print axioms P5J.k9Lays_bent
#print axioms P5J.AtMg.ex_id
#print axioms P5J.k9Cond_of_laws
#print axioms P5J.k09_kind_of_laws
