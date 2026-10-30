-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PiecesSeated.lean: the kind "lookup" (K3): `K3Pieces`
(Johnson/Desc/First/Look/K3Base.lean) AT THE PIECES THAT THE FILE's RULE TAKES (`piecesAt`, with
the cap laid), at the proof file's description, in the goals' scope: NO PREMISE ON A PIECE IS LEFT.

Main names:
  `hear_not_last`: whatever its kind, a block in front of a link's batching is not the last of the
    chain's flat list: the link's own batching block stands behind it. General in the chain.
  `pureDesc Z A B c`: the description as the seats' opening gives it.
  `k03_pieces_seated`: from the description's data, its seal, its three first blocks and its own
    test on the plan: `K3Pieces` at `piecesAt`'s first row.

A joining: `k03_pieces_of` (K3PiecesOf.lean) at `paidAtDesc` (the pieces hold the description's
blocks) and `seated_more` (Johnson/Desc/Sound/PieceSeated.lean: nothing behind the rounds; the
stretch is the block's declared rounds' data; the cap), which asks that the place is not the
chain's last: `hear_not_last` with the seats' numbering.

Limits: the goals' scope; the first chain; hD, hs and hp are premises on the description (its data
at a file, its seal, its test on the plan). Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3PiecesOf
import Johnson.Desc.Sound.PieceSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **A block in front of a link's batching is not the flat list's last.** -/
theorem hear_not_last {σ C : Type} {c : Desc.Chain σ C} {l i : ℕ} {Lk : Desc.Link σ C}
    {b : Desc.Block σ C} (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) :
    IM.flatIx c l i + 1 < c.blocksInOrder.length := by
  have hi : i < Lk.hear.length := (List.getElem?_eq_some_iff.1 h2).1
  have hlen : 1 + Lk.hear.length < Lk.blocksInOrder.length := by
    unfold Desc.Link.blocksInOrder
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h4 := IM.link_at_flat h1 (List.getElem?_eq_getElem hlen)
  have h5 := (List.getElem?_eq_some_iff.1 h4).1
  unfold IM.flatIx
  omega

/-- The description as the seats' opening gives it. -/
abbrev pureDesc (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (c : Desc.Chain Desc.First.S ProofFile.Cl) : Desc.FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- **`K3Pieces` at the pieces that the file's rule takes.** -/
theorem k03_pieces_seated {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Cells Tok : Type} (file : String) (D : WholeD)
    (hD : (pureDesc Z A B c).data file = .ok D) (hs : (pureDesc Z A B c).sealLast = true)
    (b₁ : Desc.Block (pureDesc Z A B c).S₁ (pureDesc Z A B c).Cl)
    (l₁ : List (Desc.Block (pureDesc Z A B c).S₁ (pureDesc Z A B c).Cl))
    (b₂ : Desc.Block (pureDesc Z A B c).S₂ (pureDesc Z A B c).Cl)
    (l₂ : List (Desc.Block (pureDesc Z A B c).S₂ (pureDesc Z A B c).Cl))
    (b₃ : Desc.Block (pureDesc Z A B c).S₃ (pureDesc Z A B c).Cl)
    (l₃ : List (Desc.Block (pureDesc Z A B c).S₃ (pureDesc Z A B c).Cl))
    (q₁ : (pureDesc Z A B c).first.blocksInOrder = b₁ :: l₁)
    (q₂ : (pureDesc Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (pureDesc Z A B c).second.blocksInOrder = b₃ :: l₃)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁) × (pureDesc Z A B c).S₂) ×
        (frameAt D (allOf D) D.key₂ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁ × (pureDesc Z A B c).S₂) ×
        (pureDesc Z A B c).S₃) ×
        (frameAt D (allOf D) D.key₃ (pureDesc Z A B c).lastChainFirstTreeNumber).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (d wEnd : Desc.Wit Cells Tok MsgT) (hp : (pureDesc Z A B c).planOk = true) :
    K3Pieces Bs.G₀.W Z.first.codes Z.first.shape
      ((piecesAt (ckP .two) (pureDesc Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).p₁ ::
        (piecesAt (ckP .two) (pureDesc Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).l₁) := by
  refine k03_pieces_of hS hR O
    (paidAtDesc _ _ (pureDesc Z A B c) file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃
      (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).1 hp ?_
  intro l hl dd q hq
  obtain ⟨Lk, b, b', h1, h2, -, -⟩ := IM.k3_of hS hR O l hl dd
  have hn := hear_not_last h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l dd)] at hn
  have x := (seated_more (pureDesc Z A B c) file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁
    e₂ e₃ d wEnd).1 _ q hq hn
  exact ⟨x.1.back, x.1.same, x.2⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hear_not_last
#print axioms VerifiableInference.OnPublicFiles.k03_pieces_seated
