-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PiecesOf.lean: the kind "lookup" (K3): the second of the three structures
of Johnson/Desc/First/Look/K3LawOfR.lean, `K3Pieces`, AT THE PROOF FILE's DESCRIPTION, in the goals'
scope: from the description's own test on the plan and three plain facts on each of the fifty
pieces.

Main name:
  `k03_pieces_of`: the description's `planOk` says yes; at each of the fifty pieces q: nothing is
    put behind its rounds, its stretch is round by round the data of ITS OWN BLOCK's declared
    rounds, its error is the cap: then `K3Pieces`: the constants pass their own test on the plan,
    and each piece's stretch is the data of THE PLACE's rounds.

What is shown here beyond a sorting: (1) the constant's test on the plan, out of the description's
(the seat's wrappers leave it: `IM.alone_planOk`; `Keeps.planOk_blocks`); (2) from "its own block's
rounds" to "the place's rounds": the piece holds the seated block under the strict reading, lifted
(`OfDesc.pieceAt`); the seat leaves the rounds (`IM.alone_rounds`); the constant's rounds are the
place's (`K3Lot.k03_place`).

WHO PAYS hM: Johnson/Desc/Sound/PieceMore.lean (`PieceMore.back`, `PieceMore.same`) and
PieceSeated.lean (`seated_more`) give the three facts at a piece of the file's rule AT EVERY PLACE
OF THE FIRST CHAIN BUT ITS LAST (k + 1 below the blocksInOrder list's length). They are not imported here;
`SameAs` and `PieceMore.same`'s sentence have one body, by reading. THAT THE FIFTY NUMBERS (the
greatest: 14 * 24 + 7 + 2) LIE IN FRONT OF THE LAST PLACE IS NOT SHOWN HERE: whoever calls
`seated_more` owes it.

Limits: the goals' scope; the first chain. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **`K3Pieces` at the proof file's description.** -/
theorem k03_pieces_of {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Cells Tok : Type} {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit Cells Tok MsgT)}
    (hT : OfDesc _ T)
    (hp : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true)
    (hM : ∀ l, l < 25 → ∀ (d : Bool) q, (T.p₁ :: T.l₁)[k3K l d]? = some q →
      q.back = [] ∧ List.Forall₂ SameAs q.ds q.b.rounds ∧
        q.err = Err.cap 128 (uLT (ckP .two) q.ds)) :
    K3Pieces Bs.G₀.W Z.first.codes Z.first.shape (T.p₁ :: T.l₁) where
  planOk := by
    intro l hl d b' hb
    obtain ⟨Lk, b, b₁, h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl d
    obtain rfl : b₁ = b' := Option.some.inj (h3.symm.trans hb)
    have h5 := IM.hear_at_flat h1 h2
    rw [← IM.alone_planOk h4]
    exact (Desc.Keeps.planOk_blocks _ hp).1 b (List.mem_of_getElem? h5)
  back := fun l hl d q hq => (hM l hl d q hq).1
  cap := fun l hl d q hq => (hM l hl d q hq).2.2
  rounds := by
    intro l hl d q hq p hpl
    obtain ⟨Lk, b, b₁, h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl d
    have h5 := IM.hear_at_flat h1 h2
    rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l d)] at h5
    have hqb := OfDesc.pieceAt hT hq h5
    obtain ⟨-, p', hp', hr⟩ :=
      K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape l
        d b₁ h3
    obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hpl)
    have h6 := (hM l hl d q hq).2.1
    rw [hqb] at h6
    have h7 : List.Forall₂ SameAs q.ds b.rounds := h6
    rw [(IM.alone_rounds h4).trans hr] at h7
    exact h7

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k03_pieces_of
