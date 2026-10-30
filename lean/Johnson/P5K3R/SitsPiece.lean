-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsPiece.lean: the row K03_sits at the proof file, carried from the description's
list of blocks to the pieces of the rule for a file. One theorem, a joining.

Why. The laws of the kind "lookup" speak of a piece whose block is the strict reading of a block
that narrows the value of `K3.theStated`. The rule for a file speaks of three rows of pieces that
hold the description's own blocks (`OfDesc`). Here the two meet at the proof file's written
description.

Main names:
  `k03_piece`: at the letters that the walk through the maker hands out (`IM.Open`), for public
    files in scope: where three rows of pieces hold the blocks of the description made of the first
    chain c, for every link l below 25 and both lookups: whatever piece q stands at the number
    14 l + i + 2 of the first row holds the strict reading of a block b, lifted over the public
    part; the kind's own text returns a block b' at the driver's address; b narrows b'; a yes of b
    leaves no mark.

Whose lemmas: `OfDesc.pieceAt` stands in Johnson/Desc/Sound/AtDriver.lean; the rest as in
Johnson/P5K3R/Sits.lean.

Limits: as in Johnson/P5K3R/Sits.lean. That three such rows of pieces exist is a premise
(`OfDesc`). No law of the kind is called here. Nothing on soundness; nothing on hiding.


-/
import Johnson.P5K3R.Sits
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **K03_sits, at the pieces.** -/
theorem k03_piece {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (l : ℕ) (hl : l < 25) (digits : Bool)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + IM.k3Ix l digits + 2]? = some q) :
    ∃ b b' : Block S Cl,
      VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W
        Z.first.codes Z.first.shape (IM.k3Place l digits) = some b' ∧
      q.b = (below b).lift Prod.snd (fun t s => (t.1, s)) ∧
      b.Narrows b' ∧ ∀ s rs gs t, b.decide s rs gs = .ok t → t.failed = none := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl digits
  have h5 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l digits)] at h5
  refine ⟨b, b', h3, OfDesc.pieceAt hT hq h5, IM.alone_underR h4, ?_⟩
  intro s rs gs t hy
  exact ((IM.k3_yes h4 s t rs gs).1 hy).2.1

end K3Lot
