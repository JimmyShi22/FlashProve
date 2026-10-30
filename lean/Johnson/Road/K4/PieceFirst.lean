-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceFirst.lean: K4's PIECE IN THE FIRST GROUP: ITS STRETCH IS `dsFirst par`
(Johnson/Road/K4/PlanMapsFirst.lean). THE FIRST GROUP's TWIN OF Johnson/Road/K4/PieceLater.lean: two
statements: `k4_piece_at_desc` (Johnson/Road/K4/PieceAtDesc.lean) and `k04_piece`
(Johnson/Road/K4/PieceAtFits.lean), with `k4Ds_first` (Johnson/Road/K4/DsTailR.lean) laid in, whose
right side is `dsFirst par`'s body. Turned from PieceLater.lean by program.

  Both: where block number k of the first chain is b, a block number k + 1 stands, and b declares
  K4's rounds at par (`Declares`), in the first group.
  `k4_piece_first`: at the maker's own cut: the first row's piece number k is
    `pieceOf (held b) base (dsFirst par) [] (rest₁ k (dsFirst par))`.
  `k04_piece_first`: at any rows that hold the description's blocks and tile its first chain:
    q.b = held b, q.back = [], q.ds = dsFirst par.

Limits: those of the two files named. Nothing on soundness.
-/
import Johnson.Road.K4.PieceAtFits
import Johnson.Road.K4.DsTailR
import Johnson.Road.K4.PlanMapsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Desc.First.K4 (Par k4Ds)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound

variable {W Xi : Type} {C : CK}

/-- **At the maker's own cut.** -/
theorem k4_piece_first (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃
    (d wEnd : W) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) {par : Par} (hd : Declares b par)
    (hg : (par.g == 0) = true) :
    ∃ base : ℕ,
      ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? =
          some (pieceOf (held b) base (dsFirst par) [] (rest₁ k (dsFirst par))) := by
  obtain ⟨base, ds, e, hds⟩ := k4_piece_at_desc (C := C) G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃
    rest₁ rest₂ rest₃ d wEnd k b hk hk1 hd
  obtain rfl : dsFirst par = ds := Option.some.inj ((k4Ds_first hg).symm.trans hds)
  exact ⟨base, e⟩

/-- **At any rows that hold the description's blocks and tile its first chain.** -/
theorem k04_piece_first (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) {par : Par} (hdc : Declares b par)
    (hg : (par.g == 0) = true) : q.b = held b ∧ q.back = [] ∧ q.ds = dsFirst par := by
  obtain ⟨hqb, hb, hK⟩ := k04_piece G file D hD R hO ht hd hq hk hk1 hdc
  exact ⟨hqb, hb, (Option.some.inj ((k4Ds_first hg).symm.trans hK)).symm⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_piece_first
#print axioms OnBytes.Road.K4.k04_piece_first
