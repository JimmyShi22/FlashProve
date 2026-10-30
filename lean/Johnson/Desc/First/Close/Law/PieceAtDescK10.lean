-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PieceAtDescK10.lean: THE MAKER's PIECE AT THE NUMBER OF A SUB-PROTOCOL
THAT DECLARES K10's ROUNDS, WRITTEN OUT, AT EVERY DESCRIPTION WHOSE DATA RETURN. One statement and
its proof. (In the Lean names a "block" is a sub-protocol and a "description" the IOP as written in
Lean.)

Why. `piece_at_desc` (Johnson/Road/K4/PieceAtDesc.lean, general in the kind) writes out
the piece number k of the first row that the maker cuts at a description (`piecesAt`,
Johnson/Desc/Sound/PaidAtDesc.lean): `pieceOf (held b) base ds [] (rest₁ k ds)`, with as many data
as b declares rounds, and the data b's declared rounds', round by round. That file draws K4's data
from it. Here K10's are drawn (`ds_of_along`, DataAlong.lean, beside this file).
  `k10_piece_at_desc`: under `piece_at_desc`'s own premises, b.rounds = (kind Q).rounds and both of
    Q's numbers of proof of work 0: there is a number base with: the first row's piece number k IS
    `pieceOf (held b) base (dBat Q.rows :: dEps :: Q.k times dTwo) [] (rest₁ k ..)`: THE VERY FORM
    IN WHICH `goodIn_at_maker` (GoodAtMaker.lean) ENDS.
Limits. Which sub-protocol stands at which number of the first chain is a premise; so are: the data
return; the first chain's last sub-protocol has a round (`sealLast`); each of the three flat lists
has a first member; k is not the last number. The two numbers of proof of work are premises. rest₁
is a letter. base stands under "there is". `goodIn_at_maker` is not called here. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.DataAlong
import Johnson.Road.K4.PieceAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- **THE MAKER's PIECE AT K10's NUMBER, WRITTEN OUT.** -/
theorem k10_piece_at_desc {Xi W Cl' : Type} {C : CK} (G : FileDescription Xi) (file : String)
    (D : WholeD) (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃
    (d wEnd : W) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (Q : Par) (w1 : Q.workField = 0) (w2 : Q.workClose = 0)
    (hr : b.rounds = (kind (Cl := Cl') Q).rounds) :
    ∃ base : ℕ,
      ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? =
          some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
            (rest₁ k (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) := by
  obtain ⟨base, ds, e1, e2, e3⟩ := OnBytes.Road.K4.piece_at_desc G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃
    h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd k b hk hk1
  rw [hr] at e3
  obtain rfl := ds_of_along _ Q w1 w2 ds e3 (by rw [e2, hr, kind_rounds_length])
  exact ⟨base, e1⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_piece_at_desc
