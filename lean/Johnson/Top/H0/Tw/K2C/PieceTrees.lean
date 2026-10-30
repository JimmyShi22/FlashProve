-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PieceTrees.lean: code switching (the kind K2): THE FIRST WRITTEN ROUND OF
THE SWITCH's STRETCH SENDS JUST THE TREES OF THE SENDING's LAYOUT. Beside K2C/PieceFacts.lean,
which does not turn. NO BLOCK IMPORTS THIS FILE.
  rounds_roots     the two declared rounds count p.roots roots and none
  k2_piece_trees   under k2_piece's premises: the stretch's written rounds send p.roots trees and
                   none
  numsAt_roots     the lot's numbers at a place: roots is the number of the trees of the program's
                   layout of what the place's sending announces
CALLED, NOT TYPED: trees_along (Johnson/Desc/Book/SeatOfLay.lean) · fits_piece
(Johnson/Road/K4/PieceAtFits.lean). For the law's premise «each new member's tree is one that the
first written round of the stretch sends» (hseat_of_lay_at, SeatOfLay.lean). On the plan and the
written rounds alone. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.PieceFacts
import Johnson.Desc.Book.SeatOfLay
import Johnson.Desc.ProofFile.Lot.K2OfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

theorem rounds_roots (p : P2) : (rounds p).map (·.entry.roots) = [p.roots, 0] := rfl

theorem k2_piece_trees {Xi W : Type} {C : CK} (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
    (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W} {b : Block G.S₁ G.Cl}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : P2) (hb : b.rounds = rounds p) :
    q.ds.map (·.trees.length) = [p.roots, 0] := by
  obtain ⟨_, _, hl, hA⟩ := OnBytes.Road.K4.fits_piece G file D hD R hO ht hd hq hk hk1
  rw [VerifiableInference.Desc.Book.trees_along _ q.ds hl hA, hb]
  rfl

end VerifiableInference.Desc.First.K2

namespace P1K2
open OnBytes

theorem numsAt_roots {P : Prep} {link : Option Nat} {n : Nums} (h : numsAt P link = some n) :
    ∃ lay, layTrees n.codes n.sent = some lay ∧ n.roots = lay.shapes.size := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, hl, rd, _, rfl⟩ := h
    exact ⟨lay, hl, rfl⟩

end P1K2

#print axioms VerifiableInference.Desc.First.K2.k2_piece_trees
#print axioms P1K2.numsAt_roots
