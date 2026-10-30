-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PieceEq.lean: THE PIECE AS ONE EQUATION: the piece that holds
the approximate range proof's sub-protocol (our files: the smallness test's block, K8), read at a
sub-protocol B' in the place of its own, IS the piece at the draw's one round `rdt p`, with no round laid
behind it and the cap at 128 as its errors. Statements and proofs: substitution; no new mathematics.

  `k08_piece_eq`: from the three facts on the piece (Johnson/Desc/First/K8/PieceFacts.lean): general in
    the clock, the frame, the piece's own types and B'.
  `k08_piece_at_maker`: at the maker's own rows (`piecesAt`) whose first letter lays the cap
    (`AtCap`): at a number k, not the last, whose sub-protocol has the kind's rounds: there is the
    piece at that number, it holds that sub-protocol, and the equation holds of it at every B'.
Limits. That the sub-protocol at each of the 25 numbers has the kind's rounds is a premise here.
Shown at no filling. No soundness is claimed.

-/
import Johnson.Desc.First.K8.PieceFacts
import Johnson.Desc.First.K8.TieLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)

/-- **The piece as one equation, from the three facts.** -/
theorem k08_piece_eq {C : CK} {Fr : Frame} {T Cl' W : Type} (q : Piece C Fr T Cl' W) (p : Par)
    (hb : q.back = []) (hds : q.ds = [rdt p]) (herr : q.err = Iop.Err.cap 128 (uLT C q.ds))
    (B' : Block S Claim) :
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W) =
      ⟨below B', q.base, [rdt p], [], fun _ _ w => w, Iop.Err.cap 128 (uLT C [rdt p])⟩ := by
  obtain ⟨b, base, ds, back, ext, err⟩ := q
  dsimp only at hb hds herr ⊢
  subst hb
  subst hds
  subst herr
  rfl

/-- **At the maker's own rows.** -/
theorem k08_piece_at_maker {Xi : Type} {C : CK} {W : Type} (G : FileDescription Xi) (file : String)
    (D : WholeD) (hD : G.data file = .ok D) (hs : G.sealLast = true) (b₁ : Block G.S₁ G.Cl)
    (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl) (l₂ : List (Block G.S₂ G.Cl))
    (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (h₁ : G.first.blocksInOrder = b₁ :: l₁)
    (h₂ : G.shared.blocksInOrder = b₂ :: l₂) (h₃ : G.second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃ (d wEnd : W)
    (hc : AtCap rest₁) (k : ℕ) (b : Block G.S₁ G.Cl) (hk : G.first.blocksInOrder[k]? = some b)
    (hk1 : k + 1 < G.first.blocksInOrder.length) (p : Par) (hr : b.rounds = [round p]) :
    ∃ q, ((piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt C G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[k]? = some q ∧
      q.b = held b ∧ ∀ B' : Block S Claim,
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
            Piece C (Sound.frameAt D (Sound.allOf D) D.key₁ 0) S Claim W) =
          ⟨below B', q.base, [rdt p], [], fun _ _ w => w, Iop.Err.cap 128 (uLT C [rdt p])⟩ := by
  obtain ⟨q, hq, hqb, hb, hds, herr⟩ := k08_facts_at_maker G file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂
    h₃ rest₁ rest₂ rest₃ d wEnd hc k b hk hk1 p hr
  exact ⟨q, hq, hqb, fun B' => k08_piece_eq q p hb hds herr B'⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_piece_eq
#print axioms VerifiableInference.Desc.First.K8.k08_piece_at_maker
