-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/CutAt.lean: THE MAKER OF THE PIECES (cutRow, Johnson/Desc/Sound/Tiles.lean) AT
AN INDEX, IN CLOSED FORM. A general law on that maker, at every list of blocks; no kind is named.

WHY. A block's law is owed at the piece that the maker cuts. The other laws on the maker speak of
the whole row (its blocks, its data, its first base) or of every piece alike. Whoever ties a law to
THE PIECE AT A PLACE wants that piece: its block, its first tree's number, its stretch, its rest.

  roundsIn l   the rounds that the blocks of l declare, counted.
  cutRow_at    **the piece number j of the row, j not the last**: it holds the block number j; its
               base is the row's base and the trees sent in the rounds in front; its stretch is as
               many rounds as its block declares, behind the rounds in front; nothing is put behind
               it; and it IS pieceOf of these, with the rest that the letter gives at i + j.
What is not claimed. Anything of the last piece (it takes what is left). That the data have as many
rounds as are declared. Nothing on soundness.

-/
import Johnson.Desc.Sound.TilesCutProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece Rest cutRow pieceOf nTrees cutRow_cons)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- The rounds that the blocks of l declare, counted. -/
def roundsIn (l : List (Block S Cl)) : Nat := (l.map (·.rounds.length)).sum

theorem nTrees_append (a b : List RDT) : nTrees (a ++ b) = nTrees a + nTrees b := by
  simp [nTrees]

/-- **The maker's piece at an index.** -/
theorem cutRow_at (rest : (i : Nat) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl) (i base : Nat) (ds : List RDT) (j : Nat)
      (x : Block S Cl), (b :: l)[j]? = some x → j < l.length →
      ∃ q : Piece C F S Cl W,
        ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[j]? =
          some q ∧
        q.b = x ∧ q.base = base + nTrees (ds.take (roundsIn ((b :: l).take j))) ∧
        q.ds = (ds.drop (roundsIn ((b :: l).take j))).take x.rounds.length ∧ q.back = [] ∧
        q = pieceOf x q.base q.ds [] (rest (i + j) q.ds) := by
  intro l
  induction l with
  | nil => intro b i base ds j x _ hj; exact absurd hj (Nat.not_lt_zero _)
  | cons b' l ih =>
    intro b i base ds j x hx hj
    rw [cutRow_cons]
    cases j with
    | zero =>
      have e : b = x := by simpa using hx
      subst e
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [roundsIn, nTrees, pieceOf]
      · simp [roundsIn, pieceOf]
    | succ j =>
      have hx' : (b' :: l)[j]? = some x := by simpa using hx
      have hj' : j < l.length := by simpa using hj
      obtain ⟨q, h0, h1, h2, h3, h4, h5⟩ := ih b' (i + 1)
        (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) j x hx' hj'
      have hn : roundsIn ((b :: b' :: l).take (j + 1)) =
          b.rounds.length + roundsIn ((b' :: l).take j) := by
        simp [roundsIn]
      refine ⟨q, by simpa using h0, h1, ?_, ?_, h4, ?_⟩
      · rw [h2, hn, List.take_add, nTrees_append, Nat.add_assoc]
      · rw [h3, hn, List.drop_drop]
      · have e : i + 1 + j = i + (j + 1) := by omega
        rw [← e]
        exact h5

end Desc.K14.Law
