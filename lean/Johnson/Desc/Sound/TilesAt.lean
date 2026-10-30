-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesAt.lean: **THE MAKER's PIECE AT A BLOCK OF A ROW, AND WHAT LIES BEHIND THE
BLOCKS IN FRONT OF IT.** One definition, three theorems; no kind is named. Cut by a program out of
Johnson/Desc/K12/Coin/GameTile.lean and GameHeld.lean, to the letter, so that whoever wants to know
where the maker `cutRow` (Johnson/Desc/Sound/Tiles.lean) lays a block's piece need not import the
proximity test's game. THE NAMES KEEP THEIR NAMESPACE (VerifiableInference.Desc.K12.Coin), so that
no caller turns a sign. The library's build takes this file in (lakefile.toml), and its names are declared in the namespace VerifiableInference.Desc.K12.Coin (line 24).
  `leftBehind pre base ds`: the next tree's number and the data that are left behind a row of
    blocks.
  `cutRow_at`: for every row of blocks pre ++ b :: b' :: post: the maker's piece number pre.length
    is the piece of b at what is left behind pre, with nothing put back.
  `nTrees_app`, `leftBehind_eq`: what is left behind, in closed form: the base plus the trees of the
    data that the blocks in front take; the data without these.
Limits. Nothing on soundness. Of a row's LAST block nothing is said.

-/
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Maker
open Iop _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound

section
variable {C : PQ.CK} {F : Frame} {S Cl W : Type}

/-- The next tree's number and the data that are left behind a row of blocks. -/
def leftBehind : List (Block S Cl) → ℕ → List RDT → ℕ × List RDT
  | [], base, ds => (base, ds)
  | b :: l, base, ds =>
    leftBehind l (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length)

/-- **The maker's piece at a block that is not the last.** -/
theorem cutRow_at (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (b b' : Block S Cl) (post : List (Block S Cl)) :
    ∀ (pre : List (Block S Cl)) (b₀ : Block S Cl) (l : List (Block S Cl)) (i base : ℕ)
      (ds : List RDT), b₀ :: l = pre ++ b :: b' :: post →
      ((cutRow rest putBack i base ds b₀ l).1 ::
        (cutRow rest putBack i base ds b₀ l).2)[pre.length]? =
        some (pieceOf b (leftBehind pre base ds).1
          ((leftBehind pre base ds).2.take b.rounds.length) []
          (rest (i + pre.length) ((leftBehind pre base ds).2.take b.rounds.length)))
  | [], b₀, l, i, base, ds, h => by
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    rfl
  | c :: pre, b₀, l, i, base, ds, h => by
    obtain ⟨rfl, hl⟩ := List.cons.inj h
    cases l with
    | nil => cases pre <;> cases hl
    | cons x l' =>
      have ih := cutRow_at rest putBack b b' post pre x l' (i + 1)
        (base + nTrees (ds.take b₀.rounds.length)) (ds.drop b₀.rounds.length) hl
      have ei : i + 1 + pre.length = i + (pre.length + 1) := by omega
      rw [ei] at ih
      exact ih

end

theorem nTrees_app (a b : List RDT) : nTrees (a ++ b) = nTrees a + nTrees b := by
  simp [Sound.nTrees]

/-- **What is left behind a row of blocks, in closed form.** -/
theorem leftBehind_eq {S Cl : Type} : ∀ (pre : List (Block S Cl)) (base : ℕ) (ds : List RDT),
    leftBehind pre base ds = (base + nTrees (ds.take (pre.map (·.rounds.length)).sum),
      ds.drop (pre.map (·.rounds.length)).sum)
  | [], base, ds => by simp [leftBehind, Sound.nTrees]
  | b :: l, base, ds => by
    show leftBehind l (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) = _
    rw [leftBehind_eq l, List.map_cons, List.sum_cons, List.take_add, nTrees_app, Nat.add_assoc,
      List.drop_drop]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.cutRow_at
#print axioms VerifiableInference.Desc.K12.Coin.leftBehind_eq
