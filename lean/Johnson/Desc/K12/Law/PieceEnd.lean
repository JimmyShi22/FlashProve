-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PieceEnd.lean: where a piece of a description's own tiling stands and ends:
its block, its base, its data, and the number at which the next piece begins. General in the block:
no kind, no arm, no test on a plan; the description need not have data. A fact on the arithmetic of
the maker of pieces alone (`cutRow`, Johnson/Desc/Sound/Tiles.lean; `piecesAt`,
Johnson/Desc/Sound/PaidAtDesc.lean).

Why. A law with a key at a piece speaks of the key in front (at the piece's base) and the key behind
(at its base and the trees that it sends). That the key behind one piece is the key in front of the
next is this file's `piece_next₂`, whatever the two blocks are.
Main names.
  `cutRow_piece`: the maker's piece at a block that is not the row's last: block, nothing put back,
    base, data, and base and trees. Over `cutRow_at` (Johnson/Desc/K12/Coin/GameTile.lean) and
    `leftBehind_eq` (Coin/GameHeld.lean).
  `cutRow_base`: the maker's piece at any block of the row, the last too: block and base.
  `piece_end₁`, `piece_end₂`, `piece_end₃`: `cutRow_piece` at the three rows of `piecesAt`.
  `piece_next₂`: on the shared chain's row the piece behind begins where this one ends; it may be
    the row's last.
  `tiled_at`: THE KIN IN THE LIBRARY: `Tiled` (Johnson/Desc/Sound/ChainRule.lean) holds «the next
    piece's base is this one's base and trees» at each pair; here it is drawn at two neighbours by
    their numbers. Whoever holds that a description's pieces fit (`Fits`, from the data's yes) has
    it of every pair; `piece_next₂` has it of the maker's text alone.
`nTrees` is `VerifiableInference.Desc.Sound.nTrees` (Johnson/Desc/Sound/Cuts.lean) throughout,
written in full: other functions of that name lie in sight. `Piece.trees p` is that sum at `p.ds`.
Limits: of the row's last piece only the block and the base are said: not its data, not what is put
back. Nothing on a piece's errors or extractor. Nothing on what a block decides. No soundness is
claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.GameHeld
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Tile
open OnBytes OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound

/-! ## On the maker of a row -/

section
variable {C : PQ.CK} {F : Frame} {S Cl W : Type}

/-- The rounds that a row of blocks declares, counted two ways. -/
theorem rounds_sum (pre : List (Block S Cl)) :
    (pre.map (·.rounds.length)).sum = (pre.flatMap (·.rounds)).length := by
  rw [List.length_flatMap]

/-- The trees of the data's first n + m rounds. -/
theorem nTrees_take_add (ds : List RDT) (n m : ℕ) :
    VerifiableInference.Desc.Sound.nTrees (ds.take (n + m)) =
      VerifiableInference.Desc.Sound.nTrees (ds.take n) +
        VerifiableInference.Desc.Sound.nTrees ((ds.drop n).take m) := by
  rw [List.take_add]
  unfold VerifiableInference.Desc.Sound.nTrees
  rw [List.map_append, List.sum_append]

/-- **Where the maker's piece at a block that is not the last stands and ends.** -/
theorem cutRow_piece (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (b b' : Block S Cl) (post pre : List (Block S Cl)) (b₀ : Block S Cl) (l : List (Block S Cl))
    (i base : ℕ) (ds : List RDT) (h : b₀ :: l = pre ++ b :: b' :: post) :
    ∀ p, ((cutRow rest putBack i base ds b₀ l).1 ::
        (cutRow rest putBack i base ds b₀ l).2)[pre.length]? = some p →
      p.b = b ∧ p.back = [] ∧
        p.base = base + VerifiableInference.Desc.Sound.nTrees
          (ds.take (pre.flatMap (·.rounds)).length) ∧
        p.ds = (ds.drop (pre.flatMap (·.rounds)).length).take b.rounds.length ∧
        p.base + p.trees = base + VerifiableInference.Desc.Sound.nTrees
          (ds.take ((pre.flatMap (·.rounds)).length + b.rounds.length)) := by
  intro p hp
  have hat :=
    VerifiableInference.Desc.K12.Coin.cutRow_at rest putBack b b' post pre b₀ l i base ds h
  obtain rfl := Option.some.inj (hat.symm.trans hp)
  have hl := VerifiableInference.Desc.K12.Coin.leftBehind_eq pre base ds
  rw [rounds_sum] at hl
  have e1 : (VerifiableInference.Desc.K12.Coin.leftBehind pre base ds).1 =
      base + VerifiableInference.Desc.Sound.nTrees (ds.take (pre.flatMap (·.rounds)).length) := by
    rw [hl]
  have e2 : (VerifiableInference.Desc.K12.Coin.leftBehind pre base ds).2 =
      ds.drop (pre.flatMap (·.rounds)).length := by
    rw [hl]
  refine ⟨rfl, rfl, e1, ?_, ?_⟩
  · show (VerifiableInference.Desc.K12.Coin.leftBehind pre base ds).2.take b.rounds.length = _
    rw [e2]
  · show (VerifiableInference.Desc.K12.Coin.leftBehind pre base ds).1 +
      VerifiableInference.Desc.Sound.nTrees
        ((VerifiableInference.Desc.K12.Coin.leftBehind pre base ds).2.take b.rounds.length) = _
    rw [e1, e2, nTrees_take_add, Nat.add_assoc]

/-- **Where the maker's piece at any block of the row, the last too, begins.** -/
theorem cutRow_base (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (b : Block S Cl) (post : List (Block S Cl)) :
    ∀ (pre : List (Block S Cl)) (b₀ : Block S Cl) (l : List (Block S Cl)) (i base : ℕ)
      (ds : List RDT), b₀ :: l = pre ++ b :: post →
      ∀ p, ((cutRow rest putBack i base ds b₀ l).1 ::
          (cutRow rest putBack i base ds b₀ l).2)[pre.length]? = some p →
        p.b = b ∧ p.base = base + VerifiableInference.Desc.Sound.nTrees
          (ds.take (pre.flatMap (·.rounds)).length)
  | [], b₀, l, i, base, ds, h, p, hp => by
    have hb : b₀ = b := (List.cons.inj h).1
    obtain rfl : (cutRow rest putBack i base ds b₀ l).1 = p := Option.some.inj hp
    cases l with
    | nil => exact ⟨hb, by simp [cutRow, pieceOf, VerifiableInference.Desc.Sound.nTrees]⟩
    | cons x y => exact ⟨hb, by simp [cutRow, pieceOf, VerifiableInference.Desc.Sound.nTrees]⟩
  | c :: pre, b₀, l, i, base, ds, h, p, hp => by
    obtain ⟨rfl, hl⟩ := List.cons.inj h
    cases l with
    | nil => cases pre <;> cases hl
    | cons x l' =>
      have ih := cutRow_base rest putBack b post pre x l' (i + 1)
        (base + VerifiableInference.Desc.Sound.nTrees (ds.take b₀.rounds.length))
        (ds.drop b₀.rounds.length) hl p hp
      refine ⟨ih.1, ?_⟩
      rw [ih.2, List.flatMap_cons, List.length_append, nTrees_take_add, Nat.add_assoc]

end

/-! ## At the three rows of a description's own tiling -/

section
variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (d wEnd : W)

/-- A row of blocks as pieces hold them declares the blocks' own rounds. -/
theorem held_flat {P S Cl : Type} (pre : List (Block S Cl)) :
    ((pre.map (held (P := P))).flatMap (·.rounds)).length = (pre.flatMap (·.rounds)).length := by
  rw [List.flatMap_map]
  rfl

/-- **The shared chain's row.** -/
theorem piece_end₂ (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl)
    (post : List (Block F.S₂ F.Cl)) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post) :
    ∀ p, ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p →
      p.b = held B ∧ p.back = [] ∧
        p.base = D.t₁ + VerifiableInference.Desc.Sound.nTrees
          (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧
        p.ds = (D.ds₂.drop (pre.flatMap (·.rounds)).length).take B.rounds.length ∧
        p.base + p.trees = D.t₁ + VerifiableInference.Desc.Sound.nTrees
          (D.ds₂.take ((pre.flatMap (·.rounds)).length + B.rounds.length)) := by
  intro p hp
  have hL : held (P := F.XiPub × F.S₁) b₂ :: l₂.map held =
      pre.map held ++ held B :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub × F.S₁))) hcut
    simpa using this
  have h := cutRow_piece rest₂ [] (held B) (held b') (post.map held) (pre.map held) (held b₂)
    (l₂.map held) 0 D.t₁ D.ds₂ hL p (by rw [List.length_map]; exact hp)
  rw [held_flat] at h
  exact h

/-- **The first chain's row.** -/
theorem piece_end₁ (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl)
    (post : List (Block F.S₁ F.Cl)) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post) :
    ∀ p, ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p →
      p.b = held B ∧ p.back = [] ∧
        p.base = 0 + VerifiableInference.Desc.Sound.nTrees
          (D.ds₁.take (pre.flatMap (·.rounds)).length) ∧
        p.ds = (D.ds₁.drop (pre.flatMap (·.rounds)).length).take B.rounds.length ∧
        p.base + p.trees = 0 + VerifiableInference.Desc.Sound.nTrees
          (D.ds₁.take ((pre.flatMap (·.rounds)).length + B.rounds.length)) := by
  intro p hp
  have hL : held (P := F.XiPub) b₁ :: l₁.map held =
      pre.map held ++ held B :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub))) hcut
    simpa using this
  have h := cutRow_piece rest₁ [sealRound] (held B) (held b') (post.map held) (pre.map held)
    (held b₁) (l₁.map held) 0 0 D.ds₁ hL p (by rw [List.length_map]; exact hp)
  rw [held_flat] at h
  exact h

/-- **The last chain's row.** -/
theorem piece_end₃ (pre : List (Block F.S₃ F.Cl)) (B b' : Block F.S₃ F.Cl)
    (post : List (Block F.S₃ F.Cl)) (hcut : b₃ :: l₃ = pre ++ B :: b' :: post) :
    ∀ p, ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₃ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₃)[pre.length]? =
        some p →
      p.b = held B ∧ p.back = [] ∧
        p.base = D.t₁ + D.t₂ + VerifiableInference.Desc.Sound.nTrees
          (D.ds₃.take (pre.flatMap (·.rounds)).length) ∧
        p.ds = (D.ds₃.drop (pre.flatMap (·.rounds)).length).take B.rounds.length ∧
        p.base + p.trees = D.t₁ + D.t₂ + VerifiableInference.Desc.Sound.nTrees
          (D.ds₃.take ((pre.flatMap (·.rounds)).length + B.rounds.length)) := by
  intro p hp
  have hL : held (P := F.XiPub × F.S₁ × F.S₂) b₃ :: l₃.map held =
      pre.map held ++ held B :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub × F.S₁ × F.S₂))) hcut
    simpa using this
  have h := cutRow_piece rest₃ [] (held B) (held b') (post.map held) (pre.map held) (held b₃)
    (l₃.map held) 0 (D.t₁ + D.t₂) D.ds₃ hL p (by rw [List.length_map]; exact hp)
  rw [held_flat] at h
  exact h

/-- **The keys meet on the shared chain's row**: whatever stands behind the piece of a block that is
not the last, the row's last piece too, begins where that piece ends. -/
theorem piece_next₂ (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl)
    (post : List (Block F.S₂ F.Cl)) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post) :
    ∀ p q, ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p →
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length + 1]? =
        some q → q.b = held b' ∧ q.base = p.base + p.trees := by
  intro p q hp hq
  obtain ⟨_, _, _, _, e⟩ := piece_end₂ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd pre B b' post
    hcut p hp
  have hL : held (P := F.XiPub × F.S₁) b₂ :: l₂.map held =
      (pre ++ [B]).map held ++ held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub × F.S₁))) hcut
    simpa using this
  have h := cutRow_base rest₂ [] (held b') (post.map held) ((pre ++ [B]).map held) (held b₂)
    (l₂.map held) 0 D.t₁ D.ds₂ hL q (by
      rw [List.length_map, List.length_append]
      exact hq)
  rw [held_flat, List.flatMap_append, List.length_append] at h
  refine ⟨h.1, ?_⟩
  rw [e, h.2]
  simp

end

/-! ## The kin in the library -/

/-- `Tiled` (Johnson/Desc/Sound/ChainRule.lean) at two neighbours of a row: the next piece begins
where this one ends. General in the pieces: no maker is named. -/
theorem tiled_at {C : PQ.CK} {F : Frame} {S Cl W : Type} :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W), Tiled p l → ∀ (i : ℕ) (x y),
      (p :: l)[i]? = some x → (p :: l)[i + 1]? = some y → y.base = x.base + x.trees
  | [], _, _, i, x, y, _, hy => by
    cases i <;> simp at hy
  | q :: l, p, h, 0, x, y, hx, hy => by
    obtain rfl : p = x := Option.some.inj hx
    obtain rfl : q = y := Option.some.inj hy
    exact h.2.2.2.1
  | q :: l, p, h, i + 1, x, y, hx, hy => tiled_at l q h.2.2.2.2 i x y hx hy

end H2K.Tile

#print axioms H2K.Tile.cutRow_piece
#print axioms H2K.Tile.cutRow_base
#print axioms H2K.Tile.piece_end₁
#print axioms H2K.Tile.piece_end₂
#print axioms H2K.Tile.piece_end₃
#print axioms H2K.Tile.piece_next₂
#print axioms H2K.Tile.tiled_at
