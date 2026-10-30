-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BelowAtCuts.lean: THE THREE BOUNDS AT THE PIECES THAT THE MAKER CUTS, FROM ONE
BOUND ON THE LETTER THAT GIVES A PIECE ITS ERRORS.

The maker of the pieces (`cutRow`, Johnson/Desc/Sound/Tiles.lean) gives the block number i, at the
stretch ds of the chain's data, the errors `(rest i ds).err`. So "every block of the chain has its
own errors at most c" (`EachBelow`, Johnson/Desc/Sound/BelowOfBlocks.lean) is just: `rest`'s errors
are, at the blocks' numbers and stretches.

  `EachBelow.mono`       a bound may grow.
  `eachBelow_cutRow`     at `cutRow`, from the bound at all numbers and stretches.
  `BelowAlong`, `eachBelow_cutRow_iff`   the bound block by block, at each block's own number and
                         stretch: just that.
  `eachBelow_pieces₁ | ₂ | ₃`   at a description's own three rows of pieces
                         (`atDesc F (piecesAt …)`): the form in which a file's debt on the plain
                         road asks the three bounds.

Limits. Book-keeping on lists: no round is evaluated, no block of the protocol is named, and nothing
says that c is small or that `rest`'s errors are those at which a block's law holds.
-/
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.BelowOfBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- A bound on every block's errors may grow. -/
theorem EachBelow.mono {c c' : ℝ≥0∞} (h : c ≤ c') {l : List (Piece C F S Cl W)}
    (hb : EachBelow c l) : EachBelow c' l :=
  fun q hq => Err.Below.mono_bound h (hb q hq)

/-- **At the maker's pieces.** -/
theorem eachBelow_cutRow (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (c : ℝ≥0∞) (h : ∀ i ds, Err.Below (rest i ds).err c) :
    ∀ (l : List (Block S Cl)) (i base : ℕ) (ds : List RDT) (b : Block S Cl),
      EachBelow c ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)
  | [], i, base, ds, b => by
    intro q hq
    rw [cutRow] at hq
    obtain rfl : q = pieceOf b base ds putBack (rest i ds) := by simpa using hq
    exact h i ds
  | b' :: l, i, base, ds, b => by
    intro q hq
    rw [cutRow] at hq
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact h i _
    · exact eachBelow_cutRow rest putBack c h l _ _ _ b' q hq'

/-- The bound, block by block: at each block's own number and its own stretch of the data, and
nowhere else. -/
def BelowAlong (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (c : ℝ≥0∞) :
    ℕ → List RDT → Block S Cl → List (Block S Cl) → Prop
  | i, ds, _, [] => Err.Below (rest i ds).err c
  | i, ds, b, b' :: l =>
    Err.Below (rest i (ds.take b.rounds.length)).err c ∧
      BelowAlong rest c (i + 1) (ds.drop b.rounds.length) b' l

/-- **The maker's pieces have their errors at most c just if each block has, at its own number and
stretch.** -/
theorem eachBelow_cutRow_iff (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds)
    (putBack : List Fmt.RoundView) (c : ℝ≥0∞) :
    ∀ (l : List (Block S Cl)) (i base : ℕ) (ds : List RDT) (b : Block S Cl),
      EachBelow c ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2) ↔
        BelowAlong rest c i ds b l
  | [], i, base, ds, b => by
    rw [cutRow, BelowAlong]
    constructor
    · exact fun h => h _ List.mem_cons_self
    · intro h q hq
      obtain rfl : q = pieceOf b base ds putBack (rest i ds) := by simpa using hq
      exact h
  | b' :: l, i, base, ds, b => by
    rw [cutRow, BelowAlong, ← eachBelow_cutRow_iff rest putBack c l (i + 1)
      (base + nTrees (ds.take b.rounds.length)) (ds.drop b.rounds.length) b']
    constructor
    · exact fun h => ⟨h _ List.mem_cons_self, fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    · rintro ⟨h₁, h₂⟩ q hq
      rcases List.mem_cons.1 hq with rfl | hq'
      · exact h₁
      · exact h₂ q hq'

variable {Xi : Type}

/-- **At a description's first chain's pieces.** -/
theorem eachBelow_pieces₁ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (c : ℝ≥0∞) (h : ∀ i ds, Err.Below (rest₁ i ds).err c) :
    EachBelow c ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₁ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₁) :=
  eachBelow_cutRow rest₁ _ c h _ _ _ _ _

theorem eachBelow_pieces₂ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (c : ℝ≥0∞) (h : ∀ i ds, Err.Below (rest₂ i ds).err c) :
    EachBelow c ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂) :=
  eachBelow_cutRow rest₂ _ c h _ _ _ _ _

theorem eachBelow_pieces₃ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (c : ℝ≥0∞) (h : ∀ i ds, Err.Below (rest₃ i ds).err c) :
    EachBelow c ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₃ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₃) :=
  eachBelow_cutRow rest₃ _ c h _ _ _ _ _

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachBelow_cutRow
#print axioms VerifiableInference.Desc.Sound.eachBelow_cutRow_iff
#print axioms VerifiableInference.Desc.Sound.eachBelow_pieces₁
