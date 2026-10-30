-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendWords.lean: the premise of the law of a sending on the reader of the
words (of the stretch's transcript it reads the first round's message alone) is met by every reader
that reads, of the oracles behind the block, columns of the trees that the stretch's first round
sends.

Main names:
  colsOf       the column of the oracles at (a tree's number through the file, a leaf).
  firstCols    the column of a first round's prover message at (the round's tree number n, a leaf).
  posL_spec    what a position in a list of trees left is.
  cols_behind  behind a piece, at a tree that its stretch's first round sends, the oracles' column
               is the first round's message's, or nothing where the frame does not list the place.
  ReadsFirst   a reader of columns reads the first n trees alone.
  words_first  **the premise, met**: for the piece of a sending whose block goes on.
  words_first_two   the like for the piece of a sending with two rounds.

What is not claimed. Which reader of columns gives the library's word of a message (how a tree's
columns hold its tenants' symbols) is not said. Nothing on soundness of a protocol, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- The column of the oracles at (a tree's number through the file, a leaf); nothing where the frame
does not list the place. -/
def colsOf (F : Frame) (y : F.E.Str) (j x : Nat) : List UInt64 :=
  ((posL F.all j x).map y.2).getD []

/-- The column of a first round's prover message at (the round's tree number n, a leaf). -/
def firstCols (d : RDT) (m : (wT d).Msg) (n x : Nat) : List UInt64 :=
  ((posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)).getD []

theorem posL_spec (L : List LeftT) (j x : Nat) (p : PosL L) (h : posL L j x = some p) :
    (L.get p.1).no = j ∧ p.2.val = x := by
  unfold posL at h
  obtain ⟨i, _, hi⟩ := List.exists_of_findSome?_eq_some h
  split at hi
  · rename_i hno
    split at hi
    · obtain rfl := Option.some.inj hi
      exact ⟨hno, rfl⟩
    · cases hi
  · cases hi

variable {T Cl W : Type} {F : Frame}

/-- **Behind a piece, at a tree that its stretch's first round sends.** -/
theorem cols_behind (b : Block T Cl) (base : Nat) (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView)
    (ext : T × F.E.Str → Tr (uLT (ckP .two) (d₁ :: ds)) → W → W)
    (err : Err (uLT (ckP .two) (d₁ :: ds))) (y : F.E.Str) (τ : Tr (uLT (ckP .two) (d₁ :: ds)))
    (n x : Nat) (hn : n < d₁.trees.length) :
    colsOf F ((⟨b, base, d₁ :: ds, back, ext, err⟩ : Piece (ckP .two) F T Cl W).ior.imp y τ)
        (base + n) x =
      if (posL F.all (base + n) x).isSome then firstCols d₁ τ.1 n x else [] := by
  unfold colsOf
  cases hp : posL F.all (base + n) x with
  | none => rfl
  | some q =>
    obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hp
    show (sCol (ckP .two) ⟨F.a, base, F.all, d₁ :: ds, F.key, F.all⟩ y τ
      (.tree (F.all.get q.1).no q.2.val)).getD [] = _
    rw [h1, h2]
    show (if base + n < base then _ else colAtST (ckP .two) (d₁ :: ds) τ (base + n - base) x).getD
      [] = _
    rw [if_neg (by omega), Nat.add_sub_cancel_left, colAtST_cons, if_pos hn]
    rfl

/-- A reader of columns reads the first n trees alone. -/
def ReadsFirst {α : Type} (n : Nat) (G : (Nat → Nat → List UInt64) → α) : Prop :=
  ∀ c c', (∀ j, j < n → ∀ x, c j x = c' j x) → G c = G c'

/-- **The premise on the reader of the words, met.** -/
theorem words_first {α : Type} (G : (Nat → Nat → List UInt64) → α) (b : Block T Cl) (base : Nat)
    (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (c e : Nat)
    (hG : ReadsFirst d₁.trees.length G) (y : F.E.Str) (τ : Tr (uLT (ckP .two) (d₁ :: ds))) :
    G (fun j x => colsOf F ((openPiece (W := W) (F := F) b base d₁ ds back c e).ior.imp y τ)
        (base + j) x) =
      G fun j x => if (posL F.all (base + j) x).isSome then firstCols d₁ τ.1 j x else [] :=
  hG _ _ fun j hj x => cols_behind b base d₁ ds back _ _ y τ j x hj

/-- The like for the piece of a sending with two rounds. -/
theorem words_first_two {α : Type} (G : (Nat → Nat → List UInt64) → α) (b : Block T Cl)
    (base : Nat) (d₁ d₂ : RDT) (c e : Nat) (hG : ReadsFirst d₁.trees.length G) (y : F.E.Str)
    (τ : Tr (uLT (ckP .two) [d₁, d₂])) :
    G (fun j x => colsOf F ((sendPiece (W := W) (F := F) b base d₁ d₂ c e).ior.imp y τ)
        (base + j) x) =
      G fun j x => if (posL F.all (base + j) x).isSome then firstCols d₁ τ.1 j x else [] :=
  hG _ _ fun j hj x => cols_behind b base d₁ [d₂] [] _ _ y τ j x hj

end VerifiableInference.Desc.K1
