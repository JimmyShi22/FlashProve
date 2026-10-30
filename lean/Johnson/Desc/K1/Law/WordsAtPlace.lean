-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/WordsAtPlace.lean: THE READER OF THE
WORDS OF A SENDING OF KIND K1, AS A DEFINITION, AND THE LAW's PREMISE ON IT, MET: the word at each
seat of the place, off the oracles' strings; behind the sending's piece it is read off the first
round's message alone. General in the place P, the radii, the base, the two rounds' data and the
block: so for the first segment's opening, the fifty later places and W's sending alike.

OBJECT. Sound.wordsOf (Johnson/Desc/Sound/MsgSig.lean) at the signature with one member
(shapeAt P j, rad j), at the seat that the place's own laying of trees gives message j behind nT
trees (layOf P, Johnson/Desc/K1/Law/BookAtRecord.lean); sendPiece
(Johnson/Desc/K1/Law/GoodSend3.lean).
USER. The letters fOf | fIn and the premise hf of send_goodIn, send_tied, block_tied and of the
binder hNew of k01_law: fOf := fOfAt G P rad base, fIn := fun _ m => fInAt ...
LETTERS. G (the description: it tells each tree's tenants), P, rad, nT | base, d₁, d₂, c, e, b.
Main names:
  seatOfMsg P nT j   the seat (tree, tenant) of the place's message j behind nT trees
  om_one             the signature's one member IS portOmZ cs s e, by rfl
  wordAtSeat         the word at that seat, off plain strings
  fOfAt              **J2a**: off the oracles' strings
  wordAtSeat_congr   it reads the columns of the seat's tree, and nothing else
  wordCols · fOfAt_cols · readsFirst_wordCols   as a reader of columns (ReadsFirst,
                     Johnson/Desc/K1/Law/GoodSendWords.lean)
  fInAt              the same off a first round's message
  hf_at · hf_exists  **J2b**: by words_first_two
THE PREMISE THAT STAYS. htree: every message of the place lies in a tree whose number, among the
place's, is below the number of trees of the first round's data d₁: a test on the plan.
IS IT EMPTY HERE? No: definitions, and equations at every y and τ. Where the description tells no
such tree, or a column has not its words, the word falls to 0, as Sound.wordsOf's does.
What is not claimed. That the word is near a code word. That d₁ is the place's round. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendWords
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.Port6
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece strsOf)

variable {Xi T Cl W : Type} {F : Frame}

section
variable (G : FileDescription Xi) (P : Par) (rad : ℕ → ℕ) (nT : ℕ)

/-- The seat (tree, tenant) of the place's message number j, behind nT trees. -/
def seatOfMsg (j : ℕ) : ℕ × ℕ := (nT + (layOf P).tree.getD j 0, (layOf P).part.getD j 0)

/-- The signature with one member: its member is the library's oracle message of that shape and
radius. -/
theorem om_one (cs : Codes) (s : OracleShape) (e : ℕ) :
    (Johnson.Pack.sigOf cs [(s, e)]).om ⟨0, Nat.zero_lt_succ 0⟩ = portOmZ cs s e := rfl

/-- The word at the place's seat j, off plain strings: the library's own word of the signature with
that one member. -/
def wordAtSeat (y : Strs) (j : Fin (shapesOf P).length) :
    (portOmZ P.codes (shapeAt P j) (rad j.val)).Str :=
  Sound.wordsOf G P.codes [(shapeAt P j, rad j.val)] (fun _ => seatOfMsg P nT j.val) y
    ⟨0, Nat.zero_lt_succ 0⟩

/-- **J2a: THE WORD AT THE PLACE's SEAT j OFF THE ORACLES' STRINGS.** -/
def fOfAt (y : F.E.Str) (j : Fin (shapesOf P).length) :
    (portOmZ P.codes (shapeAt P j) (rad j.val)).Str :=
  wordAtSeat G P rad nT (strsOf F y) j

/-- It reads the columns of the seat's tree, and nothing else. -/
theorem wordAtSeat_congr (y y' : Strs) (j : Fin (shapesOf P).length)
    (h : ∀ x, y.col (seatOfMsg P nT j.val).1 x = y'.col (seatOfMsg P nT j.val).1 x) :
    wordAtSeat G P rad nT y j = wordAtSeat G P rad nT y' j := by
  have e : wordOf G y (seatOfMsg P nT j.val).1 (seatOfMsg P nT j.val).2 =
      wordOf G y' (seatOfMsg P nT j.val).1 (seatOfMsg P nT j.val).2 := by
    funext x
    unfold wordOf
    rw [h x]
  unfold wordAtSeat Sound.wordsOf Sound.wordAt
  rw [e]

/-- The words of the place's seats, off a reader of columns that counts the trees from nT on. -/
def wordCols (c : ℕ → ℕ → List UInt64) (j : Fin (shapesOf P).length) :
    (portOmZ P.codes (shapeAt P j) (rad j.val)).Str :=
  wordAtSeat G P rad nT ⟨fun _ => none, fun t x => c (t - nT) x⟩ j

/-- fOfAt is that reader at the oracles' columns. -/
theorem fOfAt_cols (y : F.E.Str) :
    fOfAt G P rad nT y = wordCols G P rad nT fun t x => colsOf F y (nT + t) x := by
  funext j
  refine wordAtSeat_congr G P rad nT _ _ j fun x => ?_
  show Sound.colAt F y (nT + (layOf P).tree.getD j.val 0) x =
    colsOf F y (nT + (nT + (layOf P).tree.getD j.val 0 - nT)) x
  rw [Nat.add_sub_cancel_left]
  rfl

/-- It reads the first n trees alone, where the place's trees are fewer than n. -/
theorem readsFirst_wordCols (n : ℕ)
    (htree : ∀ j : Fin (shapesOf P).length, (layOf P).tree.getD j.val 0 < n) :
    ReadsFirst n (wordCols G P rad nT) := by
  intro c c' h
  funext j
  refine wordAtSeat_congr G P rad nT _ _ j fun x => ?_
  show c (nT + (layOf P).tree.getD j.val 0 - nT) x = c' (nT + (layOf P).tree.getD j.val 0 - nT) x
  rw [Nat.add_sub_cancel_left]
  exact h _ (htree j) x

end

/-- The words of the place's seats off the first round's message alone. -/
def fInAt (F : Frame) (G : FileDescription Xi) (P : Par) (rad : ℕ → ℕ) (base : ℕ) (d₁ : RDT)
    (m : (wT d₁).Msg) (j : Fin (shapesOf P).length) :
    (portOmZ P.codes (shapeAt P j) (rad j.val)).Str :=
  wordCols G P rad base
    (fun t x => if (posL F.all (base + t) x).isSome then firstCols d₁ m t x else []) j

/-- **J2b: hf**: behind the piece of a sending with the base base, the words at the place's seats
behind base trees are read off the first round's message alone. htree: the place's trees are among
the first round's. -/
theorem hf_at (G : FileDescription Xi) (P : Par) (rad : ℕ → ℕ) (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT)
    (c e : ℕ) (htree : ∀ j : Fin (shapesOf P).length, (layOf P).tree.getD j.val 0 < d₁.trees.length)
    (y : F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])) :
    fOfAt G P rad base ((sendPiece (W := W) (F := F) b base d₁ d₂ c e).ior.imp y τ) =
      fInAt F G P rad base d₁ τ.1 := by
  rw [fOfAt_cols]
  exact words_first_two (wordCols G P rad base) b base d₁ d₂ c e
    (readsFirst_wordCols G P rad base _ htree) y τ

/-- The same in the form of the top's binder. -/
theorem hf_exists (G : FileDescription Xi) (P : Par) (rad : ℕ → ℕ) (b : Block T Cl) (base : ℕ)
    (d₁ d₂ : RDT) (c e : ℕ)
    (htree : ∀ j : Fin (shapesOf P).length, (layOf P).tree.getD j.val 0 < d₁.trees.length) :
    ∃ fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str,
      ∀ y τ, fOfAt G P rad base ((sendPiece (W := W) (F := F) b base d₁ d₂ c e).ior.imp y τ) =
        fIn y τ.1 :=
  ⟨fun _ m => fInAt F G P rad base d₁ m, fun y τ => hf_at G P rad b base d₁ d₂ c e htree y τ⟩

end VerifiableInference.Desc.K1
