-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillWords.lean: «words»: THE READER OF THE WORDS SENT, BEHIND A SENDING's PIECE, READS OF THE STRETCH's TRANSCRIPT THE FIRST ROUND's MESSAGE ALONE. The law of a sending (send_goodIn, Johnson/Desc/K1/Law/GoodSend3.lean) takes a reader fOf of the oracles behind the block
and asks (hf) that fOf (imp y τ) = fIn y τ.1; the structures Left10… (Johnson/Top/Fire/Code/) carry it as the field «words». Here fOf is the frame's own reading of an oracle message: symsW ∘ wordOf ∘ strsOf: the reader at which Johnson/RunOne/KeyFillSeed.lean's tieS_fam stands.
  colIn · colAt_behind_first    the column, behind a stretch, of a tree that the stretch's FIRST round sends is a function of that round's message alone: at every leaf; the oracles in front are not read
  wordIn · wordOf_behind_first  so is each tenant's word: as functions
  readerOf | readerIn · words_fam   so fOf := readerOf and fIn := readerIn meet the law's hf, to the letter, at sendPiece
  words_zero · readerOf_eq      at the stretch's first tree the premise is «0 < d₁.trees.length» · the reader is tieS_fam's, by rfl
THE ONE PREMISE, PUBLIC: each new message's tree is one of the trees that the first written round sends.
OBJECT: the rule's imp (stageIOR); colAt | strsOf (Johnson/Desc/Sound/MsgAt.lean) | wordOf (Johnson/Desc/Msg.lean); sendPiece · USER: imported by Johnson/Top/Fire/Code/Row10Seven.lean, Johnson/Top/Fire/Code/Rows2Send.lean (meant: Left10…'s fOf | fIn | words) · LETTERS: all of the sending's.
NOT SAID: that a real row's data meet the premise · the ties at the call (codes · shape · radius · seat). Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeed
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Sound (Frame colAt strsOf behind sLeft_at sCol_eq stg)
open VerifiableInference.Desc.K1 (sendPiece)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Flat OnBytes.Slice

/-- The column of the round's tree n at the leaf x, in the round's message; nothing where the frame gives (b + n, x) no position. -/
def colIn (F : Frame) (b : ℕ) (d : RDT) (m : (wT d).Msg) (n x : ℕ) : List UInt64 :=
  match posL F.all (b + n) x with
  | none => []
  | some _ => ((posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)).getD []

/-- **Behind a stretch, the column of a tree that its first round sends is a function of that round's message alone.** -/
theorem colAt_behind_first (F : Frame) (b : ℕ) (d : RDT) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT (Run.ckP .two) (d :: ds))) (n x : ℕ) (hn : n < d.trees.length) :
    colAt F (behind (Run.ckP .two) F b (d :: ds) y τ) (b + n) x = colIn F b d τ.1 n x := by
  unfold colAt colIn
  cases hp : posL F.all (b + n) x with
  | none => rfl
  | some p =>
    show sLeft (Run.ckP .two) (stg F b (d :: ds)) y τ p = _
    rw [sLeft_at (Run.ckP .two) F (d :: ds) b y τ (b + n) x p hp, sCol_eq, if_neg (by omega), Nat.add_sub_cancel_left, colAtST_cons, if_pos hn]

/-- A tenant's word, in the round's message. -/
def wordIn {XI : Type} (G : FileDescription XI) (F : Frame) (b : ℕ) (d : RDT) (m : (wT d).Msg) (n t : ℕ) : ℕ → Option Sym :=
  fun x => (G.oracleAt (b + n)).bind fun o => o.cut t (colIn F b d m n x)

theorem wordOf_behind_first {XI : Type} (G : FileDescription XI) (F : Frame) (b : ℕ) (d : RDT) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT (Run.ckP .two) (d :: ds))) (n t : ℕ)
    (hn : n < d.trees.length) : wordOf G (strsOf F (behind (Run.ckP .two) F b (d :: ds) y τ)) (b + n) t = wordIn G F b d τ.1 n t := by
  funext x
  show ((G.oracleAt (b + n)).bind fun o => o.cut t (colAt F (behind (Run.ckP .two) F b (d :: ds) y τ) (b + n) x)) = _
  rw [colAt_behind_first F b d ds y τ n x hn]
  rfl

section
variable {XI K : Type} (G : FileDescription XI) (F : Frame) (cs' : OnBytes.Codes) (sh : K → OnBytes.OracleShape) (rad : K → ℕ) (b : ℕ) (n t : K → ℕ)

/-- **The frame's own reading of the oracle messages.** -/
def readerOf (y : F.E.Str) (k : K) : (portOmZ cs' (sh k) (rad k)).Str := symsW cs' (sh k) (rad k) (wordOf G (strsOf F y) (b + n k) (t k))

/-- The same, off the first round's message. -/
def readerIn (d : RDT) (_ : F.E.Str) (m : (wT d).Msg) (k : K) : (portOmZ cs' (sh k) (rad k)).Str := symsW cs' (sh k) (rad k) (wordIn G F b d m (n k) (t k))

/-- **«words»**: to the letter the premise hf of send_goodIn. -/
theorem words_fam {T Cl W : Type} (blk : Block T Cl) (d₁ d₂ : RDT) (c e : ℕ) (hn : ∀ k, n k < d₁.trees.length) :
    ∀ y τ, readerOf G F cs' sh rad b n t ((sendPiece (W := W) (F := F) blk b d₁ d₂ c e).ior.imp y τ) = readerIn G F cs' sh rad b n t d₁ y τ.1 := by
  intro y τ
  funext k
  show symsW cs' (sh k) (rad k) (wordOf G (strsOf F (behind (Run.ckP .two) F b [d₁, d₂] y τ)) (b + n k) (t k)) = _
  rw [wordOf_behind_first G F b d₁ [d₂] y τ (n k) (t k) (hn k)]
  rfl

/-- The same where every new message sits in the stretch's first tree (rows 1.0 | 1.1): THE PREMISE IS «the first written round sends a tree». -/
theorem words_zero {T Cl W : Type} (blk : Block T Cl) (d₁ d₂ : RDT) (c e : ℕ) (h0 : 0 < d₁.trees.length) :
    ∀ y τ, readerOf G F cs' sh rad b (fun _ => 0) t ((sendPiece (W := W) (F := F) blk b d₁ d₂ c e).ior.imp y τ) = readerIn G F cs' sh rad b (fun _ => 0) t d₁ y τ.1 :=
  words_fam G F cs' sh rad b (fun _ => 0) t blk d₁ d₂ c e fun _ => h0

/-- The reader is the one at which KeyFillSeed.lean's tieS_fam stands: by rfl. -/
theorem readerOf_eq (y : F.E.Str) (k : K) : readerOf G F cs' sh rad b n t y k = symsW cs' (sh k) (rad k) (wordOf G (strsOf F y) (b + n k) (t k)) := rfl

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.colAt_behind_first
#print axioms Johnson.RunOne.KeyRows23.wordOf_behind_first
#print axioms Johnson.RunOne.KeyRows23.words_fam
#print axioms Johnson.RunOne.KeyRows23.words_zero
#print axioms Johnson.RunOne.KeyRows23.readerOf_eq
