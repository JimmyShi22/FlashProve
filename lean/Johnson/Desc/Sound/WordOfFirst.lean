-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/WordOfFirst.lean: BEHIND A STRETCH OF WRITTEN ROUNDS THE WORD OF A MEMBER WHOSE
TREE THE FIRST ROUND SENDS HANGS ON THE STRINGS IN FRONT AND ON THE FIRST ROUND's MESSAGE ALONE. The
law of a sending (K1's send_gives_smpAt, Johnson/Desc/K1/Law/GoodSendForms.lean; hf) and the seam
from it to "no collision at the new members" (sendGivesSmp_of_send, SendSeam.lean; its premise
"word") ask a reading fIn of (the strings in front, the first round's message) that gives the
members' words behind the block. HERE THAT READING IS A TERM AND THE EQUATION IS PROVED.

  col_first       a column of a tree that the stretch's first round sends is the same behind two
                  transcripts with one first message.
  wordsOf_first     so is the word of a member that sits in such a tree.
  fInOf           **the reading**: the word behind any transcript with that first message.
  word_paid       **the equation**, at a sending's piece, in the seam's own form.
WHAT STAYS. hseat: each member's tree is base + n with n below the number of the first written
round's trees: the plan's and the tiling's (SentBy says "one that the stretch sends"; here: the
FIRST round).
What is not claimed. Nothing on what the word is. Nothing on soundness.

-/
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open Iop Run
open VerifiableInference.Desc.K1 (sendPiece)

/-- A column of a tree that the stretch's first round sends. -/
theorem col_first (C : CK) (F : Frame) (b : ℕ) (d : RDT) (ds : List RDT) (y : F.E.Str)
    (τ τ' : Iop.Tr (uLT C (d :: ds))) (h : τ.1 = τ'.1) (n : ℕ) (hn : n < d.trees.length) (x : ℕ) :
    colAt F (behind C F b (d :: ds) y τ) (b + n) x =
      colAt F (behind C F b (d :: ds) y τ') (b + n) x := by
  unfold colAt
  cases hp : posL F.all (b + n) x with
  | none => rfl
  | some p =>
    show sLeft C (stg F b (d :: ds)) y τ p = sLeft C (stg F b (d :: ds)) y τ' p
    rw [sLeft_at C F (d :: ds) b y τ (b + n) x p hp, sLeft_at C F (d :: ds) b y τ' (b + n) x p hp,
      sCol_eq, sCol_eq, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left, colAtST_cons,
      colAtST_cons, if_pos hn, if_pos hn, h]

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)

/-- The word of a member that sits in such a tree. -/
theorem wordsOf_first (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (C : CK)
    (F : Frame) (b : ℕ) (d : RDT) (ds : List RDT) (y : F.E.Str) (τ τ' : Iop.Tr (uLT C (d :: ds)))
    (h : τ.1 = τ'.1) (i : Fin l.length) (n : ℕ) (hj : (seat i).1 = b + n)
    (hn : n < d.trees.length) :
    wordsOf G cs l seat (strsOf F (behind C F b (d :: ds) y τ)) i =
      wordsOf G cs l seat (strsOf F (behind C F b (d :: ds) y τ')) i :=
  wordsOf_col G cs l seat _ _ i fun x => by
    rw [hj]
    exact col_first C F b d ds y τ τ' h n hn x

variable {T Cl W : Type} {Fr : Frame}

open Classical in
/-- **The reading**: the word of the member x behind any transcript with the first message μ (where
there is none: the word in front). -/
def fInOf (x : Mem) (base : ℕ) (d₁ d₂ : RDT) (y : Fr.E.Str) (μ : (wT d₁).Msg) :
    ((sigOf cs x.1.l).om x.2).Str :=
  if h : ∃ τ : Iop.Tr (uLT (ckP .two) [d₁, d₂]), τ.1 = μ then
    wordsOf G cs x.1.l x.1.seat (strsOf Fr (behind (ckP .two) Fr base [d₁, d₂] y h.choose)) x.2
  else wordsOf G cs x.1.l x.1.seat (strsOf Fr y) x.2

/-- **The equation**, at a sending's piece: the members' words behind the block hang on the strings
in front and the first round's message alone. -/
theorem word_paid (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT) (c e : ℕ) (x : Mem) (n : ℕ)
    (hj : (x.1.seat x.2).1 = base + n) (hn : n < d₁.trees.length) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) [d₁, d₂])) :
    wordsOf G cs x.1.l x.1.seat
        (strsOf Fr ((sendPiece (W := W) (F := Fr) b base d₁ d₂ c e).ior.imp y τ)) x.2 =
      fInOf G cs x base d₁ d₂ y τ.1 := by
  have hex : ∃ τ' : Iop.Tr (uLT (ckP .two) [d₁, d₂]), τ'.1 = τ.1 := ⟨τ, rfl⟩
  unfold fInOf
  rw [dif_pos hex]
  exact wordsOf_first G cs x.1.l x.1.seat (ckP .two) Fr base d₁ [d₂] y τ hex.choose
    hex.choose_spec.symm x.2 n hj hn

end VerifiableInference.Desc.Sound
