-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/K7Law.lean: ONE REAL KIND's LAW IN THE PLAIN FORM, STATED AND PROVED: K7, THE
NEXT TOKEN (Johnson/Desc/Kinds/ReplyKind.lean, ReplyBlock.lean): a worked example of what is owed
for a kind (Johnson/Desc/Plain/Leads.lean), at the kind's own text, at any place, any seat, any
stretch.

K7 only hears: it tests no equation of the model. So its law holds FOR CERTAIN (`Leads.of_sure`): it
costs nothing at any list of errors; and its relation Q says what the later blocks and the file's
last test lean on: nothing had been heard; what is laid into the one seat is a token of the
vocabulary; nothing else of the record is turned than what `setReply` turns.

  `piece_decides`: where a piece's reduction puts out b, its block's decision went on from the
    record in front to b's: general in the piece.
  `K7_law`: the law. `K7_heard`: with the seat's law "what is laid is read back": behind the block
    the seat holds that token.
THIS IS NO SOUNDNESS OF ANYTHING: that the token is the model's is the head's statement.
Imports Johnson/Desc/Sound/ExtHeardProofs.lean, and through it FoldHeardProofs.lean, for small laws
on the fold (`pieceOk`, `chainAtOk`, `foldConsOk`, `stepOk`).

-/
import Johnson.Desc.Plain.FoldChain
import Johnson.Desc.Sound.ExtHeardProofs
import Johnson.Desc.Kinds.ReplyBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds
open OnBytes (E)
open OnBytes.Desc.Reply (readReply isToken)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- Where a piece's reduction puts out b, its block's decision went on to b's record. -/
theorem piece_decides (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (hb : p.ior.red.out a τ = some b) :
    ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1 := by
  obtain ⟨s', k, hst, H'⟩ := foldConsOk (chainAtOk (pieceOk p a τ b hb))
  obtain ⟨gs, hd⟩ := stepOk hst
  have e : (s', _, _) = (b.1, ([] : List Fmt.RoundView), ([] : List OpenedColumn)) := Except.ok.inj H'
  have e₁ : s' = b.1 := congrArg Prod.fst e
  exact ⟨_, gs, by rw [← e₁]; exact hd⟩

/-- What K7's yes says of the record in front and the record behind. -/
def K7Says (V : ℕ) (L : Reply.Seat S) (a b : S × F.E.Str) : Prop :=
  L.reply a.1 = none ∧ ∃ h : E, isToken V h = true ∧ b.1 = L.setReply a.1 h

/-- **K7's law, in the plain form**: at any piece that holds the kind's block. -/
theorem K7_law (V link piece : ℕ) (L : Reply.Seat S) (p : Piece C F S Cl W)
    (hp : p.b = Reply.kind L link piece V) :
    p.ior.red.Leads (fun _ => True) (K7Says V L) p.err :=
  Reduction.Leads.of_sure _ fun a τ b _ hb => by
    obtain ⟨rs, gs, hd⟩ := piece_decides p a τ b hb
    rw [hp] at hd
    have hd' : Reply.decideE V L a.1 rs = .ok b.1 := hd
    unfold Reply.decideE at hd'
    split at hd'
    · rename_i r
      split at hd'
      · exact nomatch hd'
      · rename_i hn
        split at hd'
        · exact nomatch hd'
        · rename_i h _
          split at hd'
          · rename_i ht
            refine ⟨?_, h, ht, (Except.ok.inj hd').symm⟩
            cases hr : L.reply a.1 with
            | none => rfl
            | some x => rw [hr] at hn; exact absurd rfl hn
          · exact nomatch hd'
    · exact nomatch hd'

/-- With the seat's law: behind the block the seat holds a token. -/
theorem K7_heard (V : ℕ) (L : Reply.Seat S) (hL : ∀ s h, L.reply (L.setReply s h) = some h)
    (a b : S × F.E.Str) (h : K7Says V L a b) :
    ∃ t : E, L.reply b.1 = some t ∧ isToken V t = true := by
  obtain ⟨_, t, ht, e⟩ := h
  exact ⟨t, by rw [e, hL], ht⟩

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.K7_law
#print axioms VerifiableInference.Desc.Plain.K7_heard
