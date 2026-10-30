-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LettersAtList.lean: THE LIST "letters" (`OwesLetters`, LinkOwes.lean:
seven
debts on the link's law's two free letters) INSIDE THE FIELD A OF THE ONE LIST OF WHAT IS LEFT OF A
LINK's LAW (LinkList.lean), AT THAT LIST's OWN LETTERS: the table tabOf := the table's accessor at
the reader rdC 𝔇.cs 𝔇.arr 𝔇.ms at own := the plan's group of the segment; the context ctx := the
composed meaning's pins of the segment's three moments. A theorem: a call of
owesLetters_at (LettersWhole.lean), with two of its fourteen premises paid outright.

What is said. `letters_at_list`: **OwesLetters pb pq pe on0 (onK (k + 1)) (onK (k + 1 + 1)) tabOf
ctx**,
for every condition on0 in front that holds the table's own (h0: at the list: its first conjunct's
first). PAID INSIDE: "the meaning's pin is the library's own notion" (mgAll_pin: by definition) ·
"every seat of own is a tenant of one of the three moments" (own_group: outright).

PREMISES, each in the form in which the list or the law has it: pinB · pinQ (the list's fields) ·
**pinE: PinAsks OVER THE ONE EQUATION's PIECE: IT STANDS IN NO FIELD OF THE LIST: it was hidden in
A.letters.hce** · drawB · two (the list's share gives it) · hpb · hpq · hb₃ · hpe (what stands at
the
three numbers) · hs1 · h12 · hs2 (the law's conditions' debts).

Limits. BOOK-KEEPING: a call. pinB, pinQ, pinE, hs1, h12, hs2 are on states: SHOWN OF NO STATE HERE.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LettersWhole
import Johnson.Desc.First.Link.Law.PinAsksOf
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **THE SEVEN DEBTS ON THE LETTERS, AT THE LIST's LETTERS.** -/
theorem letters_at_list (L : Link S Claim) (p pw : Where) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (on0 : S × F.E.Str → Prop) (h0 : ∀ a, on0 a → onK k a)
    (pinB : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pb.base a.1 b.1)
    (pinQ : ∀ a τ b, onK (k + 1) a → pq.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pq.base a.1 b.1)
    (pinE : ∀ a τ b, onK (k + 1 + 1) a → pe.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pe.base a.1 b.1)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (two : TwoBlocks L p) (hpb : pb.b = below L.batchB) (hpq : pq.b = below L.behindB)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (hpe : pe.b = below b₃) (hs1 : ∀ b, onK (k + 1) b → (atS.get? b.1).isSome = true)
    (h12 : ∀ b τ c, onK (k + 1) b → pq.ior.red.out b τ = some c → onK (k + 1 + 1) c)
    (hs2 : ∀ c, onK (k + 1 + 1) c → (atS.get? c.1).isSome = true) :
    OwesLetters pb pq pe on0 (onK (k + 1)) (onK (k + 1 + 1))
      (fun a w => tabAt (𝔇.N.group m)
        (rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms w) a.1)
      (ctxPins 𝔇.N (mgAll 𝔇 Mg₀) z m) :=
  owesLetters_at 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.N (mgAll 𝔇 Mg₀) z m (𝔇.N.group m) L p pw b₃ pb pq pe
    on0 (onK (k + 1)) (onK (k + 1 + 1))
    { pin := mgAll_pin 𝔇 Mg₀
      own := own_group 𝔇.N m
      askB := fun a τ b ha => pinB a τ b (h0 a ha)
      askQ := pinQ
      askE := pinE
      hb₁ := drawB
      two := two
      hpb := hpb
      hpq := hpq
      hb₃ := hb₃
      hpe := hpe
      hs1 := hs1
      h12 := h12
      hs2 := hs2 }

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.letters_at_list
