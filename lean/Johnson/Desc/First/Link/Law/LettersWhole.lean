-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LettersWhole.lean: ALL SEVEN DEBTS ON THE LINK LAW's FREE LETTERS
(`OwesLetters`, LinkOwes.lean: hpin; hcb, hcq, hce; htabb, htabq, htab) IN ONE THEOREM, AT A CHOICE
OF THE TWO LETTERS: the table tabOf a w := the table's accessor at the reader `rdC` (ClampPin.lean:
the member's typed message, read back as a table); the context ctx := the table's own pins of the
segment's three moments (`ctxPins`, PinsBack.lean). A theorem: the assembly of ClampPin.lean,
PinsBack.lean and LettersAt.lean.

What is said.
  `LettersAsk`: what the seven take, in one structure: the meaning's pin is the library's own
    notion; every seat of own is a tenant of one of the three moments; `PinAsks` over each of the
    three pieces; the runs' share (`LinkShare`); the three pieces hold the link's three
    sub-protocols; the law's own hs1, h12, hs2. `owesLetters_at`: **`OwesLetters pb pq pe on0 on1
    on2 (fun a w => tabAt own (rdC cs arr ms w) a.1) (ctxPins Nm Mg z m)`.**

Limits. `LettersAsk` is a list of premises: `PinAsks` (a test on the plan's numbers; the OOD
samples' reader answers alike at the two states) and «every seat of own is a tenant» are paid by
nobody here; `LinkShare` under the runs' ties; hs1, h12, hs2 are the law's other debts. The
conditions on0, on1, on2 are free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ClampPin
import Johnson.Desc.First.Link.Law.LettersAt
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.LinkOwes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Meaning Numbers)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)

variable {F : Frame} {P Cells Tok Xi : Type}

/-- **What the seven take.** -/
structure LettersAsk (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (z : P) (m : ℕ)
    (own : List (ℕ × ℕ)) (L : Link S Claim) (pp pw : Where) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit Cells Tok MsgT))
    (on0 on1 on2 : S × F.E.Str → Prop) : Prop where
  pin : Mg.pin = pinJT cs G arr smp ms
  own : ∀ x ∈ own, ∃ t < 3, x ∈ Nm.sent m t
  askB : ∀ a τ b, on0 a → pb.ior.red.out a τ = some b → PinAsks cs smp Nm z m pb.base a.1 b.1
  askQ : ∀ a τ b, on1 a → pq.ior.red.out a τ = some b → PinAsks cs smp Nm z m pq.base a.1 b.1
  askE : ∀ a τ b, on2 a → pe.ior.red.out a τ = some b → PinAsks cs smp Nm z m pe.base a.1 b.1
  hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB
  two : TwoBlocks L pp
  hpb : pb.b = below L.batchB
  hpq : pq.b = below L.behindB
  hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x
  hpe : pe.b = below b₃
  hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true
  h12 : ∀ b τ c, on1 b → pq.ior.red.out b τ = some c → on2 c
  hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true

/-- **ALL SEVEN DEBTS ON THE LETTERS.** -/
theorem owesLetters_at (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (z : P) (m : ℕ)
    (own : List (ℕ × ℕ)) (L : Link S Claim) (pp pw : Where) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit Cells Tok MsgT))
    (on0 on1 on2 : S × F.E.Str → Prop)
    (A : LettersAsk cs G arr smp ms Nm Mg z m own L pp pw b₃ pb pq pe on0 on1 on2) :
    OwesLetters pb pq pe on0 on1 on2 (fun a w => tabAt own (rdC cs arr ms w) a.1)
      (ctxPins Nm Mg z m) where
  hpin a w w' _ h h' := hpin_at cs arr ms G smp Nm Mg A.pin z m own A.own a w w' h h'
  hcb := hc_at cs G arr smp ms Nm Mg A.pin z m pb on0 A.askB
  hcq := hc_at cs G arr smp ms Nm Mg A.pin z m pq on1 A.askQ
  hce := hc_at cs G arr smp ms Nm Mg A.pin z m pe on2 A.askE
  htabb a τ b' w _ hout := htabb_at own (rdC cs arr ms) L pp A.hb₁ A.two pb A.hpb a τ b' w hout
  htabq := htabq_at own (rdC cs arr ms) L pp A.two pq A.hpq on1 on2 A.hs1 A.h12 A.hs2
  htab a τ b' w _ hout := htab_at own (rdC cs arr ms) pw b₃ A.hb₃ pe A.hpe a τ b' w hout

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.owesLetters_at
