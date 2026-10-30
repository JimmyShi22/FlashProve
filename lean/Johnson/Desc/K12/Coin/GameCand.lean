-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameCand.lean: **THE ONE ROW THAT IS OWED OF words_are_committed, AT A SEAT OF
THE PROXIMITY TEST, WITH THE GAME PAID.** One definition, statements and proofs: each is one call of
`cand_of_leads` (Game.lean).

Game.lean's `k12_testGivesCand` stands at the block's own record. The rule of composition's pieces
stand on a chain's state. Here the same at any piece that has GameSeat.lean's law (so at the
tiling's own piece: GameTile.lean).

  `SeatSeams`: the seams of letters at a seat, in one statement: where the door in gives a record at
    which the kind's own "one tuple for all rows" holds, there is one tuple of candidates in the
    row's letters of which the row's ins hold. No challenge, no count, no error stands in it.
  `k12_cand_seat`, `k12_cand_seatO`: the law at p, "the row's promises give `FirstOpens` |
    `FirstOpensOwn` behind the door in", "a yes hands on the promise behind", and `SeatSeams` give
    `TestGivesCand` (Johnson/Desc/Sound/WordsLaw.lean) at p, to the letter.
Limits: those of Game.lean and GameSeat.lean. NO SOUNDNESS IS CLAIMED. The three premises are paid
nowhere here.

-/
import Johnson.Desc.K12.Coin.GameSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open Johnson.Pack (sigOf)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {S Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The seams of letters at a seat.** -/
def SeatSeams (enter : S → Except String T12) (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (mine : List Mem) (on : S × F.E.Str → Prop)
    (ins outs : S × F.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      (∃ t, enter a.1 = .ok t ∧ QN π (NTuple F π no rad rd) (t, a.2)) →
      ∀ b w, outs b w →
        ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
          (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf F a.2) (c x)) ∧
            ∀ w', LaidBy cs arr mine c w w' → ins a w'

/-- **First arm.** -/
theorem k12_cand_seat (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F S Unit (Wit Cells Tok MsgT))
    (hg : p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no p.base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) p.err)
    (mine : List Mem) (on on' : S × F.E.Str → Prop)
    (ins outs : S × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1 = .ok t → FirstOpens π num no p.base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatSeams cs G arr smp enter F π no rad rd p.base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs :=
  cand_of_leads cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1 = .ok t ∧ QN π (NTuple F π no rad rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨t, _, h1, _, h3⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

/-- **Second arm.** -/
theorem k12_cand_seatO (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F S Unit (Wit Cells Tok MsgT))
    (hg : p.ior.red.Leads (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no p.base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) p.err)
    (mine : List Mem) (on on' : S × F.E.Str → Prop)
    (ins outs : S × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no p.base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatSeams cs G arr smp enter F π no rad rd p.base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs :=
  cand_of_leads cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1 = .ok t ∧ QN π (NTuple F π no rad rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨t, _, h1, _, h3⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_seat
#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_seatO
