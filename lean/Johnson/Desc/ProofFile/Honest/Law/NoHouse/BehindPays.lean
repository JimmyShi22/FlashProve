-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindPays.lean: TWO PREMISES OF `noHouse_behind_mg`
(Honest/Law/NoHouse/BehindMg.lean), PAID FROM THE LIBRARY's OWN. (1) hstate: what a yes of
`Link.runBehind` leaves: from the library's `LinkShare` (the runs' share of a link,
Johnson/Desc/First/Link/Law/RidesAtMg.lean): `Rb`; `rest9` alike; «the ledger is well laid» is kept.
(2) hafter: what the item totalB m says at the library's composed meaning (`mgAll_totalB`,
Johnson/Desc/Sound/MgAll.lean): the runs behind the batching return; behind them the one sum can be
taken and is 0: where the meaning's link of that number is this link (`after_at`), and its public
test rw rides past a yes.

WHAT THIS IS. Conditional lemmas on the library's definitions: calls. General in the link and in the
meaning's parameters. None of the library's goals.

  `behind_step`, `behind_state`, `behind_after`

Limits. `LinkShare` is shown here of no link: the ties of a link's entries to the known runs are
owed. hrw (the meaning's public test on the segment's rows rides past a yes of `runBehind`) is shown
of no parameters. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Fill
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.TieThreeFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place Strs Wit Link Claim)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.Sound (MgData mgAll MsgT CellsQ)
open VerifiableInference.Desc.LinkJoin (Rb rest9 ledgerOk LinkShare rest_blocks ledger_behind
  after_at)

/-- A yes of the runs behind the batching is a yes of the member's step. -/
theorem behind_step (Lk : Link S Claim) {s s' : S} (h : Lk.runBehind s = .ok s') (ft : Nat) :
    Lk.behindB.step ft s [] [] = .ok (s', 0) :=
  (step_noRound ft Lk.behindB rfl s s').2 h

/-- **hstate, from the runs' share.** -/
theorem behind_state (Lk : Link S Claim) (pp : Where) (hs : LinkShare Lk pp) (s s' : S)
    (h : Lk.runBehind s = .ok s') : Rb s s' ∧
      (∃ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) ∧
      (ledgerOk s = true → ledgerOk s' = true) := by
  have hst := behind_step Lk h 0
  exact ⟨(hs.two.2 _ _ _ _ _ _ hst).1,
    ⟨{ check := s.check }, {}, {}, (rest_blocks _ _ _ Lk pp hs.hb₁ hs.stand).2 _ _ _ _ _ _ hst⟩,
    ledger_behind Lk hs.sized _ _ _ _ _ _ hst⟩

variable {Xi' P Tok : Type} {rows cols nR : Nat} {X' : OnBytes.Model.Verify.Public}

/-- **hafter, at the library's composed meaning.** -/
theorem behind_after (𝔇 : MgData Xi' P Tok rows cols nR X')
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (m : Nat) (Lk : Link S Claim)
    (hlk : 𝔇.lk m = some Lk)
    (hrw : ∀ s s', Lk.runBehind s = .ok s' → 𝔇.rw m s = true → 𝔇.rw m s' = true)
    (a : P × S) (y : Strs) (v : Wit (CellsQ rows cols) Tok MsgT)
    (h : (mgAll 𝔇 Mg).totalB m a y v) : ∃ s', Lk.runBehind a.2 = .ok s' ∧
      VerifiableInference.Desc.K9.totalIn (𝔇.N.group m) s' = true ∧
      (mgAll 𝔇 Mg).total m (a.1, s') y v := by
  obtain ⟨⟨s', h1, h2, h3⟩, h4⟩ := h
  rw [after_at 𝔇 m Lk hlk] at h1
  exact ⟨s', h1, h2, h3, hrw a.2 s' h1 h4⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.behind_step
#print axioms ProofFile.Honest.FirstThread.behind_state
#print axioms ProofFile.Honest.FirstThread.behind_after
