-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyHeldWords.lean: TWO FORMS OF "THE PROVER's WORDS", TIED. The honest side's part of a sending
speaks of the words that it has laid (`held`, Johnson/Prover/Send/Core.lean). The law on the
batching in front of a proximity test is stated at any words, and one of its premises (`LaidOn`,
Johnson/Desc/Means/Bridge.lean) is paid at the words that a prover's plain rows make (`wordsAt`,
Johnson/Desc/K12/Honest/LaidState.lean). Statements and proofs, general in all letters.

What is shown.
  **`held_wordsAt`**: at a message of a sending that is a member of the group's layout: the two
    words are the same, at both tables and every index, if the statement has the message with its
    shape and the plain rows' member holds the part's rows.
  `held_older`: a newer sending leaves the words of an older message.
  **`laidOn_congr`**: `LaidOn` reads the words at the layout's members alone: it passes from words
    to all words that agree with them there. So `LaidOn` at `wordsAt` (`laidOn_state`) gives
    `LaidOn` at the words that the sendings' parts have laid, at which the rows' claims are shown
    (E2E/KeyEvalSays.lean): the joining call is typed nowhere. IT WANTS AGREEMENT AT ALL MEMBERS OF
    THE LAYOUT (a rider, a split's message among them), and it leads to the law that is stated at
    any words (`bat_claimTrue`, Johnson/Desc/K12/Honest/BatValues.lean), not to the one that is
    fixed at `wordsAt`.

Limits. That the plain rows' members hold the parts' rows is a premise: it says how the plain rows
are filled. Nothing on encoding randomness or on a fresh table. Nothing on any prover. Nothing on
hiding follows from this file.


-/
import Johnson.Desc.K12.Honest.LaidState
import Johnson.Prover.Send.Held

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt held held_new held_old clog_eq)
open ProofFile.Honest.K12 (PlainRows wordsAt)

/-- **Tables that hold words on the members' blocks hold all words that agree with these at the
layout's members.** -/
theorem laidOn_congr {K : Type} {S : Statement} {L : GroupLayout} {m m' : Words K} {T : Tables K}
    (h : LaidOn S L m T)
    (e : ∀ o i, L.find o = some i → ∀ part idx, m o part idx = m' o part idx) :
    LaidOn S L m' T :=
  ⟨fun o i first hf hk hm idx hi => (h.main_at o i first hf hk hm idx hi).trans (e o i hf _ _),
    fun o i first hf hm idx hi => (h.mask_at o i first hf hm idx hi).trans (e o i hf _ _),
    fun o i hf hk idx hi => (h.kept_at o i hf hk idx hi).trans (e o i hf _ _)⟩

/-- **At a message of a sending, the words that the sending's part has laid are the words that the
plain rows make**: message number k of the place P, which got the number first + k and is member
number j of the layout; the statement has it with its shape; the plain rows' member j holds the
part's rows. At both tables, at every index. -/
theorem held_wordsAt (S : Statement) (L : GroupLayout) (R : PlainRows) (w₀ : Words GE)
    (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (k j : ℕ) (hk : k < P.sent.size)
    (hf : L.find (first + k) = some j) {y : _} (hy : S.oracles[first + k]? = some y)
    (hs : y.shape = shapeAt P k)
    (hM : ∀ r e, R.M j r e = (V k).main ((shapeAt P k).mainDeg == 3) r e)
    (hZ : ∀ r e, R.Z j r e = (V k).mask r e) (part : Part) (idx : ℕ) :
    held w₀ first P V (first + k) part idx = wordsAt S L R (first + k) part idx := by
  rw [held_new w₀ first P V k hk part idx]
  unfold wordsAt realRows Statement.rowBits
  simp only [hf, hy, hs]
  cases part with
  | main =>
    show (if _ then _ else _) = _
    simp only [clog_eq, OracleShape.rows, hM]
  | mask =>
    show (if _ then _ else _) = _
    simp only [clog_eq, OracleShape.rows, hZ]

/-- The same at a message that an older sending has laid: the newer sending leaves it. -/
theorem held_older (w₀ : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (o : ℕ)
    (ho : o < first) (part : Part) (idx : ℕ) : held w₀ first P V o part idx = w₀ o part idx :=
  held_old w₀ first P V o part idx fun h => absurd h.1 (Nat.not_le.2 ho)

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.laidOn_congr
#print axioms AtPublicFiles.Key.held_wordsAt
#print axioms AtPublicFiles.Key.held_older
