-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRunsSendingPlays.lean: a sending (the kind K1) whose half is the bare `K1.proverSideOfSending J`, as
`keyProver` lays it, PLAYS in the frame's sense `PlaysOn` (Honest/Law/ThreadC.lean), at every state,
all coins and all tables at hand, under one public test (`sendFits`). General in the chain, the book
and the two relations A, B. It is the twin of Honest/K1/Plays.lean, which has the same at the lifted
half `placeHalf`.

  `sentRounds`        THE TERM: the sending's two rounds as played: a second text of `sendPart`'s two
                      messages, at `sendPart`'s own arguments
  `sendHalf_silent`   no stop of the row ever stops
  `played_sendHalf`   the tie: `playedRow` returns the term and `fitsRow` says yes
  `state_sendHalf`    the prover's state behind the row: it has heard the two challenges, no more
  `sentRounds_tables`, `sentRounds_fit`   the trees sent are those that the block declares: as many,
                      all at hand, each of the declared width (`TablesFit`, Honest/Law/RunsC.lean)
  `sending_plays`     **`play` returns the term at the block**, wherever `chainSteps` has returned there, at
                      every stand; the stand behind it is written out
  `SendingEnd`        what holds behind the block, written out: the premise that a caller's B must follow
                      from
  `sending_playsOn`   **`PlaysOn` at the block**, from A to B, for every A and B such that B follows
                      from A and `SendingEnd`

Limits. "It plays" is the frame's name for a premise's form: play returns, every message has the
declared shape, and the columns are laid (none: K1's rounds read nothing). IT IS NO COMPLETENESS: it
does not say that the verifier's step accepts. That `sendFits` holds at a job, that a block has K1's
shape and that the book lends are premises here. On hiding nothing is said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Plays
import Johnson.Desc.ProofFile.Honest.Law.RunsFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt col answers)
open ProofFile.Honest.Small (playedRow fitsRow stateRow playsOn_of play_row_whole)
open ProofFile.Honest.SumLaw (playedFrom fitsFrom stateFrom aloneFrom)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **THE TERM: the sending's two rounds as played**, at the bare half. c: the part's own coins. Its
first record holds the tables whole: what is SENT as an oracle, not what a verifier is shown. The 0
beneath the held words is `sendPart`'s own text: a constant, no coin. -/
def sentRounds (name : String) (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (t : State W X)
    (seen : Seen) (d₀ d₁ : Fmt.Drawn) : List Played :=
  [⟨name, J.P.place, 0, true, [], (treeTables J.P (J.rows c seen t 0)).map some, d₀⟩,
   ⟨name, J.P.place, 0, true,
      ((answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
            (J.rows c (seen.plus [⟨[], d₀⟩]) (t.hears d₀) 1))
          (seedsAt J.P [d₀])).map fun a => Said.got (.answer (toE a))), [], d₁⟩]

/-- No stop of the row ever stops. -/
theorem sendHalf_silent (J : SendJob W X) (v : Option V) (loc ds : List Fmt.Drawn) :
    rowStopAt v (proverSideOfSending (V := V) J).parts loc ds = none := by
  cases v <;> simp [proverSideOfSending, rowStopAt, Part.stopAt, sendPart]

/-- The last challenge heard. -/
theorem lately_heard (t : State W X) (d : Fmt.Drawn) : (t.hears d).lately 1 = [d] := by
  show (t.heard ++ [d]).drop ((t.heard ++ [d]).length - 1) = [d]
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]

/-- **THE TIE**: under the public test, at challenges that K1's rounds can draw, the frame's terms
for a row return the term, and every message fits its round: at each value of the coins, every state
and whatever was seen. -/
theorem played_sendHalf (name : String) (J : SendJob W X) (hf : sendFits J.P J.ride = true)
    (c : RowCoins (proverSideOfSending (V := V) J).parts) (t : State W X) (seen : Seen) (d₀ d₁ : Fmt.Drawn)
    (hd : drawsFit (K1.rounds J.P) [d₀, d₁] = true) :
    playedRow name J.P.place (proverSideOfSending (V := V) J).parts 0 c t seen [d₀, d₁] =
        some (sentRounds name J c.1.1 t seen d₀ d₁) ∧
      fitsRow (proverSideOfSending (V := V) J).parts ((K1.rounds J.P).zip (K1.oracles J.P)) c t seen
        [d₀, d₁] = true := by
  have hs : seedsFit J.P [d₀] = true := by
    obtain ⟨a, b, e, h⟩ := k1_draws_two J.P _ hd
    cases e
    exact h
  have hl := lately_heard t d₀
  have f1 := k1_first_fits J.P (J.rows c.1.1 seen t 0)
  have f2 := k1_second_fits J.P _ (Johnson.Prover.Send.length_answers J.P (stAt J.P J.first) J.first
    (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
      (J.rows c.1.1 (seen.plus [⟨[], d₀⟩]) (t.hears d₀) 1)) (seedsAt J.P [d₀]))
  have he : (⟨(t.hears d₀).input, (t.hears d₀).heard, (t.hears d₀).own⟩ : State W X) =
      t.hears d₀ := rfl
  constructor
  · simp [proverSideOfSending, playedRow, playedFrom, sendPart, sentRounds, hf, he, hl, hs]
  · simp [proverSideOfSending, fitsRow, fitsFrom, sendPart, hf, he, hl, hs, K1.rounds, K1.oracles]
    exact ⟨f1, f2⟩

/-- The prover's state behind the row: it has heard the two challenges; input and own as before. -/
theorem state_sendHalf (J : SendJob W X) (t : State W X) (d₀ d₁ : Fmt.Drawn) :
    stateRow (proverSideOfSending (V := V) J).parts t [d₀, d₁] = ⟨t.input, t.heard ++ [d₀, d₁], t.own⟩ := by
  simp [proverSideOfSending, stateRow, stateFrom, sendPart, State.hears]

/-- The tables of the two rounds: the first round's, each under the sending's place. -/
theorem sentRounds_tables (name : String) (J : SendJob W X) (c : Cs (dueR J.P J.ride))
    (t : State W X) (seen : Seen) (d₀ d₁ : Fmt.Drawn) :
    tablesOf (sentRounds name J c t seen d₀ d₁) =
      (treeTables J.P (J.rows c seen t 0)).map fun T => some (J.P.place, T) := by
  simp [tablesOf, sentRounds, Function.comp_def]

/-- **The trees sent are those that the block declares**: as many, all at hand, each of the declared
width. No hypothesis. -/
theorem sentRounds_fit (name : String) (J : SendJob W X) (c : Cs (dueR J.P J.ride))
    (t : State W X) (seen : Seen) (d₀ d₁ : Fmt.Drawn) :
    TablesFit (K1.oracles J.P).flatten (sentRounds name J c t seen d₀ d₁) := by
  have ho : (K1.oracles J.P).flatten = (K1.oracles J.P).headD [] := by
    simp [K1.oracles]
  have e := treeTables_oracles J.P (J.rows c seen t 0)
  rw [ho]
  refine ⟨?_, fun n o hn => ?_⟩
  · rw [sentRounds_tables, List.length_map]
    simpa using congrArg List.length e
  · have e2 := congrArg (·[n]?) e
    simp only [List.getElem?_map, hn, Option.map_some] at e2
    cases hT : (treeTables J.P (J.rows c seen t 0))[n]? with
    | none =>
      rw [hT] at e2
      cases e2
    | some T =>
      rw [hT] at e2
      have e3 : (T.logLength, T.words) = (o.logLength, o.words) := Option.some.inj e2
      exact ⟨(J.P.place, T), by rw [sentRounds_tables, List.getElem?_map, hT]; rfl,
        (Prod.mk.inj e3).2⟩

/-- **A sending's block is played**: wherever `chainSteps` has returned at the block (the book has
lent), at challenges that its rounds can draw: `play` returns the term, at the coins that the book
lends, and the stand behind it is written out. At every stand m: nothing is asked of it, and no
silence of a stop. -/
theorem sending_plays {hs : List (Placed V W X)} {b : Block S Cl} (J : SendJob W X)
    (hsh : b.place = J.P.place ∧ b.rounds = K1.rounds J.P ∧ b.oracles = K1.oracles J.P)
    (hh : (hs.find? fun g => g.place == b.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {l : List (Step W X)}
    (hl : chainSteps Bk rows look v [b] hs = .ok l) (m : Mid W X) (ds : List Fmt.Drawn)
    (hd : drawsFit b.rounds ds = true) :
    ∃ (c : RowCoins (proverSideOfSending (V := V) J).parts) (d₀ d₁ : Fmt.Drawn), ds = [d₀, d₁] ∧
      lendRow Bk rows look b.place (proverSideOfSending (V := V) J).parts 0 = .ok c ∧
      play l ds [] m = .ok (sentRounds b.name J c.1.1 m.st m.shown d₀ d₁,
        ⟨⟨m.st.input, m.st.heard ++ [d₀, d₁], m.st.own⟩, m.loc ++ [d₀, d₁],
          m.seen ++ roundsOf (sentRounds b.name J c.1.1 m.st m.shown d₀ d₁), m.opened⟩) := by
  obtain ⟨hp, hr, ho⟩ := hsh
  obtain ⟨c, hc, rfl⟩ := steps_one_half hh hl
  rw [hr] at hd
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd
  obtain ⟨h1, h2⟩ := played_sendHalf (V := V) b.name J hf c m.st m.shown d₀ d₁ hd
  refine ⟨c, d₀, d₁, rfl, hc, ?_⟩
  have e := play_row_whole b.name J.P.place v (proverSideOfSending (V := V) J).parts 0
    ((K1.rounds J.P).zip (K1.oracles J.P)) c [d₀, d₁] [] m _ (sendHalf_silent J _ _ _) h2 h1
  rw [state_sendHalf] at e
  unfold Placed.steps
  rw [hp, hr, ho]
  exact e

/-- **What holds behind a sending's block**, at the stand m and the tables E in front of it: the stand
m' behind it and the tables E' behind it, written out. l: the two rounds as played. The prover's
input and own state are as before; it has heard the block's two challenges and no more; the stops'
list and the rounds seen have grown by the block's own; no column was read; the tables at hand are
those in front with the block's declared trees behind them. -/
structure SendingEnd (b : Block S Cl) (m m' : Mid W X) (E E' : Env) (ds : List Fmt.Drawn)
    (l : List Played) : Prop where
  input : m'.st.input = m.st.input
  own : m'.st.own = m.st.own
  heard : m'.st.heard = m.st.heard ++ ds
  loc : m'.loc = m.loc ++ ds
  seen : m'.seen = m.seen ++ roundsOf l
  opened : m'.opened = m.opened
  tables : E' = E.add l
  fit : TablesFit b.oracles.flatten l
  two : ds.length = 2 ∧ l.length = 2

/-- **`PlaysOn` at a sending's block**: at a block of K1's shape at the job's numbers, where the first
half found at its place is the job's bare half and the job fits its place: from every A to every B
that follows from A and `SendingEnd` where the block's own step returns. Nothing of A is used for the
play or the columns. -/
theorem sending_playsOn {φ : Face V W Pb} {chain ft : Nat} {hs : List (Placed V W X)}
    {b : Block S Cl} (J : SendJob W X)
    (hsh : b.place = J.P.place ∧ b.rounds = K1.rounds J.P ∧ b.oracles = K1.oracles J.P)
    (hh : (hs.find? fun g => g.place == b.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true) {A B : Coins Bk → S → Mid W X → Env → Prop}
    (H : ∀ k s m E ds l m' s' n, A k s m E → drawsFit b.rounds ds = true →
      SendingEnd b m m' E (E.add l) ds l → b.step ft s (roundsOf l) [] = .ok (s', n) →
      B k s' m' (E.add l)) :
    PlaysOn φ Bk chain ft hs b A B := by
  obtain ⟨hp, hr, ho⟩ := hsh
  refine playsOn_of hh fun k s m E ds c hA hd _ _ _ _ _ => ?_
  have hd' := hd
  rw [hr] at hd'
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd'
  obtain ⟨h1, h2⟩ := played_sendHalf (V := V) b.name J hf c m.st m.shown d₀ d₁ hd'
  refine ⟨sentRounds b.name J c.1.1 m.st m.shown d₀ d₁, [], ?_, ?_, ?_, fun s' n hs' => ?_⟩
  · rw [hp]
    exact h1
  · rw [hr, ho]
    exact h2
  · rw [hr]
    exact k1_cols_return _ _ _ _ _ _
  · rw [took_nil]
    refine H k s m E _ _ _ s' n hA hd ?_ hs'
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    · show (stateRow (proverSideOfSending (V := V) J).parts m.st [d₀, d₁]).input = _
      rw [state_sendHalf]
    · show (stateRow (proverSideOfSending (V := V) J).parts m.st [d₀, d₁]).own = _
      rw [state_sendHalf]
    · show (stateRow (proverSideOfSending (V := V) J).parts m.st [d₀, d₁]).heard = _
      rw [state_sendHalf]
    · rw [ho]
      exact sentRounds_fit _ _ _ _ _ _ _

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.sentRounds
#print axioms ProofFile.Honest.K1.sendHalf_silent
#print axioms ProofFile.Honest.K1.lately_heard
#print axioms ProofFile.Honest.K1.played_sendHalf
#print axioms ProofFile.Honest.K1.state_sendHalf
#print axioms ProofFile.Honest.K1.sentRounds_tables
#print axioms ProofFile.Honest.K1.sentRounds_fit
#print axioms ProofFile.Honest.K1.sending_plays
#print axioms ProofFile.Honest.K1.SendingEnd
#print axioms ProofFile.Honest.K1.sending_playsOn
