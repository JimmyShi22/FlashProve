-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlayPart.lean: from a part that is played alone to the frame's
own player, for every part. Definitions, and theorems on the frame's functions (`Part.steps`,
`rowSteps`, `play`, Honest/Frame.lean) and on `alone` (Honest/SumLaw/Terms.lean). No sub-protocol is
named here.

Terms. Honest/K3/GLOSSARY.md ("frame", "part, stretch", "play", "row").

What is shown.
  `endFrom`, `endRow`: the state behind a part's moves, and behind a row's.
  `stepsFrom`: the text of `Part.steps` from a round's number on.
  `stop_none`: a step whose two stops never stop does not stop.
  `aloneFrom_length`: where the moves answer there are as many challenges as moves, and as many
    rounds.
  `play_stepsFrom`, `play_part`: of a part that never stops and whose messages have the stated
    shape: where it answers alone, `play` on its steps goes through and yields the same rounds.
    Behind it: the state as the moves leave it, the challenges laid behind those that stops may
    read, the rounds laid behind those shown, the columns opened as they stood in front.
  `aloneRow`, `RowFits`, `NoStops`: a row's parts played alone one behind the other; every message
    of the row has the stated shape; no part of the row ever stops.
  `play_row`: the same for a row, by `play_append` (Honest/Law/Play.lean).
  `played_row`: what every round bears that was played on a row's steps, where no round states an
    oracle message: the row's place; that a half made it; no table (by `play_yields`, Play.lean).
Helpers: `stepsFrom_mem`, `rowSteps_mem`, `yields_mem`.
Two texts. Honest/SumLaw/Plays.lean (this file does not import it) has
`endFrom`'s text as `stateFrom` and `stop_none`'s statement and proof under the same name, and, by
its head, treats the same matter under like names (`stepsFrom`, `play_stepsFrom`, `play_steps`). The
tie for the first: `endFrom_eq_stateFrom` (Honest/K3/Law/Keep/Bridge.lean); no lemma of this file
ties the two.

Hypotheses that remain.
  `hb`, `hh`: the two stops never stop (of a step, of the moves' part, of the part).
  `hl`, `hf`, `h`: (in `play_part`) as many declared rounds as moves; every message has the stated
    shape, at every state and at all that was shown (every term of the frame's `Seen`); the part
    answers alone.
  `h`, `hos`: (in `played_row`) `play` on the row's steps returns; no round states an oracle
    message.
  In `play_row`, without a name, in front of arrows: `NoStops`, `RowFits`, and the row answers
    alone.
  Without a name besides: the two of `play_stepsFrom` (every message has the stated shape; the moves
    answer alone), the one of `aloneFrom_length` (the moves answer), and the memberships of the
    three helpers.

Imported. Honest/Frame.lean, Honest/Law/Play.lean and Honest/SumLaw/Terms.lean.

Users. This file is imported by Honest/K3/Law/SumFits.lean.

Limits. The hypothesis on shapes (`hf`, `RowFits`) is asked at every state and at all that was
shown, not along the run alone: at every list of rounds and at every value of the columns opened.
Nothing is said of a part that stops, of tables' columns, or of what the rounds are worth.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Play
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Oracle Place)
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V W X C : Type}

/-- The state behind moves, each with its challenge. -/
def endFrom : List (Move C W X) → State W X → List Fmt.Drawn → State W X
  | mv :: mvs, t, d :: ds => endFrom mvs { t.hears d with own := mv.hand (t.hears d) } ds
  | _, t, _ => t

/-- The text of `Part.steps`, from the round number k on. l: the rounds, each with its move. n: the
part's number of moves. -/
def stepsFrom (name : String) (a : Addr) (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (n : Nat) (c : C) (l : List ((Fmt.DeclaredRound × List Oracle) × Move C W X)) (k : Nat) :
    List (Step W X) :=
  (l.zipIdx k).map fun r =>
    ⟨name, a, r.1.1.1, r.1.1.2, bad, hid, r.2, r.2 + 1 == n,
      some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩

theorem stop_none (s : Step W X) (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    (l : List Fmt.Drawn) (n : Nat) : s.stop l n = none := by
  unfold Step.stop
  simp only [hb, hh]

theorem aloneFrom_length (c : C) : ∀ (ms : List (Move C W X)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (x : List Fmt.RoundView), aloneFrom c ms t seen ds = some x →
    ds.length = ms.length ∧ x.length = ms.length
  | [], _, _, [], x, h => by
    simp only [aloneFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | [], _, _, _ :: _, _, h => by simp [aloneFrom] at h
  | _ :: _, _, _, [], _, h => by simp [aloneFrom] at h
  | mv :: ms, t, seen, d :: ds, x, h => by
    unfold aloneFrom at h
    cases hs : mv.say c seen t with
    | error e => simp [hs] at h
    | ok y =>
      simp only [hs] at h
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h
      have ih := aloneFrom_length c ms _ _ ds x' hx'
      exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- **Steps that never stop and whose messages have the stated shape.** -/
theorem play_stepsFrom (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (hb : ∀ f o, bad f o = none) (hh : ∀ f o, hid f o = none) (n : Nat) (c : C) :
    ∀ (l : List ((Fmt.DeclaredRound × List Oracle) × Move C W X)) (k : Nat) (ds : List Fmt.Drawn)
      (back : List Fmt.RoundView) (t : State W X) (loc : List Fmt.Drawn) (seen : Seen) (x : List Fmt.RoundView),
      (∀ r ∈ l, ∀ (sn : Seen) (u : State W X) (y : Sending), r.2.say c sn u = .ok y →
        y.fits r.1.1 r.1.2 = true) →
      aloneFrom c (l.map (·.2)) t seen ds = some x →
      ∃ y, play (stepsFrom name a bad hid n c l k) ds back ⟨t, loc, seen.rounds, seen.opened⟩ =
          .ok y ∧
        roundsOf y.1 = x ∧
        y.2 = ⟨endFrom (l.map (·.2)) t ds, loc ++ ds, seen.rounds ++ x, seen.opened⟩
  | [], k, [], back, t, loc, seen, x, _, h => by
    simp only [List.map_nil, aloneFrom, Option.some.injEq] at h
    subst h
    exact ⟨([], ⟨t, loc, seen.rounds, seen.opened⟩), by simp [stepsFrom, play], rfl,
      by simp [endFrom]⟩
  | [], _, _ :: _, _, _, _, _, _, _, h => by simp [aloneFrom] at h
  | _ :: _, _, [], _, _, _, _, _, _, h => by simp [aloneFrom] at h
  | r :: l, k, d :: ds, back, t, loc, seen, x, hf, h => by
    simp only [List.map_cons] at h
    unfold aloneFrom at h
    cases hs : r.2.say c seen t with
    | error e => simp [hs] at h
    | ok y₀ =>
      simp only [hs] at h
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h
      have hfit := hf r List.mem_cons_self seen t y₀ hs
      obtain ⟨z, hz, hz1, hz2⟩ := play_stepsFrom name a bad hid hb hh n c l (k + 1) ds back.tail
        { t.hears d with own := r.2.hand (t.hears d) } (loc ++ [d])
        (seen.plus [⟨y₀.vals.map Said.got, d⟩]) x'
        (fun r' hr' => hf r' (List.mem_cons_of_mem _ hr')) hx'
      simp only [Seen.plus] at hz hz2
      let s : Step W X := ⟨name, a, r.1.1, r.1.2, bad, hid, k, k + 1 == n,
        some ⟨fun _ => r.2.say c, r.2.hand⟩⟩
      have hstop : ∀ l' n', s.stop l' n' = none := stop_none s hb hh
      have hs' : r.2.say c (⟨t, loc, seen.rounds, seen.opened⟩ : Mid W X).shown t = .ok y₀ := hs
      have htell : s.tell back.head? ⟨t, loc, seen.rounds, seen.opened⟩ =
          .ok ⟨y₀.vals.map Said.got, y₀.tables.map some, true⟩ := by
        simp only [Step.tell, hstop]
        simp only [s, hs', hfit, Bool.not_true, Bool.false_eq_true, if_false]
      have hhear : s.hear ⟨y₀.vals.map Said.got, y₀.tables.map some, true⟩ d
            ⟨t, loc, seen.rounds, seen.opened⟩ =
          .ok ⟨{ t.hears d with own := r.2.hand (t.hears d) }, loc ++ [d],
            seen.rounds ++ [⟨y₀.vals.map Said.got, d⟩], seen.opened⟩ := by
        simp only [Step.hear, hstop, ite_self]
        rfl
      have hsteps : stepsFrom name a bad hid n c (r :: l) k =
          s :: stepsFrom name a bad hid n c l (k + 1) := by
        simp [stepsFrom, List.zipIdx_cons, s]
      refine ⟨(⟨s.name, s.addr.place, s.addr.part, true, y₀.vals.map Said.got,
        y₀.tables.map some, d⟩ :: z.1, z.2), ?_, ?_, ?_⟩
      · rw [hsteps]
        simp only [play, htell, hhear, hz, Except.bind, Except.map, if_true]
      · simp only [roundsOf, List.map_cons] at hz1 ⊢
        rw [hz1]
      · rw [hz2]
        simp [endFrom, List.append_assoc]

/-- **A part that never stops and whose messages have the stated shape**: where it answers alone,
the frame's player goes through on its steps and yields the same rounds. -/
theorem play_part (p : Part V W X) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ v f o, p.hid v f o = none) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins)
    (hl : rs.length = p.moves.length)
    (hf : ∀ r ∈ rs.zip p.moves, ∀ (sn : Seen) (u : State W X) (y : Sending),
      r.2.say c sn u = .ok y → y.fits r.1.1 r.1.2 = true)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (t : State W X) (loc : List Fmt.Drawn)
    (seen : Seen) (x : List Fmt.RoundView) (h : alone p c t seen ds = some x) :
    ∃ y, play (p.steps name a rs v c) ds back ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      roundsOf y.1 = x ∧
      y.2 = ⟨endFrom p.moves t ds, loc ++ ds, seen.rounds ++ x, seen.opened⟩ := by
  have hm : (rs.zip p.moves).map (·.2) = p.moves := by
    rw [List.map_snd_zip]
    omega
  have h' : aloneFrom c ((rs.zip p.moves).map (·.2)) t seen ds = some x := by rw [hm]; exact h
  have := play_stepsFrom name a p.bad (fun f o => v.bind fun w => p.hid w f o) hb
    (fun f o => by cases v <;> simp [hh]) p.moves.length c (rs.zip p.moves) 0 ds back t loc seen x
    hf h'
  rw [hm] at this
  exact this

/-! ## A row -/

/-- The state behind a row's moves. -/
def endRow : List (Part V W X) → State W X → List Fmt.Drawn → State W X
  | [], t, _ => t
  | p :: ps, t, ds =>
    endRow ps (endFrom p.moves t (ds.take p.moves.length)) (ds.drop p.moves.length)

/-- A row's parts, each played alone, one behind the other. -/
def aloneRow : (ps : List (Part V W X)) → RowCoins ps → State W X → Seen →
    List Fmt.Drawn → Option (List Fmt.RoundView)
  | [], _, _, _, [] => some []
  | [], _, _, _, _ :: _ => none
  | p :: ps, c, t, seen, ds =>
    (alone p c.1 t seen (ds.take p.moves.length)).bind fun x =>
      (aloneRow ps c.2 (endFrom p.moves t (ds.take p.moves.length)) (seen.plus x)
        (ds.drop p.moves.length)).map (x ++ ·)

/-- No part of the row ever stops. -/
def NoStops (ps : List (Part V W X)) : Prop :=
  ∀ p ∈ ps, (∀ f o, p.bad f o = none) ∧ ∀ v f o, p.hid v f o = none

/-- Every message of the row has the shape that its round states; and there are rounds for all
moves. -/
def RowFits : (ps : List (Part V W X)) → List (Fmt.DeclaredRound × List Oracle) → RowCoins ps → Prop
  | [], rs, _ => rs = []
  | p :: ps, rs, c =>
    p.moves.length ≤ rs.length ∧
    (∀ r ∈ (rs.take p.moves.length).zip p.moves, ∀ (sn : Seen) (u : State W X) (y : Sending),
      r.2.say c.1 sn u = .ok y → y.fits r.1.1 r.1.2 = true) ∧
    RowFits ps (rs.drop p.moves.length) c.2

/-- **A row whose parts never stop and whose messages have the stated shapes**: where its parts
answer alone, one behind the other, the frame's player goes through on the row's steps and yields
the same rounds. -/
theorem play_row (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (t : State W X)
      (loc : List Fmt.Drawn) (seen : Seen) (x : List Fmt.RoundView),
      NoStops ps → RowFits ps rs c → aloneRow ps c t seen ds = some x →
      ∃ y, play (rowSteps name a v ps j rs c) ds back ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
        roundsOf y.1 = x ∧ y.2 = ⟨endRow ps t ds, loc ++ ds, seen.rounds ++ x, seen.opened⟩
  | [], j, rs, c, [], back, t, loc, seen, x, _, _, h => by
    simp only [aloneRow, Option.some.injEq] at h
    subst h
    exact ⟨([], ⟨t, loc, seen.rounds, seen.opened⟩), by simp [rowSteps, play], rfl,
      by simp [endRow]⟩
  | [], _, _, _, _ :: _, _, _, _, _, _, _, _, h => by simp [aloneRow] at h
  | p :: ps, j, rs, c, ds, back, t, loc, seen, x, hn, hf, h => by
    unfold aloneRow at h
    obtain ⟨x₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨x₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hlen, hfit, hrest⟩ := hf
    have hp := hn p List.mem_cons_self
    have hl : (rs.take p.moves.length).length = p.moves.length := by
      rw [List.length_take]; omega
    obtain ⟨y₁, hy, hy1, hy2⟩ := play_part p hp.1 hp.2 name ⟨a, j⟩ (rs.take p.moves.length) v c.1
      hl hfit (ds.take p.moves.length) back t loc seen x₁ h₁
    obtain ⟨y₂, hz, hz1, hz2⟩ := play_row name a v ps (j + 1) (rs.drop p.moves.length) c.2
      (ds.drop p.moves.length)
      (back.drop (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length)
      (endFrom p.moves t (ds.take p.moves.length)) (loc ++ ds.take p.moves.length) (seen.plus x₁)
      x₂ (fun q hq => hn q (List.mem_cons_of_mem _ hq)) hrest h₂
    simp only [Seen.plus] at hz hz2
    have hd : (ds.take p.moves.length).length =
        (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length := by
      rw [(aloneFrom_length c.1 p.moves t seen _ x₁ h₁).1]
      simp [Part.steps, hl]
    refine ⟨(y₁.1 ++ y₂.1, y₂.2), ?_, ?_, ?_⟩
    · have := play_append (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1)
        (rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2) (ds.take p.moves.length)
        (ds.drop p.moves.length) back ⟨t, loc, seen.rounds, seen.opened⟩ hd
      rw [List.take_append_drop] at this
      rw [rowSteps, this, hy]
      simp only [Except.bind, hy2, hz, Except.map]
    · simp only [roundsOf, List.map_append] at hy1 hz1 ⊢
      rw [hy1, hz1]
    · rw [hz2]
      simp [endRow, List.append_assoc]

/-! ## What the played rounds bear -/

theorem stepsFrom_mem (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (n : Nat) (c : C) :
    ∀ (l : List ((Fmt.DeclaredRound × List Oracle) × Move C W X)) (k : Nat) (s : Step W X),
      s ∈ stepsFrom name a bad hid n c l k →
      s.addr = a ∧ s.move.isSome = true ∧ ∃ r ∈ l, s.oracles = r.1.2
  | [], _, _, h => by simp [stepsFrom] at h
  | r :: l, k, s, h => by
    have e : stepsFrom name a bad hid n c (r :: l) k =
        ⟨name, a, r.1.1, r.1.2, bad, hid, k, k + 1 == n, some ⟨fun _ => r.2.say c, r.2.hand⟩⟩ ::
          stepsFrom name a bad hid n c l (k + 1) := by
      simp [stepsFrom, List.zipIdx_cons]
    rw [e, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl, r, List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2, r', hr', h3⟩ := stepsFrom_mem name a bad hid n c l (k + 1) s h
      exact ⟨h1, h2, r', List.mem_cons_of_mem _ hr', h3⟩

/-- Every step of a row stands at the row's place, has a move, and states the oracle messages of one
of the rounds. -/
theorem rowSteps_mem (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps) (s : Step W X), s ∈ rowSteps name a v ps j rs c →
      s.addr.place = a ∧ s.move.isSome = true ∧ ∃ r ∈ rs, s.oracles = r.2
  | [], _, _, _, _, h => by simp [rowSteps] at h
  | p :: ps, j, rs, c, s, h => by
    rw [rowSteps, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨h1, h2, r, hr, h3⟩ := stepsFrom_mem name ⟨a, j⟩ p.bad
        (fun f o => v.bind fun w => p.hid w f o) p.moves.length c.1
        ((rs.take p.moves.length).zip p.moves) 0 s h
      exact ⟨by rw [h1], h2, r.1, List.mem_of_mem_take (List.of_mem_zip hr).1, h3⟩
    · obtain ⟨h1, h2, r, hr, h3⟩ := rowSteps_mem name a v ps (j + 1) _ c.2 s h
      exact ⟨h1, h2, r, List.mem_of_mem_drop hr, h3⟩

theorem yields_mem : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → ∀ q ∈ ps, ∃ s ∈ ss, ∃ b d, s.Yields b d q
  | [], [], _, [], _, _, hq => by simp at hq
  | s :: ss, d :: ds, back, p :: ps, h, q, hq => by
    have h' : s.Yields back.head? d p ∧ Yields ss ds back.tail ps := h
    rw [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨s, List.mem_cons_self, _, _, h'.1⟩
    · obtain ⟨s', hs', x⟩ := yields_mem ss ds back.tail ps h'.2 q hq
      exact ⟨s', List.mem_cons_of_mem _ hs', x⟩
  | [], [], _, _ :: _, h, _, _ => h.elim
  | [], _ :: _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, h, _, _ => h.elim
  | _ :: _, _ :: _, _, [], h, _, _ => h.elim

/-- **What every round bears that was played on a row's steps**, where no round of the row states an
oracle message: the row's place; that a half made it; no table. -/
theorem played_row (name : String) (a : Place) (v : Option V) (ps : List (Part V W X)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (h : play (rowSteps name a v ps j rs c) ds back m = .ok y) (hos : ∀ r ∈ rs, r.2 = []) :
    ∀ q ∈ y.1, q.place = a ∧ q.told = true ∧ q.tables = [] := by
  intro q hq
  obtain ⟨s, hs, b, d, _, h2, h3, h4, _⟩ := yields_mem _ _ _ _ (play_yields _ _ _ _ _ h) q hq
  obtain ⟨g1, g2, r, hr, g3⟩ := rowSteps_mem name a v ps j rs c s hs
  obtain ⟨_, x, hx, _, ht⟩ := h4 g2
  refine ⟨h2.trans g1, h3.trans g2, ?_⟩
  rw [g3, hos r hr] at hx
  simp only [Sending.fits, List.map_nil, Bool.and_eq_true, beq_iff_eq, List.map_eq_nil_iff] at hx
  rw [ht, hx.2]
  rfl

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.played_row
#print axioms ProofFile.Honest.K3.Law.stop_none
#print axioms ProofFile.Honest.K3.Law.aloneFrom_length
#print axioms ProofFile.Honest.K3.Law.play_stepsFrom
#print axioms ProofFile.Honest.K3.Law.play_part
#print axioms ProofFile.Honest.K3.Law.play_row
#print axioms ProofFile.Honest.K3.Law.stepsFrom_mem
#print axioms ProofFile.Honest.K3.Law.rowSteps_mem
#print axioms ProofFile.Honest.K3.Law.yields_mem
