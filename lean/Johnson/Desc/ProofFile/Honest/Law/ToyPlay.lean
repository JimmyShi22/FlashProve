-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyPlay.lean: equations that compute `play` (Honest/Frame.lean)
one round at a time. `play` runs the prover's side of a list of rounds at given challenges. The
equations cover a round whose two stops (the abort conditions `bad` and `hid`) never fire and whose
move returns a message of the shape that the sub-protocol declares. The move is handed `m.shown`:
the rounds shown and the columns opened, whatever these are. Those about `play` take its third
argument, a stored run's rounds to fall back on, to be empty. Despite its name, the file contains
no example and names no sub-protocol.

  1  `Mid.after`, `playedOf`   the state of a run after such a round; the round as played
  2  `stop_none`, `tell_ok`, `hear_ok`   what `Step.stop`, `Step.tell` and `Step.hear` return there
  3  `play_step`, `play_nil`, `play_one`, `play_two`   `play` on a first round followed by others,
     on no round, on one round, on two rounds

These lemmas go forwards, from a move's message to the result of `play`. Honest/Law/Play.lean goes
backwards, from a successful result of `play` to what each round did (`play_cons_ok`,
`tell_yields`).

Limits. The lemmas are equations about `play` and the three functions of one round (`Step.stop`,
`Step.tell`, `Step.hear`). They prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W X : Type}

/-! ## 1 After a round -/

/-- The state of a run after a round with the move `mv`, in which the items `vals` were sent in the
clear and the challenge was `d`. The field `opened` is carried on as it is: no round changes it. -/
def Mid.after (m : Mid W X) (mv : Move Unit W X) (vals : List Fmt.ItemValue) (d : Fmt.Drawn) : Mid W X :=
  ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d], m.seen ++ [⟨vals, d⟩],
    m.opened⟩

/-- The played round (`Played`) in which the prover's side sent `z` and the challenge was `d`. -/
def playedOf (s : Step W X) (z : Sending) (d : Fmt.Drawn) : Played :=
  ⟨s.name, s.addr.place, s.addr.part, true, z.vals.map Said.got, z.tables.map some, d⟩

/-! ## 2 The three functions of one round -/

theorem stop_none {s : Step W X} (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    (l : List Fmt.Drawn) (n : Nat) : s.stop l n = none := by
  simp only [Step.stop, hb, hh]

theorem tell_ok {s : Step W X} {b : Option Fmt.RoundView} {m : Mid W X} {mv : Move Unit W X} {z : Sending}
    (hst : s.stop m.loc s.nth = none) (hmv : s.move = some mv)
    (hz : mv.say () m.shown m.st = .ok z) (hf : z.fits s.decl s.oracles = true) :
    s.tell b m = .ok ⟨z.vals.map Said.got, z.tables.map some, true⟩ := by
  simp [Step.tell, hst, hmv, hz, hf]

theorem hear_ok {s : Step W X} {x : Told} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X}
    (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none) (hmv : s.move = some mv) :
    s.hear x d m = .ok (m.after mv x.vals d) := by
  simp [Step.hear, hmv, stop_none hb hh, Mid.after]

/-! ## 3 A run, round by round -/

/-- **A first round followed by others.** -/
theorem play_step {s : Step W X} {ss : List (Step W X)} {d : Fmt.Drawn} {ds : List Fmt.Drawn}
    {m : Mid W X} {mv : Move Unit W X} {z : Sending} (hb : ∀ f o, s.bad f o = none)
    (hh : ∀ f o, s.hid f o = none) (hmv : s.move = some mv)
    (hz : mv.say () m.shown m.st = .ok z) (hf : z.fits s.decl s.oracles = true) :
    play (s :: ss) (d :: ds) [] m =
      (play ss ds [] (m.after mv (z.vals.map Said.got) d)).map fun y =>
        (playedOf s z d :: y.1, y.2) := by
  have hx : s.tell ([] : List Fmt.RoundView).head? m =
      .ok ⟨z.vals.map Said.got, z.tables.map some, true⟩ :=
    tell_ok (stop_none hb hh m.loc s.nth) hmv hz hf
  have hm : s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m =
      .ok (m.after mv (z.vals.map Said.got) d) := hear_ok hb hh hmv
  rw [play, hx]
  show (s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m).bind _ = _
  rw [hm]
  rfl

theorem play_nil (m : Mid W X) : play ([] : List (Step W X)) [] [] m = .ok ([], m) := by
  rw [play]

/-- **One round.** -/
theorem play_one {s : Step W X} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X} {z : Sending}
    (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none) (hmv : s.move = some mv)
    (hz : mv.say () m.shown m.st = .ok z) (hf : z.fits s.decl s.oracles = true) :
    play [s] [d] [] m = .ok ([playedOf s z d], m.after mv (z.vals.map Said.got) d) := by
  rw [play_step hb hh hmv hz hf, play_nil]
  rfl

/-- **Two rounds.** The second move computes its message at the state after the first round. -/
theorem play_two {s₀ s₁ : Step W X} {d₀ d₁ : Fmt.Drawn} {m : Mid W X} {mv₀ mv₁ : Move Unit W X}
    {z₀ z₁ : Sending} (hb₀ : ∀ f o, s₀.bad f o = none) (hh₀ : ∀ f o, s₀.hid f o = none)
    (hmv₀ : s₀.move = some mv₀) (hz₀ : mv₀.say () m.shown m.st = .ok z₀)
    (hf₀ : z₀.fits s₀.decl s₀.oracles = true) (hb₁ : ∀ f o, s₁.bad f o = none)
    (hh₁ : ∀ f o, s₁.hid f o = none) (hmv₁ : s₁.move = some mv₁)
    (hz₁ : mv₁.say () (m.after mv₀ (z₀.vals.map Said.got) d₀).shown
      (m.after mv₀ (z₀.vals.map Said.got) d₀).st = .ok z₁)
    (hf₁ : z₁.fits s₁.decl s₁.oracles = true) :
    play [s₀, s₁] [d₀, d₁] [] m =
      .ok ([playedOf s₀ z₀ d₀, playedOf s₁ z₁ d₁],
        (m.after mv₀ (z₀.vals.map Said.got) d₀).after mv₁ (z₁.vals.map Said.got) d₁) := by
  rw [play_step hb₀ hh₀ hmv₀ hz₀ hf₀, play_one hb₁ hh₁ hmv₁ hz₁ hf₁]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.stop_none
#print axioms ProofFile.Honest.tell_ok
#print axioms ProofFile.Honest.hear_ok
#print axioms ProofFile.Honest.play_step
#print axioms ProofFile.Honest.play_nil
#print axioms ProofFile.Honest.play_one
#print axioms ProofFile.Honest.play_two
#print axioms ProofFile.Honest.Mid.after
#print axioms ProofFile.Honest.playedOf
