-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyStop.lean: what `play` (Honest/Frame.lean) returns at one round
of a part that has a stop: where the stop returns `none`, and where it stops the part after the
round. It stands beside Honest/Law/ToyPlay.lean, whose lemmas ask that the stops always return
`none`. No toy example and no sub-protocol occurs here.

  1  `take_snoc`, `drop_snoc`, `stop_front`, `stop_last_none`, `stop_last_bad`   what the two stops
     are given before a part's first round and after a part of one round
  2  `hear_go`, `hear_halt`, `play_one_go`, `play_one_halt`   the round, played

Limits.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W X : Type}

/-! ## 1 What the stops are given -/

theorem take_snoc {α : Type} (l : List α) (d : α) :
    (l ++ [d]).take ((l ++ [d]).length - 1) = l := by
  simp

theorem drop_snoc {α : Type} (l : List α) (d : α) :
    (l ++ [d]).drop ((l ++ [d]).length - 1) = [d] := by
  simp

/-- Before a part's first round the stops are given none of its own challenges. -/
theorem stop_front {s : Step W X} (l : List Fmt.Drawn) (hb : ∀ f, s.bad f [] = none)
    (hh : ∀ f, s.hid f [] = none) : s.stop l 0 = none := by
  simp [Step.stop, hb, hh]

/-- After a part of one round they are given that round's challenge. -/
theorem stop_last_none {s : Step W X} {l : List Fmt.Drawn} {d : Fmt.Drawn}
    (hb : s.bad l [d] = none) (hh : s.hid l [d] = none) : s.stop (l ++ [d]) 1 = none := by
  simp only [Step.stop, take_snoc, drop_snoc, hb, hh]

theorem stop_last_bad {s : Step W X} {l : List Fmt.Drawn} {d : Fmt.Drawn} {e : String}
    (hb : s.bad l [d] = some e) :
    s.stop (l ++ [d]) 1 = some ⟨.bad, s.name ++ ": " ++ e⟩ := by
  simp only [Step.stop, take_snoc, drop_snoc, hb]

/-! ## 2 The round, played -/

theorem hear_go {s : Step W X} {x : Told} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X}
    (hmv : s.move = some mv) (hst : s.stop (m.loc ++ [d]) (s.nth + 1) = none) :
    s.hear x d m = .ok (m.after mv x.vals d) := by
  simp [Step.hear, hmv, hst, Mid.after]

theorem hear_halt {s : Step W X} {x : Told} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X}
    {e : Refusal} (hmv : s.move = some mv) (hl : s.last = true)
    (hst : s.stop (m.loc ++ [d]) (s.nth + 1) = some e) : s.hear x d m = .error e := by
  simp [Step.hear, hmv, hl, hst]

/-- **One round at which no stop fires.** -/
theorem play_one_go {s : Step W X} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X} {z : Sending}
    (h₀ : s.stop m.loc s.nth = none) (h₁ : s.stop (m.loc ++ [d]) (s.nth + 1) = none)
    (hmv : s.move = some mv) (hz : mv.say () m.shown m.st = .ok z)
    (hf : z.fits s.decl s.oracles = true) :
    play [s] [d] [] m = .ok ([playedOf s z d], m.after mv (z.vals.map Said.got) d) := by
  have hx : s.tell ([] : List Fmt.RoundView).head? m =
      .ok ⟨z.vals.map Said.got, z.tables.map some, true⟩ := tell_ok h₀ hmv hz hf
  have hm : s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m =
      .ok (m.after mv (z.vals.map Said.got) d) := hear_go hmv h₁
  rw [play, hx]
  show (s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m).bind _ = _
  rw [hm]
  rfl

/-- **One round after which a stop stops the part**: the run returns that error. -/
theorem play_one_halt {s : Step W X} {d : Fmt.Drawn} {m : Mid W X} {mv : Move Unit W X}
    {z : Sending} {e : Refusal} (h₀ : s.stop m.loc s.nth = none) (hl : s.last = true)
    (h₁ : s.stop (m.loc ++ [d]) (s.nth + 1) = some e) (hmv : s.move = some mv)
    (hz : mv.say () m.shown m.st = .ok z) (hf : z.fits s.decl s.oracles = true) :
    play [s] [d] [] m = .error e := by
  have hx : s.tell ([] : List Fmt.RoundView).head? m =
      .ok ⟨z.vals.map Said.got, z.tables.map some, true⟩ := tell_ok h₀ hmv hz hf
  have hm : s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m = .error e :=
    hear_halt hmv hl h₁
  rw [play, hx]
  show (s.hear ⟨z.vals.map Said.got, z.tables.map some, true⟩ d m).bind _ = _
  rw [hm]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.take_snoc
#print axioms ProofFile.Honest.drop_snoc
#print axioms ProofFile.Honest.stop_front
#print axioms ProofFile.Honest.stop_last_none
#print axioms ProofFile.Honest.stop_last_bad
#print axioms ProofFile.Honest.hear_go
#print axioms ProofFile.Honest.hear_halt
#print axioms ProofFile.Honest.play_one_go
#print axioms ProofFile.Honest.play_one_halt
