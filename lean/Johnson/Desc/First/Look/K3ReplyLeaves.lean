-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3ReplyLeaves.lean: THE KIND "LOOKUP" (K3) LEAVES THE REPLY THAT WAS HEARD
AS IT IS: the frame fact on the reply, OF THE BLOCK THAT RIDES at every address of K3. Without
Mathlib.

Why. Along the first chain one witness is carried from the last statement to the first, and its
token is the reply that the chain's last record holds (Johnson/Desc/Sound/LeadsE.lean:
`steps_token`). That rests on a fact on every block's text but the one that hears the reply: THE
RECORD'S REPLY IS NOT TURNED: an equation, both ways.

Main theorems:
  `block_put`, `blockVia_put`: where K3's `decide` says yes, the record behind is the seat's `put`
    at the record in front, at something heard and a ledger: at every seat; of the middle term
    `block` and of the block that is seated.
  `mark_out`, `putFork_out`, `putTl_out`, `hearLook_out`: four writers of the carried record do not
    turn the field `out` (the index masks' number, the pile, the reply that was heard): whoever
    writes through these has the fact for nothing. `calls_out`, `digits_out`, `block_out`,
    `blockVia_out`: so of `put` and of `decide` at the two seats that run.
  `quietLook_out`, `quietDigits_out`, `quietHead_out`, `quietAt_out`: so of the quiet halves.
  **`theWhole_out`: THE BLOCK THAT RIDES AT AN ADDRESS (`theWhole`: `decide`, then its quiet half):
    where it says yes, `out` is not turned. `theWhole_reply`: so `replyTok?` behind is `replyTok?`
    in front.**

Limits: of the blocks' `decide`: K3's runs of claims are not looked at. A block that refuses all
meets it for nothing. Nothing on soundness; nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3PointAtSeats
import Johnson.Desc.First.Look.K3Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork)

theorem block_put {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl))
    {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (H : (block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g G, s' = seat.put s g G := by
  unfold block at H
  dsimp only at H
  obtain ⟨F, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨x, -, H⟩ := ebind_ok H
  cases H
  exact ⟨x.1, x.2, rfl⟩

/-- The like of the block that is seated (`Law.blockVia`, Via/Via.lean). -/
theorem blockVia_put {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl))
    {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (H : (Law.blockVia seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g G, s' = seat.put s g G := by
  unfold Law.blockVia at H
  dsimp only at H
  unfold Law.decideVia at H
  obtain ⟨F, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨x, -, H⟩ := ebind_ok H
  cases H
  exact ⟨x.1, x.2, rfl⟩

theorem mark_out (s : First.S) (n : String) : (s.mark n).out = s.out := by
  unfold First.S.mark
  split <;> rfl

theorem putFork_out (s : First.S) (G : Fork) : (s.putFork G).out = s.out := by
  unfold First.S.putFork
  repeat' split
  all_goals rfl

theorem putTl_out (s : First.S) (tl : Model.HTailF2) : (s.putTl tl).out = s.out := by
  unfold First.S.putTl
  repeat' split
  all_goals rfl

theorem hearLook_out (s : First.S) (g : Model.Forest.Heard) : (s.hearLook g).out = s.out := by
  unfold First.S.hearLook
  repeat' split
  all_goals first | rfl | exact mark_out _ _

theorem calls_out {Cl : Type} (claim : Aff → Cl) (s : First.S) (g : Model.Forest.Heard)
    (G : Fork) : ((seatCalls claim).put s g G).out = s.out := by
  show ((s.putFork G).hearLook g).out = s.out
  rw [hearLook_out, putFork_out]

theorem digits_out {Cl : Type} (claim : Aff → Cl) (s : First.S) (g : Model.Forest.Heard)
    (G : Fork) : ((seatDigits claim).put s g G).out = s.out := by
  unfold seatDigits
  dsimp only
  split
  · rw [putFork_out, putTl_out]
  · exact mark_out _ _

/-- **Where K3's `decide` says yes at a seat that runs, the field `out` is not turned.** -/
theorem block_out {Cl : Type} (claim : Aff → Cl) (digits : Bool) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P)
    (guests : List (First.Look.Guest First.S Cl)) {s s' : First.S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))}
    (H : (block (if digits then seatDigits claim else seatCalls claim) piece laid before p
      guests).decide s rs cols = .ok s') : s'.out = s.out := by
  obtain ⟨g, G, rfl⟩ := block_put _ piece laid before p guests H
  cases digits
  · exact calls_out claim s g G
  · exact digits_out claim s g G

/-- **The like of the block that is seated.** -/
theorem blockVia_out {Cl : Type} (claim : Aff → Cl) (digits : Bool) (piece : Nat)
    (laid : Array Nat) (before : List (Nat × Nat)) (p : First.Look.P)
    (guests : List (First.Look.Guest First.S Cl)) {s s' : First.S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))}
    (H : (Law.blockVia (if digits then seatDigits claim else seatCalls claim) piece laid before p
      guests).decide s rs cols = .ok s') : s'.out = s.out := by
  obtain ⟨g, G, rfl⟩ := blockVia_put _ piece laid before p guests H
  cases digits
  · exact calls_out claim s g G
  · exact digits_out claim s g G

/-! ## The quiet halves -/

theorem quietLook_out (fs : Model.Forest.Shape) {s s' : First.S}
    (H : quietLook fs s = .ok s') : s'.out = s.out := by
  unfold quietLook at H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  cases H
  rfl

theorem quietDigits_out (used claims : Nat) {s s' : First.S}
    (H : quietDigits used claims s = .ok s') : s'.out = s.out := by
  unfold quietDigits at H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨G, -, H⟩ := ebind_ok H
  cases H
  exact putFork_out s G

theorem quietHead_out (X : Model.Verify.Public) {s s' : First.S}
    (H : quietHead X s = .ok s') : s'.out = s.out := by
  unfold quietHead at H
  split at H
  · obtain ⟨_, -, H⟩ := ebind_ok H
    obtain ⟨_, -, H⟩ := ebind_ok H
    obtain ⟨_, -, H⟩ := ebind_ok H
    obtain ⟨_, -, H⟩ := ebind_ok H
    obtain ⟨_, -, H⟩ := ebind_ok H
    obtain ⟨_, -, H⟩ := ebind_ok H
    cases H
    rfl
  · cases H

theorem quietAt_out (X : Model.Verify.Public) (i : Nat) (digits : Bool)
    {f : First.S → Except String First.S} (hf : quietAt X i digits = some f) {s s' : First.S}
    (H : f s = .ok s') : s'.out = s.out := by
  unfold quietAt at hf
  dsimp only at hf
  by_cases h1 : isHead X i = true
  · rw [if_pos h1] at hf
    cases digits
    · cases hf
    · cases hf
      exact quietHead_out X H
  · rw [if_neg h1] at hf
    by_cases h2 : (i % (if X.p4 = true then 2 else 1) == 0) = true
    · rw [if_pos h2] at hf
      cases digits
      · cases hf
        exact quietLook_out _ H
      · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact quietDigits_out _ _ H
    · rw [if_neg h2] at hf
      cases digits
      · cases hf
      · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact quietDigits_out _ _ H

/-! ## The block that rides -/

/-- The block at an address, without its quiet half. -/
theorem theOwn_out {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block First.S Cl}
    (hb : theOwn claim runs X codes shape a = some b) {s s' : First.S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (H : b.decide s rs cols = .ok s') :
    s'.out = s.out := by
  unfold theOwn at hb
  split at hb
  · cases hb
  · obtain ⟨i, -, hb⟩ := Option.bind_eq_some_iff.1 hb
    obtain ⟨digits, -, hb⟩ := List.exists_of_findSome?_eq_some hb
    split at hb
    · cases hb
    · obtain ⟨p, -, hb⟩ := Option.bind_eq_some_iff.1 hb
      obtain ⟨sent, -, hb⟩ := Option.bind_eq_some_iff.1 hb
      obtain ⟨laid, -, hb⟩ := Option.bind_eq_some_iff.1 hb
      obtain ⟨key, -, hb⟩ := Option.map_eq_some_iff.1 hb
      subst hb
      cases runs
      · exact blockVia_out claim digits a.piece laid sent p [] (rs := rs) (cols := cols) H
      · exact blockVia_out claim digits a.piece laid sent p [] (rs := rs) (cols := cols) H

/-- **THE ROW: THE BLOCK THAT RIDES AT AN ADDRESS OF K3 (its `decide`, then its quiet half) DOES NOT
TURN THE FIELD `out`**: the index masks' number, the pile, the reply that was heard. -/
theorem theWhole_out {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block First.S Cl}
    (hb : theWhole claim runs X codes shape a = some b) {s s' : First.S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (H : b.decide s rs cols = .ok s') :
    s'.out = s.out := by
  unfold theWhole at hb
  obtain ⟨b₀, h₀, hb⟩ := Option.map_eq_some_iff.1 hb
  split at hb
  · rename_i f hf
    subst hb
    obtain ⟨i, -, hq⟩ := Option.bind_eq_some_iff.1 hf
    obtain ⟨s₁, h₁, h₂⟩ := ebind_ok (show (b₀.decide s _ _ >>= fun s' => f s') = .ok s' from H)
    rw [quietAt_out X i _ hq h₂, theOwn_out claim runs X codes shape a h₀ h₁]
  · subst hb
    exact theOwn_out claim runs X codes shape a h₀ H

/-- **reply_leaves, of the block that rides.** -/
theorem theWhole_reply {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block First.S Cl}
    (hb : theWhole claim runs X codes shape a = some b) {s s' : First.S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (H : b.decide s rs cols = .ok s') :
    s'.replyTok? = s.replyTok? := by
  unfold First.S.replyTok?
  rw [theWhole_out claim runs X codes shape a hb H]

end VerifiableInference.Desc.K3
