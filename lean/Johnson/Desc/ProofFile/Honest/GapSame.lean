-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/GapSame.lean: the state of the prover's run (`Mid`,
Honest/Frame.lean) has a field `opened`: the columns opened so far. `play` leaves that field as it
is; `walk` (Honest/Walk.lean) lengthens it after each sub-protocol. This file shows that the two
reach the same state but for that field, as long as no move on the way depends on the columns handed
to it (`Step.Blind`, Honest/Blind.lean). No definition.

  1  `tell_field`   a blind step's message is the same whatever the field holds
  2  `hear_field`   hearing a challenge carries the field on and reads nothing of it. No hypothesis
  3  `play_field`   `play` over blind steps from a state with another field: the same rounds, and
     the same state but for the field
  4  `settle_same`   `ChainProgress.settle` changes nothing of the prover's state but the field
  5  `walk_play`   **where a walk over blind steps ends with the run still played, `play` from the
     walk's first state returns, and the two last states agree but for the field**
  6  `midInW_midIn`   the same for the state before the part at an address, in one chain

Limits.
  * The direction is from the walk to `play`. That the walk's state is `some` says besides that the
    verifier has accepted every sub-protocol asked on the way. The converse is not stated.
  * Where a step on the way is not blind, 3, 5 and 6 say nothing. A part that reads the columns and
    is played by `play` from a state at which no columns are handed is handed none.
  * Once the parts of the kind K10 that read the columns are laid, the hypothesis of 6 (the steps
    before the address are blind) is false at each address of the first chain behind the first of
    them. A lemma that goes on to `midAt` (Honest/Frame.lean) needs it of the whole first chain too,
    since `midAt` reaches the second chain through it: such a lemma is silent in all of the second
    chain. There a lemma is to be stated of the walk's own state, with no hypothesis on the steps.
  * The hypotheses on the steps are shown at no chain: `Part.steps_blind` (Honest/Blind.lean)
    reaches one part's steps alone.
  * `midAtW` (Honest/MidW.lean) against `midAt`, over the three chains of a run, is not in this
    file.
  * `play` is taken with no stored run to fall back on in 5 and 6.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Gap
import Johnson.Desc.ProofFile.Honest.Blind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl W Y : Type}

/-! ## 1 One round -/

/-- A blind step's message is the same whatever the field holds. -/
theorem tell_field {s : Step W Y} (hb : s.Blind) (back : Option Fmt.RoundView) (m : Mid W Y)
    (o : Option (List OpenedColumn)) : s.tell back { m with opened := o } = s.tell back m := by
  cases hm : s.move with
  | none => simp only [Step.tell, hm]
  | some mv =>
    have e : mv.say () ⟨m.seen, o⟩ m.st = mv.say () ⟨m.seen, m.opened⟩ m.st :=
      hb mv hm () m.seen o m.opened m.st
    simp only [Step.tell, hm, Mid.shown, e]

/-- Hearing a challenge carries the field on and reads nothing of it. -/
theorem hear_field (s : Step W Y) (x : Told) (d : Fmt.Drawn) (m : Mid W Y)
    (o : Option (List OpenedColumn)) :
    s.hear x d { m with opened := o } = (s.hear x d m).map ({ · with opened := o }) := by
  cases hm : s.move with
  | none =>
    simp only [Step.hear, hm]
    rfl
  | some mv =>
    simp only [Step.hear, hm]
    split <;> rfl

/-! ## 2 A run of rounds -/

/-- `play` over blind steps from a state with another field. -/
theorem play_field : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W Y) (o : Option (List OpenedColumn)), (∀ s ∈ ss, s.Blind) →
    play ss ds back { m with opened := o } =
      (play ss ds back m).map fun y => (y.1, { y.2 with opened := o })
  | [], [], _, m, o, _ => by
    rw [play, play]
    rfl
  | s :: ss, d :: ds, back, m, o, hb => by
    rw [play, play, tell_field (hb s List.mem_cons_self)]
    cases s.tell back.head? m with
    | error e => rfl
    | ok x =>
      show (s.hear x d { m with opened := o }).bind _ = Except.map _ ((s.hear x d m).bind _)
      rw [hear_field]
      cases s.hear x d m with
      | error e => rfl
      | ok m' =>
        show (play ss ds back.tail { m' with opened := o }).map _ =
          Except.map _ ((play ss ds back.tail m').map _)
        rw [play_field ss ds back.tail m' o fun t ht => hb t (List.mem_cons_of_mem _ ht)]
        cases play ss ds back.tail m' <;> rfl
  | [], _ :: _, _, _, _, _ => by simp [play, Except.map]
  | _ :: _, [], _, _, _, _ => by simp [play, Except.map]

/-! ## 3 The walk -/

/-- Where `ChainProgress.settle` returns with the run still played, it has changed nothing of the prover's
state but the field. -/
theorem settle_same (L : Lay) : ∀ (bs : List (Block S Cl)) (z z' : ChainProgress S Cl W Y) (m' : Mid W Y),
    ChainProgress.settle L bs z = .ok z' → z'.mid = some m' →
    ∃ m o, z.mid = some m ∧ m' = { m with opened := o }
  | [], z, z', m', h, h1 => by
    rw [ChainProgress.settle] at h
    obtain rfl := Except.ok.inj h
    exact ⟨m', m'.opened, h1, rfl⟩
  | b :: bs, z, z', m', h, h1 => by
    rw [ChainProgress.settle] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨m', m'.opened, h1, rfl⟩
    · obtain ⟨cols, -, h⟩ := of_bind_ok h
      obtain ⟨m₁, o, hm, rfl⟩ := settle_same L bs _ z' m' h h1
      cases hzm : z.mid with
      | none => simp [hzm] at hm
      | some m₀ =>
        split at hm
        · rw [hzm] at hm
          obtain rfl : m₀.took cols = m₁ := Option.some.inj hm
          exact ⟨m₀, o, rfl, rfl⟩
        · cases hm

/-- **Where a walk over blind steps ends with the run still played, `play` from its first state
returns, and the two last states agree but for the field.** -/
theorem walk_play (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (m' : Mid W Y), (∀ s ∈ ss, s.Blind) → walk L ss ds z = .ok z' →
    z'.mid = some m' →
    ∃ m₀ y, z.mid = some m₀ ∧ play ss ds [] m₀ = .ok y ∧ m' = { y.2 with opened := m'.opened }
  | [], [], z, z', m', _, h, h1 => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact ⟨m', ([], m'), h1, by rw [play], rfl⟩
  | s :: ss, d :: ds, z, z', m', hb, h, h1 => by
    rw [walk] at h
    obtain ⟨x, hx, h⟩ := of_bind_ok h
    obtain ⟨z₁, hz₁, h⟩ := of_bind_ok h
    obtain ⟨m₁', y', e1, hp, e'⟩ :=
      walk_play L ss ds z₁ z' m' (fun t ht => hb t (List.mem_cons_of_mem _ ht)) h h1
    unfold ChainProgress.heard at hz₁
    obtain ⟨mm, hmm, hz₁⟩ := of_bind_ok hz₁
    obtain ⟨m₁, o₁, e2, rfl⟩ := settle_same L _ _ z₁ m₁' hz₁ e1
    have e3 : mm = some m₁ := e2
    subst e3
    cases hzm : z.mid with
    | none =>
      rw [hzm] at hmm
      cases hmm
    | some m₀ =>
      rw [hzm] at hmm
      obtain ⟨m₂, hh, e⟩ := map_ok hmm
      obtain rfl := Option.some.inj e
      have hx' : s.tell none m₀ = .ok x := by
        unfold ChainProgress.say at hx
        rw [hzm] at hx
        exact hx
      rw [play_field ss ds [] m₂ o₁ fun t ht => hb t (List.mem_cons_of_mem _ ht)] at hp
      obtain ⟨y, hy, rfl⟩ := map_ok hp
      refine ⟨m₀, (⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals,
        x.tables, d⟩ :: y.1, y.2), rfl, ?_, e'⟩
      rw [play]
      show (s.tell none m₀).bind _ = _
      rw [hx']
      show (s.hear x d m₀).bind _ = _
      rw [hh]
      show (play ss ds [] m₂).map _ = _
      rw [hy]
      rfl
  | [], _ :: _, _, _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, _, h, _ => by simp [walk] at h

/-! ## 4 Before an address, in one chain -/

/-- The state before the part at an address: by the walk and by `play`. `hb`: the steps before the
address are blind. `h`: `midInW` returns a state there. `play` is taken with no stored run to fall
back on. -/
theorem midInW_midIn {L : Lay} {steps : List (Step W Y)} {ds : List Fmt.Drawn}
    {z : ChainProgress S Cl W Y} {a : Addr} {m' : Mid W Y}
    (hb : ∀ s ∈ steps.take (steps.takeWhile fun s => s.addr != a).length, s.Blind)
    (h : midInW L steps ds z a = .ok (some m')) :
    ∃ m₀ m, z.mid = some m₀ ∧ midIn steps ds [] m₀ a = .ok m ∧
      m' = { m with opened := m'.opened } := by
  unfold midInW at h
  split at h
  · cases h
  · rename_i hany
    obtain ⟨z', hw, e⟩ := map_ok h
    obtain ⟨m₀, y, e0, hp, e'⟩ := walk_play L _ _ z z' m' hb hw e
    refine ⟨m₀, y.2, e0, ?_, e'⟩
    unfold midIn
    rw [if_neg hany]
    show (play _ _ [] m₀).map _ = _
    rw [hp]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.tell_field
#print axioms ProofFile.Honest.hear_field
#print axioms ProofFile.Honest.play_field
#print axioms ProofFile.Honest.settle_same
#print axioms ProofFile.Honest.walk_play
#print axioms ProofFile.Honest.midInW_midIn
