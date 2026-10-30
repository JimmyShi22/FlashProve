-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Join.lean: THE JOIN OF TWO HALVES INTO THE WHOLE MEMBER.
Some members of the first chain's blocksInOrder list are two sub-protocols laid as one: W's place (K1's
sending, then K13's rows: the library's `Block.andThen`), and the 25 links' first hearing members (a
lot's sub-protocol, then the frame's «opened»: the library's `IM.Joined`, Johnson/IMR/SameSpot.lean;
its lemmas: Johnson/IMR/FirstSeats.lean). Each half has its own authors, who can say what a yes of
ITS half keeps. Here: a yes of the whole (the library's `StepYes`, Johnson/Top/H0/Walk/Reach.lean)
is a yes of the first half to some state between, and a yes of the second from there: so the two
halves' clauses hold in a row.

WHAT THIS IS. Lemmas on the library's definitions: over its `andThen_step`
(Johnson/Top/H0/StepLaws/StepLaws.lean), `step_ok_iff` (Johnson/Desc/Sound/RunIsDecide.lean),
`Joined.step`, `Joined.rounds`. General in the two sub-protocols and in the two clauses. None of the
library's goals.

  1  `step_counted`, `stepYes_andThen`, `keeps_andThen`
  2  `stepYes_joined`, `keeps_joined`

Limits. One way only: from a yes of the whole. Nothing says that a half's yes can be had. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place andThen_step)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-! ## 1 Two sub-protocols laid as one -/

section
variable {S Cl : Type}

/-- A step reads of its columns just those that it counts. -/
theorem step_counted (ft : Nat) (b : Block S Cl) (s t : S) (R : List Fmt.RoundView) (c : List OpenedColumn)
    (k : Nat) (h : b.step ft s R c = .ok (t, k)) : b.step ft s R (c.take k) = .ok (t, k) := by
  have h' := (step_ok_iff ft b s t R c k).1 h
  refine (step_ok_iff ft b s t R (c.take k) k).2 ?_
  rw [List.take_take, Nat.min_self]
  exact h'

/-- **A yes of the whole is a yes of the first half, and then one of the second.** -/
theorem stepYes_andThen (ft : Nat) (n : String) (b₁ b₂ : Block S Cl) (s s' : S)
    (h : StepYes ft (b₁.andThen n b₂) s s') : ∃ t, StepYes ft b₁ s t ∧ StepYes ft b₂ t s' := by
  obtain ⟨R, c, hR, e⟩ := h
  have hR' : R.length = b₁.rounds.length + b₂.rounds.length := by
    rw [hR]
    exact List.length_append
  obtain ⟨t, k1, k2, h1, h2, hk⟩ := (andThen_step n b₁ b₂ ft s s' R c c.length).1 e
  refine ⟨t, ⟨R.take b₁.rounds.length, c.take k1, ?_, ?_⟩,
    ⟨R.drop b₁.rounds.length, c.drop k1, ?_, ?_⟩⟩
  · rw [List.length_take]
    omega
  · rw [List.length_take, Nat.min_eq_left (by omega)]
    exact step_counted ft b₁ s t _ c k1 h1
  · rw [List.length_drop]
    omega
  · rw [List.length_drop, show c.length - k1 = k2 by omega]
    exact h2

/-- **THE TWO HALVES' CLAUSES HOLD IN A ROW.** -/
theorem keeps_andThen (ft : Nat) (n : String) (b₁ b₂ : Block S Cl) (C₁ C₂ : S → S → Prop)
    (h₁ : ∀ s t, StepYes ft b₁ s t → C₁ s t) (h₂ : ∀ t s', StepYes ft b₂ t s' → C₂ t s')
    (s s' : S) (h : StepYes ft (b₁.andThen n b₂) s s') : ∃ t, C₁ s t ∧ C₂ t s' := by
  obtain ⟨t, g1, g2⟩ := stepYes_andThen ft n b₁ b₂ s s' h
  exact ⟨t, h₁ s t g1, h₂ t s' g2⟩

end

/-! ## 2 A lot's sub-protocol with the frame's «opened» joined -/

open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **A yes of a link's first hearing member**: a yes of the lot's own sub-protocol, no mark behind
it; then the link's row's «opened» from that state on, no mark behind it, the reply as it was. -/
theorem stepYes_joined {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) {ft : Nat} {s s' : S} (h : StepYes ft b s s') :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
        (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ StepYes ft b' s m ∧ m.failed = none ∧ f.opened m = .ok s' ∧
      s'.failed = none ∧ ProofFile.sameReply m s' = true := by
  obtain ⟨R, c, hR, e⟩ := h
  obtain ⟨fs, f, m, g1, g2, g3, g4, g5, g6, g7⟩ := hj.step e
  exact ⟨fs, f, m, g1, g2, ⟨R, c, by rw [hR, hj.rounds], g3⟩, g4, g5, g6, g7⟩

/-- **THE LOT's AUTHORS' CLAUSE, THEN THE FRAME's.** C₂ is asked at whatever row of frames stands at
the link's number. -/
theorem keeps_joined {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) (ft : Nat) (C₁ C₂ : S → S → Prop)
    (h₁ : ∀ s m, StepYes ft b' s m → m.failed = none → C₁ s m)
    (h₂ : ∀ fs f m s',
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
      fs[l]? = some f → m.failed = none → f.opened m = .ok s' → s'.failed = none →
      ProofFile.sameReply m s' = true → C₂ m s')
    (s s' : S) (h : StepYes ft b s s') : ∃ m, C₁ s m ∧ C₂ m s' := by
  obtain ⟨fs, f, m, g1, g2, g3, g4, g5, g6, g7⟩ := stepYes_joined hj h
  exact ⟨m, h₁ s m g3 g4, h₂ fs f m s' g1 g2 g4 g5 g6 g7⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.step_counted
#print axioms ProofFile.Honest.stepYes_andThen
#print axioms ProofFile.Honest.keeps_andThen
#print axioms ProofFile.Honest.stepYes_joined
#print axioms ProofFile.Honest.keeps_joined
