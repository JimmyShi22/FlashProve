-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/JoinedAt.lean: two turns of
Johnson/Desc/Sound/JoinedSteps.lean and StepsThrough.lean, laid BESIDE them (no statement there
turns). Theorems with their proofs. General in the record, the types of claims and the order R.

(1) A MEMBER OF A REAL FLAT LIST IS SELDOM THE TERM ITSELF: a fold lays a guard around each place's
block (it refuses where the block has left a mark) and writes a name and a place in. Such a member's
decision is NOT the block's; but every yes of it is a yes of the block, at the same record, rounds
and groups.
  `YesOf B' B`: just that. `YesOf.refl`, `YesOf.trans`, `yesOfDecide` (equal decisions),
    `yesOfBind` (a test laid behind the decision that hands the record on as it came).
  `stepsOfYes`, `callsWithOfYes`, `callsAtOfYes`: the three laws go from B to B'.
(2) `KeptQ` FORGOT WHERE. `KeptAt R front B Q`, of the one block's records s, s', rounds rs: there
are m, m': `front` (all that is joined in front of the gathering step B), AT s AND AT ITS OWN CUT OF
rs, says yes and leaves m; B says yes at m and leaves m'; Q holds of B's own call AT m AND m'; and
R m' s'. THE GROUPS OF OPENED COLUMNS STAY UNDER "THERE ARE" (`CallsWith` hands Q none): `front`
is asked at SOME groups, cut to its own number `front.openings`. So m is pinned by s and rs alone
JUST WHERE `front` OPENS NOTHING (`keptAtQuiet`: the groups are [] there); elsewhere it is a yes of
`front` at s and its cut of rs, at groups that this statement does not name.
  `roundsAndThen`: what is joined behind cuts no round off the front.
  **`callsAndThenAllAt`**: one step of the row gathers, the others step: the one block calls the
    gatherer, with `KeptAt`.
  `keptOfAt`: `KeptAt` gives `KeptQ`.

Limits. Frame's laws: no error, nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.JoinedSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl Cl' : Type}

/-! ## (1) A member whose yes is the block's yes -/

/-- Every yes of B' is a yes of B, at the same record, rounds and groups, with the same record
behind. -/
def YesOf (B' B : Block S Cl) : Prop :=
  ∀ s rs gs s', B'.decide s rs gs = .ok s' → B.decide s rs gs = .ok s'

theorem YesOf.refl (B : Block S Cl) : YesOf B B := fun _ _ _ _ h => h

theorem YesOf.trans {A B C : Block S Cl} (h : YesOf A B) (h' : YesOf B C) : YesOf A C :=
  fun s rs gs s' H => h' s rs gs s' (h s rs gs s' H)

theorem yesOfDecide (B B' : Block S Cl) (e : B'.decide = B.decide) : YesOf B' B :=
  fun _ _ _ _ H => e ▸ H

/-- A test laid behind the decision, which hands the record on as it came or refuses. -/
theorem yesOfBind (B B' : Block S Cl) (g : S → Except String S) (hg : ∀ t t', g t = .ok t' → t' = t)
    (e : ∀ s rs gs, B'.decide s rs gs = (B.decide s rs gs).bind g) : YesOf B' B := by
  intro s rs gs s' H
  rw [e] at H
  obtain ⟨t, ht, H⟩ := bindOk (x := B.decide s rs gs) H
  rw [ht, hg t s' H]

theorem stepsOfYes {R : S → S → Prop} (B B' : Block S Cl) (e : YesOf B' B) (h : B.Steps R) :
    B'.Steps R :=
  fun s rs gs s' H => h s rs gs s' (e s rs gs s' H)

theorem callsWithOfYes {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (B B' : Block S Cl) (f : S → Except String (List Cl' × S)) (e : YesOf B' B)
    (h : CallsWith R Q B f) : CallsWith R Q B' f :=
  fun s rs gs s' H => h s rs gs s' (e s rs gs s' H)

theorem callsAtOfYes {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (B B' : Block S Cl) (f : S → Except String (List Cl × S)) (e : YesOf B' B)
    (h : CallsAt R Q B f) : CallsAt R Q B' f :=
  fun s rs gs s' H => h s rs gs s' (e s rs gs s' H)

/-! ## (2) Q, kept WITH ITS PLACE -/

/-- Q of the gathering step's own call, with where that step stood inside the one block. -/
def KeptAt (R : S → S → Prop) (front B : Block S Cl)
    (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop) :
    S → List Fmt.RoundView → S → List Cl' → S → S → Prop :=
  fun s rs t cls e s' => ∃ (gs : List (List (Nat × List UInt64))) (m : S) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))) (m' : S),
    front.decide s (rs.take front.rounds.length) (gs.take front.openings) = .ok m ∧
      B.decide m rs' gs' = .ok m' ∧ Q m rs' t cls e m' ∧ R m' s'

theorem keptOfAt {R : S → S → Prop} {front B : Block S Cl}
    {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop} {s : S} {rs : List Fmt.RoundView} {t : S}
    {cls : List Cl'} {e s' : S} (h : KeptAt R front B Q s rs t cls e s') :
    KeptQ Q s rs t cls e s' := by
  obtain ⟨_, m, rs', _, m', _, _, hQ, _⟩ := h
  exact ⟨m, rs', m', hQ⟩

/-- Where `front` opens nothing its groups are none: m is what `front` leaves at s, its cut of rs
and no group. -/
theorem keptAtQuiet {R : S → S → Prop} {front B : Block S Cl}
    {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop} {s : S} {rs : List Fmt.RoundView} {t : S}
    {cls : List Cl'} {e s' : S} (h0 : front.openings = 0) (h : KeptAt R front B Q s rs t cls e s') :
    ∃ m rs' gs' m', front.decide s (rs.take front.rounds.length) [] = .ok m ∧
      B.decide m rs' gs' = .ok m' ∧ Q m rs' t cls e m' ∧ R m' s' := by
  obtain ⟨gs, m, rs', gs', m', hf, hB, hQ, hm⟩ := h
  rw [h0, List.take_zero] at hf
  exact ⟨m, rs', gs', m', hf, hB, hQ, hm⟩

theorem roundsAndThen (name : String) (p q : Block S Cl) :
    p.rounds.length ≤ (p.andThen name q).rounds.length := by
  show p.rounds.length ≤ (p.rounds ++ q.rounds).length
  rw [List.length_append]
  exact Nat.le_add_right _ _

theorem callsAtRight {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : p.Steps R) (hq : CallsWith R Q q f) :
    CallsWith R (KeptAt R p q Q) (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, h₄⟩ := hq _ _ _ _ H'
  exact ⟨t, cls, e, hR.trans _ _ _ (hp _ _ _ _ hm) h₁, h₂, h₃, gs, m, _, _, s', hm, H', h₄,
    hR.refl _⟩

/-- On, behind: the pins stand, since what is joined behind cuts no round off the front. -/
theorem callsAtOn {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (front B p q : Block S Cl)
    (f : S → Except String (List Cl' × S)) (hr : front.rounds.length ≤ p.rounds.length)
    (hp : CallsWith R (KeptAt R front B Q) p f) (hq : q.Steps R) :
    CallsWith R (KeptAt R front B Q) (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m₁, hm₁, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, gs₀, m, rs', gs', m', hf, hB, hQ, hm⟩ := hp _ _ _ _ hm₁
  rw [List.take_take, Nat.min_eq_left hr] at hf
  exact ⟨t, cls, e, h₁, h₂, hR.trans _ _ _ h₃ (hq _ _ _ _ H'), gs₀, m, rs', gs', m', hf, hB, hQ,
    hR.trans _ _ _ hm (hq _ _ _ _ H')⟩

theorem callsAtAll {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (front B : Block S Cl) (f : S → Except String (List Cl' × S)) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl), front.rounds.length ≤ b.rounds.length →
      CallsWith R (KeptAt R front B Q) b f →
      (∀ x ∈ l, x.Steps R) → CallsWith R (KeptAt R front B Q) (andThenAll name b l) f
  | [], _, _, hb, _ => hb
  | x :: l, b, hr, hb, hl =>
    callsAtAll hR name front B f l (b.andThen name x) (Nat.le_trans hr (roundsAndThen name b x))
      (callsAtOn hR name front B b x f hr hb (hl x List.mem_cons_self))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- **One step of the row gathers; the others step: the one block calls the gatherer, and what the
step said of its call is kept WITH ITS PLACE.** -/
theorem callsAndThenAllAt {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (f : S → Except String (List Cl' × S)) (b B : Block S Cl)
    (l₁ l₂ : List (Block S Cl)) (hb : b.Steps R) (h₁ : ∀ x ∈ l₁, x.Steps R)
    (hB : CallsWith R Q B f) (h₂ : ∀ x ∈ l₂, x.Steps R) :
    CallsWith R (KeptAt R (andThenAll name b l₁) B Q) (andThenAll name b (l₁ ++ B :: l₂)) f := by
  rw [andThenAllApp]
  exact callsAtAll hR name _ B f l₂ _ (roundsAndThen name _ B)
    (callsAtRight hR name _ B f (stepsAndThenAll hR name l₁ b hb h₁) hB) h₂

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.yesOfBind
#print axioms VerifiableInference.Desc.stepsOfYes
#print axioms VerifiableInference.Desc.callsWithOfYes
#print axioms VerifiableInference.Desc.callsAtOfYes
#print axioms VerifiableInference.Desc.keptAtQuiet
#print axioms VerifiableInference.Desc.callsAtOn
#print axioms VerifiableInference.Desc.callsAndThenAllAt
