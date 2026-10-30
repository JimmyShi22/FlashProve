-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawSeated.lean: A BLOCK AS IT IS LAID INTO A CHAIN, WITH A REFUSAL AT A MARKED
RECORD BEHIND ITS DECISION: ITS STEP AGAINST THE BARE BLOCK'S; AND THE SMALLNESS TEST'S FIRST HALF'S
LAW OF THE STEP AT SUCH A BLOCK.

A law on a block speaks of one term. Whoever lays the block into a chain's list may lay another: the
block with a guard behind its decision: where the record that the decision returns bears a mark
(`S.failed`), the guarded block refuses. A law on the bare block's step then speaks of a step that
nothing calls. Here the two are tied, for every block at the first chain's carried record:
  `Guards c b`: c has the declared rounds of b, and its decision is b's followed by the refusal at a
    mark. Nothing is asked of the other fields (the name, the place, the test on the plan).
  `Seats c b`: THE SAME WITHOUT THE REFUSAL'S WORDS: c has the declared rounds of b, and a yes of c
    is a yes of b with the same record and no mark behind it, both ways. `Guards.seats`. A SEAT MAY
    LAY FURTHER GUARDS (one on the reply): then `Guards` does not hold by `rfl`, and may not hold at
    all; `Seats` holds wherever the further guards never bite; `Block.Under`
    (Johnson/Desc/Sound/HearsOnce.lean: a yes of c is the same yes of b) holds always.
  `Seats.under`, `Guards.under`, `lays_of_under`, `andThen_under`: for laws of the form "wherever
    the decision goes on": they pass along `Under`, also through a joint of two blocks.
  `step_seats`, `step_guards`: **the step of c goes on, to (s', k), if and only if the step of b
    does and s' bears no mark.**
  `Guards.yes`, `Guards.leaves`, `Guards.lays`: a yes of c is a yes of b with the same record: so
    every law of the form "wherever the decision goes on" passes from b to c.
  `hear_mark`: the block of the draw lays no mark and takes none off.
  `step_seats_iff`, `step_seated_iff`: **the law of the step at the carried record, of ANY c with
    `Seats c (approximateRangeProofDrawKind atS p)`, or with `Guards`**: c.step says yes if and only if there is one round,
    the frame's test on it passes, `MeansAtS` holds, no column is taken, AND THE RECORD IN FRONT
    BEARS NO MARK.
Statements and proofs.
Limits. That a given seat lays a block with `Guards` or `Seats` is to be seen at that seat's text.
`Guards` SPELLS THE REFUSAL'S WORDS: it holds by `rfl` only where the guard is written just so.
`Block.step` reads a block's rounds and decision alone (Johnson/Desc/Block.lean): what a chain's
other tests read of a block (its place, `before`, `oracles`, `planOk`) is not spoken of.

-/
import Johnson.Desc.First.K8.LawRowsStep
import Johnson.Desc.Sound.FoldHeard
import Johnson.Desc.Sound.HearsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- c is b with a refusal at a marked record behind its decision. -/
def Guards {Cl : Type} (c b : Block S Cl) : Prop :=
  c.rounds = b.rounds ∧ ∀ s rs gs, c.decide s rs gs =
    (b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)

/-- A yes of the guarded decision. -/
theorem decide_guards {Cl : Type} {c b : Block S Cl} (h : Guards c b) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    c.decide s rs gs = .ok s' ↔ b.decide s rs gs = .ok s' ∧ s'.failed = none := by
  rw [h.2]
  cases hb : b.decide s rs gs with
  | error e => simp [Except.bind]
  | ok t =>
    simp only [Except.bind]
    cases hf : t.failed with
    | none =>
      constructor
      · intro e
        obtain rfl : t = s' := Except.ok.inj e
        exact ⟨rfl, hf⟩
      · rintro ⟨e, _⟩
        exact e
    | some m =>
      constructor
      · intro e
        exact nomatch e
      · rintro ⟨e, e'⟩
        obtain rfl : t = s' := Except.ok.inj e
        rw [hf] at e'
        exact nomatch e'

/-- A yes of the guarded block is a yes of the bare one, with the same record. -/
theorem Guards.yes {Cl : Type} {c b : Block S Cl} (h : Guards c b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : c.decide s rs gs = .ok s') :
    b.decide s rs gs = .ok s' := ((decide_guards h s s' rs gs).1 hd).1

theorem Guards.leaves {Cl α : Type} {c b : Block S Cl} (h : Guards c b) {f : S → α}
    (hl : b.Leaves f) : c.Leaves f := fun s rs gs s' hd => hl s rs gs s' (h.yes hd)

theorem Guards.lays {Cl α : Type} {c b : Block S Cl} (h : Guards c b) {f : S → α}
    {rd : List Fmt.RoundView → α} (hl : b.Lays f rd) : c.Lays f rd :=
  fun s rs gs s' hd => hl s rs gs s' (h.yes hd)

/-- **The same without the refusal's words**: c has the declared rounds of b, and a yes of c is a
yes of b, with the same record, behind which no mark stands: both ways. -/
def Seats {Cl : Type} (c b : Block S Cl) : Prop :=
  c.rounds = b.rounds ∧ ∀ s rs gs t, c.decide s rs gs = .ok t ↔
    b.decide s rs gs = .ok t ∧ t.failed = none

theorem Guards.seats {Cl : Type} {c b : Block S Cl} (h : Guards c b) : Seats c b :=
  ⟨h.1, fun s rs gs t => decide_guards h s t rs gs⟩

/-- A yes of c is the same yes of b. -/
theorem Seats.under {Cl : Type} {c b : Block S Cl} (h : Seats c b) : c.Under b :=
  fun s rs gs t hd => ((h.2 s rs gs t).1 hd).1

theorem Guards.under {Cl : Type} {c b : Block S Cl} (h : Guards c b) : c.Under b := h.seats.under

/-- What a block lays, a block under it lays. -/
theorem lays_of_under {Cl Cl' α : Type} {c : Block S Cl'} {b : Block S Cl} (u : c.Under b)
    {f : S → α} {rd : List Fmt.RoundView → α} (hl : b.Lays f rd) : c.Lays f rd :=
  fun s rs gs s' hd => hl s rs gs s' (u s rs gs s' hd)

/-- Two blocks joined, each under another with the first one's rounds: the joint is under the other
joint, whatever the names. -/
theorem andThen_under {Cl : Type} {p' p q' q : Block S Cl} (hr : p'.rounds = p.rounds)
    (up : p'.Under p) (uq : q'.Under q) (n' n : String) :
    (Block.andThen n' p' q').Under (Block.andThen n p q) := by
  intro s rs gs t H
  have ho : p'.openings = p.openings := by
    unfold Block.openings
    rw [hr]
  obtain ⟨t1, h1, H⟩ :=
    bindOk (x := p'.decide s (rs.take p'.rounds.length) (gs.take p'.openings)) H
  rw [hr, ho] at h1 H
  show (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind _ = .ok t
  rw [up _ _ _ _ h1]
  exact uq _ _ _ _ H

/-- **The step of such a block against the bare block's.** -/
theorem step_seats {Cl : Type} {c b : Block S Cl} (h : Seats c b) (ft : Nat) (s s' : S)
    (k : Nat) (rs : List Fmt.RoundView) (cols : List Col) :
    c.step ft s rs cols = .ok (s', k) ↔ b.step ft s rs cols = .ok (s', k) ∧ s'.failed = none := by
  unfold Block.step
  rw [h.1]
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · simp
  · split
    · simp
    · generalize regroup _ _ = gs
      cases hc : c.decide s (rs.map noDigest) gs with
      | error e =>
        cases hb : b.decide s (rs.map noDigest) gs with
        | error e' => simp
        | ok u =>
          simp only [Except.ok.injEq, Prod.mk.injEq, false_iff, reduceCtorEq]
          rintro ⟨⟨rfl, -⟩, hq⟩
          rw [(h.2 s _ gs u).2 ⟨hb, hq⟩] at hc
          cases hc
      | ok u =>
        obtain ⟨h1, h2⟩ := (h.2 s _ gs u).1 hc
        rw [h1]
        simp only [Except.ok.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, hk⟩
          exact ⟨⟨rfl, hk⟩, h2⟩
        · rintro ⟨hk, -⟩
          exact hk

/-- **The step of the guarded block against the bare block's.** -/
theorem step_guards {Cl : Type} {c b : Block S Cl} (h : Guards c b) (ft : Nat) (s s' : S)
    (k : Nat) (rs : List Fmt.RoundView) (cols : List Col) :
    c.step ft s rs cols = .ok (s', k) ↔ b.step ft s rs cols = .ok (s', k) ∧ s'.failed = none :=
  step_seats h.seats ft s s' k rs cols

/-- The block of the draw lays no mark and takes none off. -/
theorem hear_mark (p : Par) (s s' : S) (r : Fmt.RoundView) (h : MeansAtS p s r s') :
    s'.failed = s.failed := by
  obtain ⟨tl, _, _, _, _, _, _, _, _, _, e⟩ := h
  rw [e]
  exact (putTl_rest s _).2.2.2.2.1

/-- **The law of the step at the carried record, of the block as it is laid into a chain.** -/
theorem step_seats_iff {Cl : Type} (p : Par) (c : Block S Cl) (h : Seats c (approximateRangeProofDrawKind atS p))
    (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List Col) :
    c.step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ roundsFit [round p] [r] = true ∧ MeansAtS p st r st' ∧ n = 0 ∧
        st.failed = none := by
  rw [step_seats h, step_atS_iff]
  constructor
  · rintro ⟨⟨r, e, hf, hm, hn⟩, hk⟩
    exact ⟨r, e, hf, hm, hn, (hear_mark p st st' r hm) ▸ hk⟩
  · rintro ⟨r, e, hf, hm, hn, hk⟩
    exact ⟨⟨r, e, hf, hm, hn⟩, (hear_mark p st st' r hm).trans hk⟩

theorem step_seated_iff {Cl : Type} (p : Par) (c : Block S Cl) (h : Guards c (approximateRangeProofDrawKind atS p))
    (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List Col) :
    c.step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ roundsFit [round p] [r] = true ∧ MeansAtS p st r st' ∧ n = 0 ∧
        st.failed = none := step_seats_iff p c h.seats ft st st' n rs cols

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.decide_guards
#print axioms VerifiableInference.Desc.First.K8.Guards.leaves
#print axioms VerifiableInference.Desc.First.K8.andThen_under
#print axioms VerifiableInference.Desc.First.K8.step_seats
#print axioms VerifiableInference.Desc.First.K8.step_guards
#print axioms VerifiableInference.Desc.First.K8.step_seats_iff
#print axioms VerifiableInference.Desc.First.K8.hear_mark
#print axioms VerifiableInference.Desc.First.K8.step_seated_iff
