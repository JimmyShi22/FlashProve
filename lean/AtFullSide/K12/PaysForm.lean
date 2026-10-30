-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysForm.lean: how a prover's side pays (SidePays, Honest/Law/ReadyOfSides.lean) when
it is the pair of a proximity test: the tests that chainSteps asks at one block, stated once, and
what carries them. General in the book, the job and the description.

  SideFits              the five tests of chainSteps at a side and its block, and the lending at
                        every run's coins
  sidePays_of_fits      such a side pays
  SideFits.guarded      so does the side behind the guard (K12/FieldGuard.lean)
  lends_of_fits         the lending alone, where a block stands at the side's place
  fits_of_pair          a pair fits where the book cuts it, has no row or entry beyond its two parts
                        and lends it
  fits_of_laysB         so at laysB (K12/StepsReturn.lean), in the first and the shared chain
  fits_of_laysLastB     so at laysLastB (K12/StepsReturnLast.lean), in the last chain
  fits_at_numbers, fits_at_numbers_last   the same at a job whose parameters are a given record
  alike_member, rounds_of_alike   a block of a description that is alike to another stands beside a
                        block with its place and its rounds

By what. chainSteps_side (Law/ReadyOfParts.lean); lendRow_placed, needsField_rounds, needsField_cut,
needsField_parts_length (K12/FieldGuardLift.lean); lendRow_ok, look_due (E2E/KeyBookLends.lean);
first_moves, rest_moves (K12/HalfSteps.lean); due_seen (K12/StepsReturnLast.lean). These laws do not
ask SeatOf: a block enters by its place, its rounds and its oracle messages alone, and the block's
decision is not read. So nothing here says that a block seats a test.

Limits.
- Every law here is an implication; none is called at a book or a job in this file.
- SideFits holds vacuously at a list with no block at the side's place. A caller who needs a block
  there has it from the description.
- That a side pays says that chainSteps returns, at every view and every run's coins. It says
  nothing on whether a part plays or a round is accepted.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K12.StepsReturnLast
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift
import Johnson.AtFull.ProofPlan.PlanAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Place Alike₂)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest hiding look_due
open ProofFile.Honest.K12
open AtPublicFiles.KeyBook (Within lendRow_ok look_due seen)
open ProofFile.Honest.Small (placed_rounds)

variable {S Cl S' Cl' V W X : Type}

/-! ## 1 The form -/

/-- **What chainSteps asks of a side at each block at its place**: the block has as many lists of
oracle messages as rounds; the side has that many rounds; the book cuts it so; no row or entry names
a part beyond its own; and the book lends it, at every run's coins. -/
def SideFits (B : ProverCoinCounts) (ch : Nat) (bs : List (Block S Cl)) (g : Placed V W X) : Prop :=
  ∀ b ∈ bs, b.place = g.place →
    b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length ∧
    B.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
    (B.rowsOf ch).any
      (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false ∧
    B.ahead.any
      (fun e => e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = false ∧
    ∀ k : Coins B, ∃ c, lendRow B (B.rowsOf ch) (k.look ch) b.place g.parts 0 = .ok c

/-- **A side that fits pays.** -/
theorem sidePays_of_fits {B : ProverCoinCounts} {ch : Nat} {bs : List (Block S Cl)} {g : Placed V W X}
    (h : SideFits B ch bs g) : SidePays B ch bs g := by
  intro b hb hp hs hf v k
  obtain ⟨ho, hr, hc, h1, h2, hl⟩ := h b hb hp
  obtain ⟨c, hc'⟩ := hl k
  exact ⟨_, chainSteps_side B _ _ v b hs g hf ho hr hc h1 h2 c hc'⟩

/-- **A side that fits fits behind the guard**: the guard keeps what a part states and how many
moves it has. -/
theorem SideFits.guarded {B : ProverCoinCounts} {ch : Nat} {bs : List (Block S Cl)} {g : Placed V W X}
    (h : SideFits B ch bs g) : SideFits B ch bs g.needsField := by
  intro b hb hp
  obtain ⟨ho, hr, hc, h1, h2, hl⟩ := h b hb hp
  refine ⟨ho, ?_, ?_, ?_, ?_, fun k => ?_⟩
  · rw [needsField_rounds]
    exact hr
  · rw [needsField_cut]
    exact hc
  · rw [needsField_parts_length]
    exact h1
  · rw [needsField_parts_length]
    exact h2
  · obtain ⟨c, hc'⟩ := hl k
    refine ⟨guardCoins g.parts c, ?_⟩
    rw [lendRow_placed, hc'] <;> rfl

/-- **A side that fits is lent**, where a block of the list stands at its place. -/
theorem lends_of_fits {B : ProverCoinCounts} {ch : Nat} {bs : List (Block S Cl)} {g : Placed V W X}
    (h : SideFits B ch bs g) (hin : g.place ∈ bs.map (·.place)) (k : Coins B) :
    ∃ c, lendRow B (B.rowsOf ch) (k.look ch) g.place g.parts 0 = .ok c := by
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hin
  have q := (h b hb e).2.2.2.2.2 k
  rw [e] at q
  exact q

/-! ## 2 A proximity test's pair -/

/-- Two stages or more, as a list's first two. -/
theorem stages_two {l : List Fmt.M1.Stage} (h : 2 ≤ l.length) :
    ∃ s t rest, l = s :: t :: rest := by
  cases l with
  | nil => exact absurd h (by decide)
  | cons s l =>
    cases l with
    | nil => exact absurd h (by simp)
    | cons t rest => exact ⟨s, t, rest, rfl⟩

/-- **The pair fits** where each block at its place has the pair's rounds, the book cuts it so, has
no row or entry beyond its two parts, and lends it at every run's coins. -/
theorem fits_of_pair {bs : List (Block S Cl)} (B : ProverCoinCounts) (ch : Nat) (J : TestJob W X)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hcut : B.cuts.lookup J.p.place =
      some [firstLen J.p.nums.stages, restLen J.p.nums.stages])
    (hrow : (B.rowsOf ch).any
      (fun r => r.1.place == J.p.place && decide (2 ≤ r.1.part)) = false)
    (hent : B.ahead.any
      (fun e => e.spender.place == J.p.place && decide (2 ≤ e.spender.part)) = false)
    (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hr : ∀ b ∈ bs, b.place = J.p.place →
      b.rounds.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (hl : ∀ k : Coins B, ∃ c, lendRow B (B.rowsOf ch) (k.look ch) J.p.place
      (proverSideOfProximityTest J : Placed V W X).parts 0 = .ok c) :
    SideFits B ch bs (proverSideOfProximityTest J : Placed V W X) := by
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  intro b hb hp
  have hp' : b.place = J.p.place := hp
  refine ⟨ho b hb, ?_, ?_, ?_, ?_, fun k => ?_⟩
  · rw [placed_rounds, hr b hb hp']
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  · rw [hp', hcut]
    show some [_, _] = some [(firstPart J : Part V W X).moves.length,
      (restPart J : Part V W X).moves.length]
    rw [l1, l2]
  · rw [hp']
    exact hrow
  · rw [hp']
    exact hent
  · rw [hp']
    exact hl k

/-- **At laysB the pair fits**, in the first and the shared chain. -/
theorem fits_of_laysB {bs : List (Block S Cl)} (B : ProverCoinCounts) (ch : Nat) (hch : ch = 0 ∨ ch = 1)
    (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hB : laysB B ch J = true)
    (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hr : ∀ b ∈ bs, b.place = J.p.place →
      b.rounds.length = firstLen J.p.nums.stages + restLen J.p.nums.stages) :
    SideFits B ch bs (proverSideOfProximityTest J : Placed V W X) := by
  unfold laysB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := hB
  have hseen : seen B ch = B.rowsOf ch := by
    rcases hch with rfl | rfl <;> rfl
  refine fits_of_pair B ch J s t rest hst a3 a4 a5 ho hr fun k => ?_
  obtain ⟨c, hc⟩ := lendRow_ok B (B.rowsOf ch) (k.look ch) J.p.place
    (fun j => by
      rw [look_due, hseen]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hp => by
      have q := a8 e he
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [look_due, hseen]
      exact q)
    [(firstPart J : Part V W X), restPart J] 0 (fun i p hp => by
      match i, hp with
      | 0, hp =>
        obtain rfl := Option.some.inj hp
        exact (first_states J).trans a6
      | 1, hp =>
        obtain rfl := Option.some.inj hp
        exact a7)
  exact ⟨c, hc⟩

/-- **At laysLastB the pair fits**, in the last chain. -/
theorem fits_of_laysLastB {bs : List (Block S Cl)} (B : ProverCoinCounts) (J : TestJob W X)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hB : laysLastB B J = true) (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hr : ∀ b ∈ bs, b.place = J.p.place →
      b.rounds.length = firstLen J.p.nums.stages + restLen J.p.nums.stages) :
    SideFits B 2 bs (proverSideOfProximityTest J : Placed V W X) := by
  unfold laysLastB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hB
  refine fits_of_pair B 2 J s t rest hst a3 a4 a5 ho hr fun k => ?_
  obtain ⟨c, hc⟩ := lendRow_ok B (B.rowsOf 2) (k.look 2) J.p.place
    (fun j => by
      rw [look_due, due_seen B ⟨J.p.place, j⟩ a9 a10]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hp => by
      have q := a8 e he
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [look_due]
      exact q)
    [(firstPart J : Part V W X), restPart J] 0 (fun i p hp => by
      match i, hp with
      | 0, hp =>
        obtain rfl := Option.some.inj hp
        exact (first_states J).trans a6
      | 1, hp =>
        obtain rfl := Option.some.inj hp
        exact a7)
  exact ⟨c, hc⟩

/-- The same as fits_of_laysB, at a job whose parameters are the record q. -/
theorem fits_at_numbers {bs : List (Block S Cl)} (B : ProverCoinCounts) (ch : Nat) (hch : ch = 0 ∨ ch = 1)
    (J : TestJob W X) (q : P12) (hp : J.p = q) (two : 2 ≤ q.nums.stages.length)
    (hB : laysB B ch J = true) (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hr : ∀ b ∈ bs, b.place = q.place →
      b.rounds.length = firstLen q.nums.stages + restLen q.nums.stages) :
    SideFits B ch bs (proverSideOfProximityTest J : Placed V W X) := by
  subst hp
  obtain ⟨s, t, rest, e⟩ := stages_two two
  exact fits_of_laysB B ch hch J s t rest e hB ho hr

/-- The same as fits_of_laysLastB, at a job whose parameters are the record q. -/
theorem fits_at_numbers_last {bs : List (Block S Cl)} (B : ProverCoinCounts) (J : TestJob W X) (q : P12)
    (hp : J.p = q) (two : 2 ≤ q.nums.stages.length) (hB : laysLastB B J = true)
    (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hr : ∀ b ∈ bs, b.place = q.place →
      b.rounds.length = firstLen q.nums.stages + restLen q.nums.stages) :
    SideFits B 2 bs (proverSideOfProximityTest J : Placed V W X) := by
  subst hp
  obtain ⟨s, t, rest, e⟩ := stages_two two
  exact fits_of_laysLastB B J s t rest e hB ho hr

/-! ## 3 Blocks of a description alike to another -/

/-- **Each block of the second list stands beside a block of the first that is alike to it.** -/
theorem alike_member {l : List (Block S Cl)} {l' : List (Block S' Cl')}
    (h : List.Forall₂ Alike₂ l l') {b' : Block S' Cl'} (hb : b' ∈ l') :
    ∃ b ∈ l, Alike₂ b b' := by
  induction h with
  | nil => cases hb
  | @cons a a' l l' ha _ ih =>
    rcases List.mem_cons.1 hb with e | hb'
    · subst e
      exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨b, hb₁, hb₂⟩ := ih hb'
      exact ⟨b, List.mem_cons_of_mem _ hb₁, hb₂⟩

/-- **A count of rounds at a place, read off one list, holds of a list alike to it.** -/
theorem rounds_of_alike {l : List (Block S Cl)} {l' : List (Block S' Cl')}
    (h : List.Forall₂ Alike₂ l l') {a : Place} {n : Nat}
    (hw : (l.all fun b => !(b.place == a) || b.rounds.length == n) = true) :
    ∀ b ∈ l', b.place = a → b.rounds.length = n := by
  intro b hb hp
  obtain ⟨c, hc, hk⟩ := alike_member h hb
  have q : (!(c.place == a) || c.rounds.length == n) = true := List.all_eq_true.1 hw c hc
  rw [hk.1, hp] at q
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at q
  rw [← hk.2.1]
  exact q

end AtFullSide.K12

#print axioms AtFullSide.K12.SideFits
#print axioms AtFullSide.K12.sidePays_of_fits
#print axioms AtFullSide.K12.SideFits.guarded
#print axioms AtFullSide.K12.lends_of_fits
#print axioms AtFullSide.K12.stages_two
#print axioms AtFullSide.K12.fits_of_pair
#print axioms AtFullSide.K12.fits_of_laysB
#print axioms AtFullSide.K12.fits_of_laysLastB
#print axioms AtFullSide.K12.fits_at_numbers
#print axioms AtFullSide.K12.fits_at_numbers_last
#print axioms AtFullSide.K12.alike_member
#print axioms AtFullSide.K12.rounds_of_alike
