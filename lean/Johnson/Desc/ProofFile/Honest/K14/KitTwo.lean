-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/KitTwo.lean: general lemmas on the frame's functions, beside
Honest/K14/Kit.lean: for a row of one part with TWO moves, and for a member that brings new trees.
No kind is named here.

  steps_two, two_plays   a row of one part with two moves and no stop, at a sub-protocol that
                  declares two rounds: its steps; it plays, where both moves return messages that
                  fit
  reads_none_two  two rounds that open no tree and read no committed table read nothing
  lendRow_own     what lendRow hands the one part of a row as its own coins: the first coins at the
                  part's address, as many as it takes
  fresh_mem_own   a source that is at hand behind a member of a thread and not in front of it is one
                  of the chain's own trees, numbered behind those in front
  add_own         the tree behind such a source, behind rounds as played: the table of that number
                  among the rounds' tables

What is not claimed. Nothing on any sub-protocol, on a verifier's decision, on soundness or on
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Kit
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type}

/-- The steps of a row of one part with two moves, at a sub-protocol that declares two rounds. -/
theorem steps_two (b : Block S Cl) (d₀ d₁ : Fmt.DeclaredRound)
    (o₀ o₁ : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d₀, o₀), (d₁, o₁)]) (p : Part V W X)
    (mv₀ mv₁ : Move p.Coins W X) (hm : p.moves = [mv₀, mv₁]) (v : Option V) (c : RowCoins [p]) :
    ({ place := b.place, parts := [p] } : Placed V W X).steps b v c =
      [{ name := b.name, addr := { place := b.place, part := 0 }, decl := d₀, oracles := o₀
         bad := p.bad, hid := fun f o => v.bind fun w => p.hid w f o, nth := 0, last := false
         move := some { say := fun _ => mv₀.say c.1, hand := mv₀.hand } },
       { name := b.name, addr := { place := b.place, part := 0 }, decl := d₁, oracles := o₁
         bad := p.bad, hid := fun f o => v.bind fun w => p.hid w f o, nth := 1, last := true
         move := some { say := fun _ => mv₁.say c.1, hand := mv₁.hand } }] := by
  simp [Placed.steps, rowSteps, Part.steps, hb, hm]

/-- **A row of one part with two moves and no stop plays**, where both moves return messages that
fit the declared rounds. -/
theorem two_plays (b : Block S Cl) (d₀ d₁ : Fmt.DeclaredRound)
    (o₀ o₁ : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d₀, o₀), (d₁, o₁)]) (p : Part V W X)
    (mv₀ mv₁ : Move p.Coins W X) (hm : p.moves = [mv₀, mv₁]) (hbad : ∀ f o, p.bad f o = none)
    (hhid : ∀ w f o, p.hid w f o = none) (v : Option V) (c : RowCoins [p]) (m : Mid W X)
    (x₀ x₁ : Fmt.Drawn) (z₀ z₁ : Sending) (hz₀ : mv₀.say c.1 m.shown m.st = .ok z₀)
    (hf₀ : z₀.fits d₀ o₀ = true)
    (hz₁ : mv₁.say c.1
      (m.after { say := fun _ => mv₀.say c.1, hand := mv₀.hand }
        (z₀.vals.map Said.got) x₀).shown
      (m.after { say := fun _ => mv₀.say c.1, hand := mv₀.hand } (z₀.vals.map Said.got) x₀).st =
        .ok z₁)
    (hf₁ : z₁.fits d₁ o₁ = true) :
    play (({ place := b.place, parts := [p] } : Placed V W X).steps b v c) [x₀, x₁] [] m =
      .ok ([playedBy b (z₀.vals.map Said.got) (z₀.tables.map some) x₀,
          playedBy b (z₁.vals.map Said.got) (z₁.tables.map some) x₁],
        (m.after { say := fun _ => mv₀.say c.1, hand := mv₀.hand } (z₀.vals.map Said.got) x₀).after
          { say := fun _ => mv₁.say c.1, hand := mv₁.hand } (z₁.vals.map Said.got) x₁) := by
  rw [steps_two b d₀ d₁ o₀ o₁ hb p mv₀ mv₁ hm v c]
  exact play_two (mv₀ := ⟨fun _ => mv₀.say c.1, mv₀.hand⟩)
    (mv₁ := ⟨fun _ => mv₁.say c.1, mv₁.hand⟩) hbad (fun f o => by cases v <;> simp [hhid]) rfl hz₀
    hf₀ hbad (fun f o => by cases v <;> simp [hhid]) rfl hz₁ hf₁

/-- Two rounds that open no tree and read no committed table read nothing. -/
theorem reads_none_two (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (d₀ d₁ : Fmt.DeclaredRound) (x₀ x₁ : Fmt.Drawn)
    (ho₀ : d₀.opens = []) (hs₀ : d₀.stored = []) (ho₁ : d₁.opens = []) (hs₁ : d₁.stored = []) :
    readsOf chain ft stored tree [d₀, d₁] [x₀, x₁] = [] := by
  simp [readsOf, ho₀, hs₀, ho₁, hs₁]

/-- What lendRow hands the one part of a row as its own coins. -/
theorem lendRow_own {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} {p : Part V W X} {c : RowCoins [p]} (h : lendRow B rows look a [p] 0 = .ok c) :
    (look { place := a, part := 0 }).2.cut { f := 0, e := 0 } p.takes = some c.1.1 := by
  simp only [lendRow] at h
  cases hp : lendPart B rows look ⟨a, 0⟩ p with
  | error e =>
    rw [hp] at h
    cases h
  | ok c' =>
    rw [hp] at h
    have e : c = (c', ()) := (Except.ok.inj h).symm
    subst e
    unfold lendPart at hp
    simp only at hp
    split at hp
    · cases hp
    split at hp
    · cases hp
    · rename_i own hown
      rw [hown]
      cases h1 : lend look p.spends ((B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (·.once))
        with
      | error e =>
        rw [h1] at hp
        cases hp
      | ok sp =>
        rw [h1] at hp
        cases h2 : lend look p.carries
          ((B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (!·.once)) with
        | error e =>
          rw [h2] at hp
          cases hp
        | ok ca =>
          rw [h2] at hp
          have e : (own, sp, ca) = c' := Except.ok.inj hp
          rw [← e]

/-- A source that is at hand behind the member number b of a thread and not in front of it. -/
theorem fresh_mem_own {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : Nat} {blk : Block S Cl}
    (hb : T.bs[b]? = some blk) {σ : Fmt.TreeSource} (hσ : σ ∈ T.fresh b) :
    ∃ i, i < (blk.oracles.flatMap id).length ∧ σ = .own (treesTo T.bs b + i) := by
  unfold Thread.fresh at hσ
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  have h2' : σ ∉ T.hand b := by simpa using h2
  unfold Thread.hand at h1 h2'
  rcases List.mem_append.1 h1 with h | h
  · exact absurd (List.mem_append_left _ h) h2'
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    have hj' := List.mem_range.1 hj
    rw [treesTo_succ hb] at hj'
    have hge : treesTo T.bs b ≤ j := by
      by_contra hlt
      exact h2' (List.mem_append_right _
        (List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_of_not_le hlt), rfl⟩))
    exact ⟨j - treesTo T.bs b, by omega, by rw [Nat.add_sub_cancel' hge]⟩

/-- The tree behind the chain's own source number E.sent + i, behind rounds as played. -/
theorem add_own (E : Env) (ps : List Played) (i : Nat) :
    (E.add ps).tree (.own (E.sent + i)) = ((tablesOf ps)[i]?).bind id := by
  show (if E.sent + i < E.sent then _ else _) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.steps_two
#print axioms ProofFile.Honest.K14.two_plays
#print axioms ProofFile.Honest.K14.reads_none_two
#print axioms ProofFile.Honest.K14.lendRow_own
#print axioms ProofFile.Honest.K14.fresh_mem_own
#print axioms ProofFile.Honest.K14.add_own
