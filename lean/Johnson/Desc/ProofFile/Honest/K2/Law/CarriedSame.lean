-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CarriedSame.lean: the kind "the code switch" (K2): TWO SWITCHES
OF ONE CHAIN, AT ONE RUN's COINS: WHERE THE BOOK's CARRIED ENTRIES OF THE SECOND NAME, NUMBER BY
NUMBER, THE RUNS THAT THOSE OF THE FIRST NAME, THE SECOND IS HANDED EACH CARRIED STRETCH THAT THE
FIRST IS HANDED: `GivesAll` (Honest/K2/Law/ClosingGrows.lean). Four statements with their proofs; no
definition.

  `carried_has_entry`, `part_has_entry`, `handed_has_entry`   where the lending returned and the
                      carried stretch number i returns, the book's list has an entry number i
  `givesAll_carried`  THE LAW: under hT, on the book alone

hT IS A PREMISE, ON PUBLIC DATA: for each entry number i of what the first carries there is an entry
number i of what the second carries, with the same owner, start and count. It is proved at no book
here. It asks nothing on WHICH run that is.

By: `carried_of_handed` (Honest/K2/Law/CarriedOfLend.lean), at both switches. Kin: the first three
are the way back of `carried_returns_lend`, `carried_returns_part`, `carried_returns`
(Honest/K2/Law/CarriedReturns.lean): there: an entry number i, so the stretch number i returns;
here: the stretch returns, so there is an entry.

Limits. An equation at each run's coins: no sentence on what an element is for. That both switches
are handed their stretches is a premise. Nothing asks that the second stand behind the first.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedOfLend
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- Of the frame's `lend`: a carried stretch that returns has its entry. -/
theorem carried_has_entry (look : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y →
      ∀ (i : Nat) (s : Stretch), Stretch.carried ds y i = .ok s → ∃ e, l[i]? = some e
  | [], [], _, _, _, _, hs => by simp [Stretch.carried] at hs
  | [], _ :: _, _, h, _, _, _ => by simp [lend] at h
  | _ :: _, [], _, h, _, _, _ => by simp [lend] at h
  | d :: ds, a :: l, y, h, i, s, hs => by
    unfold lend at h
    by_cases h1 : (a.name != d.1) = true
    · rw [if_pos h1] at h
      cases h
    · rw [if_neg h1] at h
      by_cases h2 : (a.count != d.2) = true
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h
        cases hc : (look a.owner).2.cut a.start d.2 with
        | none =>
          rw [hc] at h
          cases h
        | some x =>
          rw [hc] at h
          obtain ⟨y', hy', rfl⟩ := exMap_ok h
          cases i with
          | zero => exact ⟨a, rfl⟩
          | succ n =>
            obtain ⟨e, he⟩ := carried_has_entry look ds l y' hy' n s hs
            exact ⟨e, by simpa using he⟩

/-- The like of `lendPart`, at a part of any kind. -/
theorem part_has_entry {V W X : Type} (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) (c : p.Coins)
    (h : lendPart B rows look a p = .ok c) (i : Nat) (s : Stretch)
    (hs : Stretch.carried p.carries c.2.2 i = .ok s) :
    ∃ e, ((B.ahead.filter fun x => x.spender == a).filter (!·.once))[i]? = some e := by
  unfold lendPart at h
  simp only at h
  by_cases h1 : (p.takes != dueAt rows a) = true
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    cases hc : (look a).2.cut ⟨0, 0⟩ p.takes with
    | none =>
      rw [hc] at h
      cases h
    | some own =>
      rw [hc] at h
      obtain ⟨sp, -, h'⟩ := exBind_ok h
      obtain ⟨ca, hca, rfl⟩ := exMap_ok h'
      exact carried_has_entry look p.carries _ ca hca i s hs

variable {Bk : ProverCoinCounts}

/-- At the switch's part. -/
theorem handed_has_entry (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c) (i : Nat)
    (s : Stretch) (hs : Stretch.carried p.carries c.2.2 i = .ok s) :
    ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e := by
  unfold handed at h
  cases hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [hl] at h
    cases h
  | ok c' =>
    rw [hl] at h
    have ec : c' = c := Option.some.inj h
    subst ec
    exact part_has_entry Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩ _ c' hl i s hs

/-- **THE LAW.** p₀, p: two switches of one chain. hT: on the book alone. -/
theorem givesAll_carried (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hT : ∀ (i : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[i]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count) :
    GivesAll (Stretch.carried p₀.carries c₀.2.2) (Stretch.carried p.carries c.2.2) := by
  intro i s hs
  obtain ⟨e₀, he₀⟩ := handed_has_entry ch p₀ k c₀ h₀ i s hs
  obtain ⟨e, he, t1, t2, t3⟩ := hT i e₀ he₀
  rw [carried_of_handed ch p k c h i e he, t1, t2, t3,
    ← carried_of_handed ch p₀ k c₀ h₀ i e₀ he₀]
  exact hs

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.carried_has_entry
#print axioms ProofFile.Honest.K2.Law.part_has_entry
#print axioms ProofFile.Honest.K2.Law.handed_has_entry
#print axioms ProofFile.Honest.K2.Law.givesAll_carried
