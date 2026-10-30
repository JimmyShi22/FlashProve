-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SplitCoin.lean: kind K14: WHICH COIN THE BOOK LENDS THE PART AT
"SPLIT". The part spends one coin under the name splitRun (Honest/K14/Parts.lean). Where the frame's
lendRow returns at its row, the book has just one spending entry for the part, under that name and
of that count, and the coin is cut off the entry's owner's coins at the entry's start. So where the
entry names the sender of the split's mask message and the place of an entry of that message among
the sender's coins, the coin that "SPLIT" adds IS the coin that the sender lays there.

  lend_one        what lend returns for one named count: one entry, and the cut off its owner's
                  coins
  lendRow_spends  what lendRow hands the one part of a row as the coins that it spends
  split_lent      so at the row of "SPLIT": one entry, and the cut
  cut_cut         a coin of a cut at ⟨0, s⟩ of count ⟨0, 1⟩ is the coin number s of a cut from the
                  front that reaches it
  one_coin        **the coin lent to "SPLIT" is the owner's own coin number s**, where the entry's
                  owner is the one part of a row to which lendRow has lent its coins, and the
                  entry's start is ⟨0, s⟩

What is not claimed. That a book has such an entry: a premise, on public data. Which entry of which
message stands at the number s among the owner's coins. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import Johnson.Desc.ProofFile.Honest.K14.KitTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)

variable {V W X W₀ Rc Ky : Type}

/-- What lend returns for one named count. -/
theorem lend_one {look : Addr → (d : Due) × Cs d} {name : String} {n : Due} {l : List Ahead}
    {sp : CsAll [(name, n)]} (h : lend look [(name, n)] l = .ok sp) :
    ∃ e, l = [e] ∧ e.name = name ∧ e.count = n ∧ (look e.owner).2.cut e.start n = some sp.1 := by
  match l, h with
  | [], h => simp [lend] at h
  | e :: l', h =>
    simp only [lend] at h
    split at h
    · cases h
    rename_i hn
    split at h
    · cases h
    rename_i hc
    split at h
    · cases h
    rename_i x hx
    match l', h with
    | [], h =>
      simp only [lend, Except.map] at h
      obtain rfl := Except.ok.inj h
      exact ⟨e, rfl, by simpa using hn, by simpa using hc, hx⟩
    | _ :: _, h => simp [lend, Except.map] at h

/-- What lendRow hands the one part of a row as the coins that it spends. -/
theorem lendRow_spends {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} {p : Part V W X} {c : RowCoins [p]} (h : lendRow B rows look a [p] 0 = .ok c) :
    lend look p.spends ((B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (·.once)) =
      .ok c.1.2.1 := by
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
    · cases h1 : lend look p.spends ((B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (·.once))
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
          obtain rfl := Except.ok.inj hp
          rfl

/-- **What the book lends the part at "SPLIT"**: it has just one spending entry for the part, under
the name splitRun and of the count of one element, and the coin is cut off that entry's owner's
coins at the entry's start. -/
theorem split_lent (A : Data) (weights : W₀ → Weights) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Place}
    {c : RowCoins [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)]}
    (h : lendRow B rows look a
      [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)] 0 = .ok c) :
    ∃ e, (B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (·.once) = [e] ∧
      e.name = splitRun ∧ e.count = ⟨0, 1⟩ ∧
      (look e.owner).2.cut e.start ⟨0, 1⟩ = some c.1.2.1.1 :=
  lend_one (name := splitRun) (n := ⟨0, 1⟩) (lendRow_spends h)

/-- The one coin of a cut at ⟨0, s⟩ is the coin number s of a cut from the front that reaches it. -/
theorem cut_cut {d t : Due} (C : Cs d) (s : Nat) {o : Cs t} {y : Cs ⟨0, 1⟩}
    (ho : C.cut ⟨0, 0⟩ t = some o) (hy : C.cut ⟨0, s⟩ ⟨0, 1⟩ = some y) (hs : s < t.e) :
    y.e 0 = o.e ⟨s, hs⟩ := by
  unfold Cs.cut at ho hy
  split at ho
  · split at hy
    · obtain rfl := Option.some.inj ho
      obtain rfl := Option.some.inj hy
      show C.e _ = C.e _
      congr 1
      exact Fin.ext (by simp)
    · cases hy
  · cases ho

/-- **The coin lent to "SPLIT" is the owner's own coin number s.** q: the one part of the owner's
row; cq: what lendRow has lent that row. -/
theorem one_coin (A : Data) (weights : W₀ → Weights) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a pl : Place}
    {c : RowCoins [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)]}
    (h : lendRow B rows look a
      [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)] 0 = .ok c)
    {q : Part V W X} {cq : RowCoins [q]} (hq : lendRow B rows look pl [q] 0 = .ok cq) (s : Nat)
    (he : ∀ e ∈ B.ahead, e.spender = ⟨a, 0⟩ → e.once = true →
      e.owner = ⟨pl, 0⟩ ∧ e.start = ⟨0, s⟩) (hs : s < q.takes.e) :
    c.1.2.1.1.e 0 = cq.1.1.e ⟨s, hs⟩ := by
  obtain ⟨e, hl, -, -, hcut⟩ := split_lent A weights h
  have hm : e ∈ (B.ahead.filter fun e => e.spender == ⟨a, 0⟩).filter (·.once) := by
    rw [hl]
    exact List.mem_cons_self ..
  obtain ⟨hm1, honce⟩ := List.mem_filter.1 hm
  obtain ⟨hm2, hsp⟩ := List.mem_filter.1 hm1
  obtain ⟨ho, hst⟩ := he e hm2 (by simpa using hsp) honce
  rw [ho, hst] at hcut
  exact cut_cut _ s (lendRow_own hq) hcut hs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.lend_one
#print axioms ProofFile.Honest.K14.lendRow_spends
#print axioms ProofFile.Honest.K14.split_lent
#print axioms ProofFile.Honest.K14.cut_cut
#print axioms ProofFile.Honest.K14.one_coin
