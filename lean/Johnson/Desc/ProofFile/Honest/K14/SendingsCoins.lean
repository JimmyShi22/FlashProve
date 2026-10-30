-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsCoins.lean: where lendRow returns at a row of one part,
and the count beside what look hands out at the part's address is the table's count there, the coins
of the extension field that the part is lent as its own ARE the coins of that field that look hands
out at the address: at every number, beyond the count too, where both sides are 0. In the shared
chain, at a run's coins, the second condition is shown (find_due), and lendRow's returning alone is
asked.

  find_due        the count beside the coins that are found at an address is the table's count
                  there; where nothing is found at the address both sides are the default count,
                  0 and 0 (getD on the left, dueAt's own default on the right)
  lendRow_takes   where lendRow returns, the part takes just as many coins as the table has for it
  lent_e          under both conditions (h, hd): the part's own coin number j of the extension
                  field, as the program's element, or 0 beyond the count: the same of the coins that
                  look hands out at the address
  lent_shared     that in the shared chain (the chain number 1), at a run's coins, where lendRow
                  returns: general in the part

What is not claimed. Nothing on the coins of the base field. Nothing on how coins are sampled.
Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.KitTwo
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {V W X : Type}

/-- The count beside the coins that are found at an address is the table's count there. Where
nothing is found there, the left side is the default count ⟨0, 0⟩ (getD), and so is dueAt's. The
frame has a theorem of the same short name one namespace up, with another statement
(ProofFile.Honest.find_due, Honest/Law/ReadyAny.lean); inside this namespace the short name means this
one. -/
theorem find_due : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    ((Purse.find? l c a).getD ⟨{ f := 0, e := 0 }, Cs.empty⟩).1 = dueAt l a
  | [], _, _ => rfl
  | r :: l, c, a => by
    unfold Purse.find? dueAt
    rw [List.lookup_cons]
    by_cases h : r.1 = a
    · subst h
      simp
    · have h1 : (r.1 == a) = false := beq_eq_false_iff_ne.2 h
      have h2 : (a == r.1) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
      rw [if_neg (by rw [h1]; exact Bool.false_ne_true), h2]
      exact find_due l c.2 a

/-- Where lendRow returns, the part takes just as many coins as the table has for it. Kin: the first
clause of the frame's lendPart_ok (Honest/Law/Rule/PartCell.lean), here at a row of one part. -/
theorem lendRow_takes {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} {p : Part V W X} {c : RowCoins [p]} (h : lendRow B rows look a [p] 0 = .ok c) :
    p.takes = dueAt rows { place := a, part := 0 } := by
  simp only [lendRow] at h
  cases hp : lendPart B rows look ⟨a, 0⟩ p with
  | error e =>
    rw [hp] at h
    cases h
  | ok c' =>
    unfold lendPart at hp
    simp only at hp
    split at hp
    · cases hp
    · rename_i hne
      simpa using hne

/-- **The part's own coin number j of the extension field**, as the program's element, 0 beyond the
count, is the coin number j that look hands out at the part's address, where lendRow returns at the
row of this one part (h) and the count beside what look hands out at the address is the table's
count there (hd). -/
theorem lent_e {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} {p : Part V W X} {c : RowCoins [p]} (h : lendRow B rows look a [p] 0 = .ok c)
    (hd : (look { place := a, part := 0 }).1 = dueAt rows { place := a, part := 0 }) (j : Nat) :
    (coinsE c.1.1).toArray.getD j zeroE =
      if hj : j < (look { place := a, part := 0 }).1.e then
        E.ofTriple (OnBytes.Slice.ofE ((look { place := a, part := 0 }).2.e ⟨j, hj⟩))
      else zeroE := by
  have ht : p.takes = (look { place := a, part := 0 }).1 := (lendRow_takes h).trans hd.symm
  have ho := lendRow_own h
  unfold Cs.cut at ho
  split at ho
  · rename_i hle
    rw [← Option.some.inj ho]
    unfold coinsE
    by_cases hj : j < (look { place := a, part := 0 }).1.e
    · have hj' : j < p.takes.e := by rw [ht]; exact hj
      rw [dif_pos hj]
      simp [Array.getD_eq_getD_getElem?, hj']
    · have hj' : ¬ j < p.takes.e := by rw [ht]; exact hj
      rw [dif_neg hj]
      simp [Array.getD_eq_getD_getElem?, hj']
  · cases ho

/-- **That in the shared chain, at a run's coins**, where lendRow returns there (h); hd is had from
find_due. The chain's number is the literal 1. -/
theorem lent_shared {Bk : ProverCoinCounts} (k : Coins Bk) {a : Place} {p : Part V W X} {c : RowCoins [p]}
    (h : lendRow Bk (Bk.rowsOf 1) (k.look 1) a [p] 0 = .ok c) (j : Nat) :
    (coinsE c.1.1).toArray.getD j zeroE =
      if hj : j < (k.look 1 { place := a, part := 0 }).1.e then
        E.ofTriple (OnBytes.Slice.ofE ((k.look 1 { place := a, part := 0 }).2.e ⟨j, hj⟩))
      else zeroE :=
  lent_e h (find_due Bk.shared k.shared { place := a, part := 0 }) j

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.find_due
#print axioms ProofFile.Honest.K14.lendRow_takes
#print axioms ProofFile.Honest.K14.lent_e
#print axioms ProofFile.Honest.K14.lent_shared
