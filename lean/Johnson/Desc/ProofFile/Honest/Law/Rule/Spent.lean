-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Spent.lean: the coins that the parts of a list spend, as the
book gives them at a run's coins: a function of the book and the coins (`spentOf_row`). On `lend`,
`lendPart`, `lendRow` (Honest/Frame.lean) and `coinsE` (Honest/Sum.lean): no kind is named.

  1  `runsE`, `spentOf`   the coins of a list of blocks; the coins that the parts of a list spend:
     the two definitions stand in Honest/SpentOf.lean, which this file imports
  2  `sliceE`, `spentAt`, `rowSpent`   an entry's block, cut from its owner's coins; what the part
     at an address spends; what a list of n parts spends
  3  `ofFn_cut`, `cut_coinsE`, `lend_runsE`, `spentOf_row`   where `lendRow` returns, `spentOf` of
     what it returns is `rowSpent`

Limits.
  * Coins of the extension field alone (`coinsE` reads no other).
  * Blocks that are spent, not those that are carried.
  * Nothing says that `lendRow` returns. Where an entry of the book reaches beyond its owner's
    count, `sliceE` returns a shorter block without an error, and the later coins' numbers in
    `rowSpent` shift; `spentOf_row` speaks only where `lendRow` returns.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SpentOf
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E)
open VerifiableInference.Desc (Place)

variable {V W X : Type}

/-! ## 2 From the book and the coins -/

/-- An entry's block, cut from its owner's coins of the extension field. -/
def sliceE (look : Addr → (d : Due) × Cs d) (e : Ahead) : List E :=
  ((coinsE (look e.owner).2).drop e.start.e).take e.count.e

/-- What the part at an address spends: the book's spending entries that name it, in the book's
order. -/
def spentAt (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (a : Addr) : List E :=
  (spentE Bk a).flatMap (sliceE look)

/-- What a list of n parts at a place spends, part by part, from part number j on. -/
def rowSpent (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (p : Place) : Nat → Nat → List E
  | 0, _ => []
  | n + 1, j => spentAt Bk look ⟨p, j⟩ ++ rowSpent Bk look p n (j + 1)

/-! ## 3 The lemmas -/

/-- A stretch of a list that is given by a function. -/
theorem ofFn_cut {α : Type} {d n : Nat} (a : Nat) (h : a + n ≤ d) (f : Fin d → α) :
    (List.ofFn fun i : Fin n => f ⟨a + i.1, by have := i.2; omega⟩) =
      ((List.ofFn f).drop a).take n := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_ofFn, List.getElem?_ofFn,
      dif_pos hi, dif_pos (by omega)]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by
        rw [List.length_take]
        exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_not_lt hi))]

theorem cut_coinsE {d : Due} {c : Cs d} {a n : Due} {x : Cs n} (h : c.cut a n = some x) :
    coinsE x = ((coinsE c).drop a.e).take n.e := by
  unfold Cs.cut at h
  split at h
  · rename_i hb
    have e := Option.some.inj h
    subst e
    exact ofFn_cut a.e hb.2 fun i => E.ofTriple (OnBytes.Slice.ofE (c.e i))
  · cases h

theorem lend_runsE (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (es : List Ahead) (sp : CsAll ds), lend look ds es = .ok sp →
    runsE ds sp = es.flatMap (sliceE look)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | d :: ds, a :: l, sp, h => by
    simp only [lend] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    rename_i x hx
    obtain ⟨y, hy, e⟩ := exMap_ok h
    subst e
    have hc : a.count = d.2 := by simpa using h2
    show coinsE x ++ runsE ds y = sliceE look a ++ l.flatMap (sliceE look)
    rw [lend_runsE look ds l y hy, cut_coinsE hx]
    unfold sliceE
    rw [hc]

/-- **Where the book gives a list of parts its coins, what the list's parts spend is a function of
the book and the coins.** -/
theorem spentOf_row (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (p : Place) : ∀ (ps : List (Part V W X)) (j : Nat) (c : RowCoins ps),
    lendRow Bk rows look p ps j = .ok c → spentOf ps c = rowSpent Bk look p ps.length j
  | [], _, _, _ => rfl
  | q :: ps, j, c, h => by
    simp only [lendRow] at h
    obtain ⟨c₁, h1, h'⟩ := exBind_ok h
    obtain ⟨r, hr, e⟩ := exMap_ok h'
    subst e
    obtain ⟨c₀, h0, e0⟩ : ∃ c₀, lendPart Bk rows look ⟨p, j⟩ q = .ok c₀ ∧ c₀ = c₁ := by
      cases hq : lendPart Bk rows look ⟨p, j⟩ q with
      | error s =>
        rw [hq] at h1
        cases h1
      | ok c₀ =>
        rw [hq] at h1
        exact ⟨c₀, rfl, Except.ok.inj h1⟩
    subst e0
    show runsE q.spends c₀.2.1 ++ spentOf ps r =
      spentAt Bk look ⟨p, j⟩ ++ rowSpent Bk look p ps.length (j + 1)
    rw [spentOf_row Bk rows look p ps (j + 1) r hr,
      lend_runsE look q.spends _ c₀.2.1 (lendPart_ok h0).2.1]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.sliceE
#print axioms ProofFile.Honest.spentAt
#print axioms ProofFile.Honest.rowSpent
#print axioms ProofFile.Honest.ofFn_cut
#print axioms ProofFile.Honest.cut_coinsE
#print axioms ProofFile.Honest.lend_runsE
#print axioms ProofFile.Honest.spentOf_row
