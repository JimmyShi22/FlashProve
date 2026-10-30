-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/CoinBack.lean: two definitions with code, and statements
with their proofs. NO KIND IS NAMED. By the writers of the feed-forward layers' own rounds
(sub-protocol K4). It imports Honest/Law/Rule/Spent.lean alone.

What is here. THE READING GIVES THE COIN BACK BEHIND THE PACKING. A run's coins of the extension
field are field elements (`Cs.e`, Honest/Frame.lean). The frame packs each into the program's three
words (`coinsE`, Honest/Sum.lean), and a text for a message's entries reads a packed one back with
`Reading.gl.val`. Here: reading after packing is the identity, coin by coin; so the list of what a
row's parts spend (`rowSpent`, Honest/Law/Rule/Spent.lean), read back member by member, IS the list
of the owners' own field elements at the book's entries (`rowSpentGl`): no packing and no reading
stand in that list's text.

  `val_coin`, `val_coinsE`   one coin; the coins at a count.
  `sliceGl`, `rowSpentGl`   an entry's run off its owner's coins, and what a row of n parts spends,
      as field elements: the texts of `sliceE` and `rowSpent` without the packing.
  `val_sliceE`, `val_spentAt`, `val_rowSpent`   **each list, read back, is its like of field
      elements.**
  `sliceGl_of_look`, `rowSpentGl_alike`   **two looks that agree on each run that the book's entries
      cut for the row's parts to spend give one list**; they agree on a run where they hand one
      thing at its owner's address.

`look`, the place and the number of parts are the caller's letters. «What a row's parts spend» is
`rowSpent`'s name for its list ONLY WHERE `lendRow` RETURNS (`spentOf_row`, that file): where an
entry reaches beyond its owner's count, `drop` and `take` shorten the run in silence and every
later member's number shifts; Honest/Small/LendsRow.lean has the public test under which that does
not happen. The library has the first statement's like (`liftGl_val`,
OnBytes/Desc/First/NormBridge/HonestGl.lean).

Not shown here. That the book's lending returns. Whether two entries of the book name one coin.
Coins of the extension field alone, and runs that are spent, not those that are carried, as in
Honest/Law/Rule/Spent.lean. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Spent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Place)

/-- Reading after packing is the identity. -/
theorem val_coin (x : Cb.Gl.E) : Reading.gl.val (E.ofTriple (OnBytes.Slice.ofE x)) = x := by
  show OnBytes.Slice.toE (E.ofTriple (OnBytes.Slice.ofE x)).triple = x
  rw [E.triple_ofTriple, OnBytes.Slice.toE_ofE]

/-- The packed coins at a count, read back, are the coins. -/
theorem val_coinsE {d : Due} (c : Cs d) : (coinsE c).map Reading.gl.val = List.ofFn c.e := by
  unfold coinsE
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext fun i => val_coin (c.e i))

/-- An entry's run off its owner's coins, as field elements: `sliceE`'s text without the packing. -/
def sliceGl (look : Addr → (d : Due) × Cs d) (e : Ahead) : List Cb.Gl.E :=
  ((List.ofFn (look e.owner).2.e).drop e.start.e).take e.count.e

/-- What a row of n parts at the place p spends, from the part number j on, as field elements:
`rowSpent`'s text without the packing. -/
def rowSpentGl (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (p : Place) : Nat → Nat → List Cb.Gl.E
  | 0, _ => []
  | n + 1, j => (spentE Bk ⟨p, j⟩).flatMap (sliceGl look) ++ rowSpentGl Bk look p n (j + 1)

/-- An entry's run, read back. No hypothesis. -/
theorem val_sliceE (look : Addr → (d : Due) × Cs d) (e : Ahead) :
    (sliceE look e).map Reading.gl.val = sliceGl look e := by
  unfold sliceE sliceGl
  rw [List.map_take, List.map_drop, val_coinsE]

/-- What the part at an address spends, read back. No hypothesis. -/
theorem val_spentAt (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (a : Addr) :
    (spentAt Bk look a).map Reading.gl.val = (spentE Bk a).flatMap (sliceGl look) := by
  unfold spentAt
  rw [List.map_flatMap]
  exact congrArg (fun f => (spentE Bk a).flatMap f) (funext fun e => val_sliceE look e)

/-- **WHAT A ROW's PARTS SPEND, READ BACK MEMBER BY MEMBER, IS THE OWNERS' OWN FIELD ELEMENTS AT THE
BOOK's ENTRIES.** No hypothesis. -/
theorem val_rowSpent (Bk : ProverCoinCounts) (look : Addr → (d : Due) × Cs d) (p : Place) : ∀ (n j : Nat),
    (rowSpent Bk look p n j).map Reading.gl.val = rowSpentGl Bk look p n j
  | 0, _ => rfl
  | n + 1, j => by
    show (spentAt Bk look ⟨p, j⟩ ++ rowSpent Bk look p n (j + 1)).map Reading.gl.val =
      (spentE Bk ⟨p, j⟩).flatMap (sliceGl look) ++ rowSpentGl Bk look p n (j + 1)
    rw [List.map_append, val_spentAt, val_rowSpent Bk look p n (j + 1)]

/-! ## Two looks that agree on the runs -/

private theorem flatMap_alike {α β : Type} : ∀ (l : List α) (f g : α → List β),
    (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_alike l f g fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Two looks that hand one thing at an entry's owner give one run. CONDITIONAL on h. -/
theorem sliceGl_of_look {look look' : Addr → (d : Due) × Cs d} {e : Ahead}
    (h : look e.owner = look' e.owner) : sliceGl look e = sliceGl look' e := by
  unfold sliceGl
  rw [h]

/-- **TWO LOOKS THAT AGREE ON EACH RUN THAT THE BOOK's ENTRIES CUT FOR THE ROW's PARTS TO SPEND GIVE
ONE LIST.** n parts, from the part number j on. CONDITIONAL on that agreement. -/
theorem rowSpentGl_alike (Bk : ProverCoinCounts) (look look' : Addr → (d : Due) × Cs d) (p : Place) :
    ∀ (n j : Nat),
    (∀ i, j ≤ i → i < j + n → ∀ e ∈ spentE Bk ⟨p, i⟩, sliceGl look e = sliceGl look' e) →
    rowSpentGl Bk look p n j = rowSpentGl Bk look' p n j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    show (spentE Bk ⟨p, j⟩).flatMap (sliceGl look) ++ rowSpentGl Bk look p n (j + 1) =
      (spentE Bk ⟨p, j⟩).flatMap (sliceGl look') ++ rowSpentGl Bk look' p n (j + 1)
    rw [flatMap_alike _ _ _ (h j (Nat.le_refl j) (by omega)),
      rowSpentGl_alike Bk look look' p n (j + 1) fun i h1 h2 => h i (by omega) (by omega)]

end ProofFile.Honest

#print axioms ProofFile.Honest.val_coin
#print axioms ProofFile.Honest.val_coinsE
#print axioms ProofFile.Honest.val_sliceE
#print axioms ProofFile.Honest.val_spentAt
#print axioms ProofFile.Honest.val_rowSpent
#print axioms ProofFile.Honest.sliceGl_of_look
#print axioms ProofFile.Honest.rowSpentGl_alike
