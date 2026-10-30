-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HandedAtEnd.lean: no soundness is claimed.
The first two clauses of HandedRoots (OpensAtW.lean), paid out of the first table's own promise at its last border. The last table's promise (onL, Johnson/Desc/Last/BordersLast.lean) bears at every border, as its first clause, the slot's own condition Oc; at the filling that is meant Oc is ocEnd (Johnson/Desc/Sound/TieEnd.lean): the first chain's whole promise at its last border. That promise holds (1) the book-keeping bookAt: the record's book has as many trees as the table's numbers say (Numbers.treesAt none); (2) every public item that is open there: among them, where the meaning is filled by the layer (Door.FillsK12, Johnson/Desc/K12/Door/FillsK12.lean), «K12.bookInOrder»: as many roots as trees, and the tree at place z has the number ft + z.
  bookAt_of_ocEnd     the first: at a record without a mark
  **handed_two**      ocEnd … p y · no mark · FillsK12 Mg₁ d · the item is open at the last border · firstOfS (get p).2 = some f ⇒ f.roots = N₁.treesAt none ∧ ∀ j T, f.book.trees[j]? = some T → T.number = d.ft + j
  **handedRoots_at**  inside the last table's promise at any border k, at Oc := ocEnd …, Mg := tiedMeaning get Mg₁ MgS, hand := fun q => firstOfS (get q).2: HandedRoots (N₁.treesAt none) d.ft nΩ f o' from its third clause alone
Left, by name. hq: the item is open at the first chain's last border (a test on the table; Johnson/Desc/First/BordersKept.lean has the law «open at the start and dropped by nobody») · FillsK12 Mg₁ d (the make of the meaning) · the third clause: Omega's tree's number in the shared chain's end's book: the last table's promise says nothing of it.
Does not show. That the promise is kept along the first chain (each kind's «I keep the item»: the table's ties). No member. Nothing on soundness.
-/
import Johnson.ToldDescR.OpensAtW
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.K12.Door.FillsK12
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Meaning Numbers pubSets moreItem)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut firstOfS)
open VerifiableInference.Desc.K12.Door (FillsK12 K12Data nBook numbers_of_book roots_of_book)

section
variable {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
  (links : List ModelPart) (ps : List Place)

/-- At a record without a mark the first chain's promise at its last border holds its book-keeping
on the book: as many trees as the table's numbers say. -/
theorem bookAt_of_ocEnd (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) : (get p).2.book.trees.size = N₁.treesAt none := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have hb : First.bookAt N₁ none (get p).2 = true := (Bool.and_eq_true_iff.1 h'.1).2
    unfold First.bookAt at hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact hb.1.1

/-- **The first two clauses, of what the last chain's start takes of the first chain's last
record.** -/
theorem handed_two (d : K12Data) (hM : FillsK12 Mg₁ d)
    (hq : moreItem nBook ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) (p : A) (y : Strs)
    (h : ocEnd get N₁ Mg₁ links ps p y) (hm : (get p).2.failed = none) {f : Handed}
    (hf : firstOfS (get p).2 = some f) :
    f.roots = N₁.treesAt none ∧ ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T →
      T.number = d.ft + j := by
  have hb := ocEnd_pub get N₁ Mg₁ links ps p y h hm _ hq
  rw [hM.book] at hb
  have hb' : VerifiableInference.Desc.K12.Door.bookInOrderB d.ft (get p).2.book (get p).2.roots =
    true := hb
  unfold firstOfS at hf
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
  exact ⟨(roots_of_book hb').trans (bookAt_of_ocEnd get N₁ Mg₁ links ps p y h hm),
    fun j T hT => numbers_of_book hb' j T hT⟩

end

section
variable {P S₁ S₂ P₀ Wt : Type} {Fr : Frame} (get : P × S₁ → P₀ × First.S) (N₁ : Numbers)
  (Ns : NumbersS) (Mg₁ : Meaning P₀ Wt) (MgS : MeaningS S₂ (P × S₁) Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (links : List ModelPart) (ps : List Place)

/-- **`HandedRoots` inside the last table's promise, from its third clause alone.** -/
theorem handedRoots_at (d : K12Data) (hM : FillsK12 Mg₁ d)
    (hq : moreItem nBook ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) (k nΩ : ℕ)
    (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str)
    (ha : onQ₃ (Fr := Fr) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ MgS) Pm PL
      (ocEnd get N₁ Mg₁ links ps) k a)
    {f : Handed} (hf : firstOfS (get (a.1.1.1, a.1.1.2.1)).2 = some f) {o' : SharedOut}
    (hΩ : ∀ (q : ℕ × ℕ) (T : Tree), o'.book.place[o'.omega]? = some q →
      o'.book.trees[q.1]? = some T → T.number = nΩ) :
    HandedRoots (N₁.treesAt none) d.ft nΩ f o' := by
  obtain ⟨h1, h2⟩ := handed_two get N₁ Mg₁ links ps d hM hq _ _ ha.1 ha.2.1 hf
  exact ⟨h1, h2, hΩ⟩

end

end ToldDesc

#print axioms ToldDesc.bookAt_of_ocEnd
#print axioms ToldDesc.handed_two
#print axioms ToldDesc.handedRoots_at
