-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/FenceOf.lean: THE FENCE AROUND "EVERY PENDING CLAIM ON THE COMMITTED TABLE
HOLDS"
(`IndexFence`, Pile.lean) FROM FIVE FACTS ON REACHED STATES, THE TABLE's PROMISE AND ONE TEST ON THE
PLAN. One structure of Prop, one definition, six theorems. A law file: no sub-protocol imports it.

Why. The code switch's fifth tie (T5.lean) takes the fence as a premise (the field fence of
`K2Owes`). Here it is brought down to what others owe under their own names.

What is said.
  `BookFacts L M s`: five fields of the structure of facts on reached states
    (Johnson/Desc/First/FoldFacts.lean: bookInOrder, seatsCarried, bookFits, msgShapes, pileMasks),
    in
    that file's own text, at one state s, THE FIRST TREE's NUMBER BEING 0.
  `below_of_fits`: where the book's places are the listed ones and each names a tree that the book
    holds, the listed places name trees below the book's number of trees.
  `promise_gives`: at a state without a mark inside the table's promise in front of sub-protocol k,
    where the index masks' pin is open: the book has a place for every oracle message; the state's
    number of the index masks' message is the plan's; the statement holds a message of that number.
  `indexFence_of`: THE FENCE, from these and `L.places[N.indexNo]? = some N.index` (a test on the
  plan's
    numbers: the listed place of the index masks' message is the plan's tenant).
  `pinOpenB`, `pinOpen_small`, `pinOpen_full`: "the index masks' pin is open in front of k" as a
  test
    with code on the table; BY LEAN's KERNEL it accepts at all 5 | 25 code switches of the two
    written lists; `pinOpen_can_fail`: a negative test: in front of the first sub-protocol of the
    small
    list, where the index masks' message is not sent yet, it refuses.

ON "THE FIRST TREE's NUMBER IS 0". It is no free choice: at the proof file's description every place
of the code switch has firstTree = 0 (`P1K2.ft_of_pub`, Johnson/Top/H0/K2Hears/FtAtPub.lean), and so
has the public part (`P1K2.firstTree_of_pub`). So `BookFacts` asks the field bookInOrder at the
number
that the description itself bears.

Limits. `BookFacts` and the test on the plan are premises. The step from the structure of facts on
reached states is one projection a field; it is not typed here: that file does not compile over this
ground yet (one of its imports is not at hand).
(Where this and lean/THEOREM.md differ, the page
holds.) No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.AtDriver
import Johnson.Top.H0.K2Ties.Table
import Johnson.Top.H0.K2Ties.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubOfItems bookAt
  flatPlacesOf)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  place_of_seats atFirstBook atFirstSeats atFirstFits atFirstShapes)
open VerifiableInference.Desc.K13 (pileMasksC indexIsC indexThereC)

/-- **Five facts on reached states, at one state; the first tree's number is 0.** -/
structure BookFacts (L : Laid) (M : List OracleShape) (s : S) : Prop where
  bookInOrder : atFirstBook 0 s = true
  seatsCarried : atFirstSeats L s = true
  bookFits : atFirstFits s = true
  msgShapes : atFirstShapes M s = true
  pileMasks : pileMasksC s = true

/-- The listed places name trees below the book's number of trees. -/
theorem below_of_fits {L : Laid} {B : TreeBook} (h1 : seatsCarriedB L B = true)
    (h2 : bookFitsB B = true) : placesBelowB L B.place.size B.trees.size = true := by
  have e : B.place.toList = L.places.take B.place.size := by
    unfold seatsCarriedB at h1
    simp only [Bool.and_eq_true] at h1
    exact eq_of_beq h1.1.1.1
  unfold placesBelowB
  rw [← e]
  refine List.all_eq_true.2 fun q hq => decide_eq_true ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
  have hi' : i < B.place.size := by simpa using hi
  have h3 := List.all_eq_true.1 h2 i (List.mem_range.2 hi')
  rw [Array.getElem?_eq_getElem hi'] at h3
  rw [Array.getElem_toList]
  by_contra hn
  simp only [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at h3
  cases h3

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok)) (links : List ModelPart)
  (ps : List Place) (k : ℕ) (z : P)

/-- What the table's promise gives where the index masks' pin is open. -/
theorem promise_gives (a : First.S × Fr.E.Str)
    (hon : onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a) (hm : a.1.failed = none)
    (hI : Item.pinI ∈ (openSets links ps (start links))[k]?.getD []) :
    a.1.book.place.size = a.1.st.oracles.size ∧ a.1.out.indexMasks = D.N.indexNo ∧
      a.1.out.indexMasks < a.1.st.oracles.size := by
  obtain ⟨_, h⟩ := hon
  rcases h with h | ⟨hb, _, _, _⟩
  · exact absurd hm h
  simp only [Bool.and_eq_true] at hb
  have hp := List.all_eq_true.1 hb.1.2
  have hmem : ∀ q ∈ [Pub.indexIs, Pub.indexThere],
      q ∈ (pubSets (mgAll D Mg₀).more links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []) := fun q hq =>
    List.mem_append_right _ (List.mem_flatMap.2 ⟨.pinI, hI, hq⟩)
  have h1 : indexIsC D.N.indexNo a.1 = true := hp .indexIs (hmem _ (by simp))
  have h2 : indexThereC a.1 = true := hp .indexThere (hmem _ (by simp))
  have h3 := hb.2
  unfold bookAt at h3
  simp only [Bool.and_eq_true] at h3
  refine ⟨eq_of_beq h3.1.2, eq_of_beq h1, ?_⟩
  by_contra hn
  unfold indexThereC at h2
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at h2
  cases h2

/-- **The fence**, from five facts on reached states, the promise and one test on the plan. -/
theorem indexFence_of (L : Laid) (M : List OracleShape) (a : First.S × Fr.E.Str)
    (hon : onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a) (hm : a.1.failed = none)
    (hI : Item.pinI ∈ (openSets links ps (start links))[k]?.getD []) (hB : BookFacts L M a.1)
    (hP : L.places[D.N.indexNo]? = some D.N.index) : IndexFence D.N M L a.1 := by
  obtain ⟨h1, h2, h3⟩ := promise_gives D Mg₀ links ps k z a hon hm hI
  refine ⟨hB.msgShapes, hB.bookInOrder, hB.seatsCarried, h1,
    below_of_fits hB.seatsCarried hB.bookFits, h3, ?_, hB.pileMasks⟩
  rw [place_of_seats hB.seatsCarried _ (by rw [h1]; exact h3), h2]
  exact hP

end

/-- The index masks' pin is open in front of sub-protocol number k. -/
def pinOpenB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openSets links ps (start links))[k]?.getD []).contains Item.pinI

theorem pinOpen_of_B (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : pinOpenB links ps k = true) :
    Item.pinI ∈ (openSets links ps (start links))[k]?.getD [] := List.contains_iff_mem.1 h

theorem pinOpen_small : (switches 4).all (fun x =>
    pinOpenB linksSmall (flatPlacesOf linksSmall true) x.1) = true := by decide +kernel

theorem pinOpen_full : (switches 24).all (fun x =>
    pinOpenB linksFull (flatPlacesOf linksFull true) x.1) = true := by decide +kernel

theorem pinOpen_can_fail :
    pinOpenB linksSmall (flatPlacesOf linksSmall true) 0 = false := by decide +kernel

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.below_of_fits
#print axioms VerifiableInference.Desc.First.K2Ties.promise_gives
#print axioms VerifiableInference.Desc.First.K2Ties.indexFence_of
#print axioms VerifiableInference.Desc.First.K2Ties.pinOpen_of_B
#print axioms VerifiableInference.Desc.First.K2Ties.pinOpen_small
#print axioms VerifiableInference.Desc.First.K2Ties.pinOpen_full
#print axioms VerifiableInference.Desc.First.K2Ties.pinOpen_can_fail
