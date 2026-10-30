-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/DoorFactsAtPlus13.lean: five
binders (hled, hnl: of k01_fifty, K1/Law/K01Law.lean, and k01_fiftyR, K1/Law/K01FiftyR.lean; hD: of
k01_fiftyR; hkIn, hsIn: of aPile_of, K1/Law/APileOf.lean) on the wider
meaning's list of extra public tests, each to the binder's letter at
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)`, where `Mg₀.more` is the empty one. Facts on the closed term
`mwMore` (Johnson/Desc/K1/Law/DoorAtPlus13.lean) by evaluation in Lean's kernel.
  `inSetB`, `noLeftB`      the two tests; `inSet_of`, `noLeft_of`: what an accept of each says
  `hled_plus13`    hled, at mLed := fun l _ => l: the segment's own `ledger l` stands in the open
                   public set in front of each of the fifty
  `hnl_plus13`     hnl: no `left m` stands there
  `hkIn_plus13`    hkIn: "K13.pileMasks" stands there
  `hsIn_plus13`    hsIn: "K12.seatsCarried" stands there
  `doorsFit_beyond`, `doorsFit_all`   behind the last border the test on the two doors holds idly;
                   so `doorsFitAllB` (K13/Law/BridgeKind.lean) gives it at every number
  `hD_plus13`      hD: the test on the two doors, the composed meaning's and the wider one's, at
                   every number
  `doorFacts_fail`, `noLeft_fails`   [kernel] each of the tests can fail
The recursion limit is raised in this file (maxRecDepth 1000000):
for the elaboration of the kernel's evaluations alone.
What is not claimed. That the table is right. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.DoorAtPlus13
import Johnson.Desc.K13.Law.BridgeKind
import Johnson.Desc.K13.Law.IndexSeatAtTable
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf pubSets
  pubSetsBy_length openSets_length)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgMore
  mgAll_more_closed doorsFitB)
open VerifiableInference.Desc.K13.Law (plus13 cA13 doorsFitAllB pileMasksItem seatsItem)
open VerifiableInference.Desc.K12.Door (K12Data)
open IM (k1Ix)

/-! ## 1 The tests -/

/-- The item stands in the open public set in front of sub-protocol k. -/
def inSetB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Pub) : Bool :=
  ((pubSets M links ps)[k]?.getD []).contains q

theorem inSet_of {M : More} {links : List ModelPart} {ps : List Place} {k : ℕ} {q : Pub}
    (h : inSetB M links ps k q = true) : q ∈ (pubSets M links ps)[k]?.getD [] :=
  List.contains_iff_mem.1 h

/-- No `left` stands in the open public set in front of sub-protocol k. -/
def noLeftB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((pubSets M links ps)[k]?.getD []).all fun q =>
    match q with
    | .left _ => false
    | _ => true

theorem noLeft_of {M : More} {links : List ModelPart} {ps : List Place} {k : ℕ}
    (h : noLeftB M links ps k = true) (m : ℕ) :
    Pub.left m ∉ (pubSets M links ps)[k]?.getD [] := fun hm =>
  nomatch List.all_eq_true.1 h _ hm

/-- Behind the last border all three lists are empty. -/
theorem doorsFit_beyond (M₀ M : More) (cA : Pub → Bool) (links : List ModelPart) (ps : List Place)
    (i : ℕ) (h : ps.length + 1 ≤ i) : doorsFitB M₀ M cA links ps i = true := by
  have e0 : (pubSets M₀ links ps)[i]? = none :=
    List.getElem?_eq_none (by unfold pubSets; rw [pubSetsBy_length]; exact h)
  have e1 : (pubSets M links ps)[i]? = none :=
    List.getElem?_eq_none (by unfold pubSets; rw [pubSetsBy_length]; exact h)
  have e2 : (First.openSets links ps (First.start links))[i]? = none :=
    List.getElem?_eq_none (by rw [openSets_length]; exact h)
  unfold doorsFitB
  rw [e0, e1, e2]
  rfl

theorem doorsFit_all {M₀ M : More} {cA : Pub → Bool} {links : List ModelPart} {ps : List Place}
    (h : doorsFitAllB M₀ M cA links ps = true) (i : ℕ) : doorsFitB M₀ M cA links ps i = true := by
  by_cases hi : i < ps.length + 1
  · exact List.all_eq_true.1 h i (List.mem_range.2 hi)
  · exact doorsFit_beyond M₀ M cA links ps i (Nat.le_of_not_lt hi)

/-! ## 2 At the full size's written list of places, by evaluation in Lean's kernel -/

theorem led_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      (.ledger l)) = true := by
  decide +kernel

theorem noLeft_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    noLeftB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)) = true := by
  decide +kernel

theorem masksIn_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      pileMasksItem) = true := by
  decide +kernel

theorem seatsIn_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      seatsItem) = true := by
  decide +kernel

theorem doors_mw :
    doorsFitAllB mgMore mwMore cA13 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- **The tests can fail**: another segment's ledger is not open; at the composed meaning's own
list the two names are not open; with the two lists exchanged, and with an empty class, the test on
the two doors refuses at the first border. -/
theorem doorFacts_fail :
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (.ledger 4) = false ∧
    inSetB mgMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      pileMasksItem = false ∧
    inSetB mgMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      seatsItem = false ∧
    doorsFitB mwMore mgMore cA13 linksFull (flatPlacesOf linksFull true) 0 = false ∧
    doorsFitB mgMore mwMore (fun _ => false) linksFull (flatPlacesOf linksFull true) 0 = false := by
  decide +kernel

/-- `noLeftB` can fail: right behind segment 3's lookup on the calls (piece 2) a `left` stands. THE
NUMBER IS READ OFF THE TABLE's WORDS ("made by the lookup's sub-protocol, asked and dropped by the
caller's"), not off a print: a file that is not in this library prints the borders at
which one stands.
-/
theorem noLeft_fails :
    noLeftB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + 4) = false := by
  decide +kernel

/-! ## 3 The binders -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **hled**, at mLed := fun l _ => l. -/
theorem hled_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool,
    Pub.ledger ((fun (l : ℕ) (_ : Bool) => l) l d) ∈
      (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact inSet_of (List.all_eq_true.1 (List.all_eq_true.1 led_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- **hnl.** -/
theorem hnl_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool, ∀ m,
    Pub.left m ∉ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
      (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d m
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact noLeft_of (List.all_eq_true.1 (List.all_eq_true.1 noLeft_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp)) m

/-- **hkIn.** -/
theorem hkIn_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool,
    pileMasksItem ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
      (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact inSet_of (List.all_eq_true.1 (List.all_eq_true.1 masksIn_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- **hsIn.** -/
theorem hsIn_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool,
    seatsItem ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
      (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact inSet_of (List.all_eq_true.1 (List.all_eq_true.1 seatsIn_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- **hD**, at M9 := mgAll Dm Mg₀ and D13 := d13 Dm. -/
theorem hD_plus13 (h : Mg₀.more = {}) : ∀ i,
    doorsFitB (mgAll Dm Mg₀).more (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more cA13 linksFull
      (flatPlacesOf linksFull true) i = true := by
  intro i
  rw [plus13_more_closed Dm dk Mg₀ h, mgAll_more_closed Dm Mg₀ h]
  exact doorsFit_all doors_mw i

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hled_plus13
#print axioms VerifiableInference.Desc.K1.hnl_plus13
#print axioms VerifiableInference.Desc.K1.hkIn_plus13
#print axioms VerifiableInference.Desc.K1.hsIn_plus13
#print axioms VerifiableInference.Desc.K1.hD_plus13
#print axioms VerifiableInference.Desc.K1.doorFacts_fail
#print axioms VerifiableInference.Desc.K1.noLeft_fails
