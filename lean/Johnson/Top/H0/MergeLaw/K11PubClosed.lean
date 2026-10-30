-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/K11PubClosed.lean: KIND K11 (THE MERGE): THE CLOSED FACTS ON THE TABLE THAT
`merge_pubHeld` (Johnson/Desc/Sound/MgAt/K11Pub.lean) LEAVES, AT THE FULL SIZE's WRITTEN LISTS:
links := `linksFull` (Johnson/Desc/Sound/AtDriver.lean), ps := `flatPlacesOf linksFull true`, border
k := 346, segment m := 24. Statements with their proofs: evaluation by Lean's kernel; two
rewritings. After the pattern of Johnson/Desc/Sound/MgAt/K11Closed.lean (not
imported). NO SOUNDNESS.

The four lists are those of `merge_t2`'s premise hPub (Johnson/Top/H0/MergeLaw/TieOneTwo.lean):
O, Q: the items and the public tests that are open at border 346; O', Q': the same one step on, by
the table's row at the place number 346.
  `k11PlaceW`, `k11_place`: the place number 346 of the written list, written out.
  `keep24`: the eight public tests that other files' lemmas carry across the merge.
  `k11_hL_closed`, `k11_hIn_closed`: at the composed meaning's closed list of extra public tests
    (`moreAll`, Johnson/Desc/Sound/MoreAll.lean): whatever is asked behind the merge is one of the
    seven of `merge_pubHeld` or stands in keep24; four of the seven, and all of keep24, are asked in
    front.
  `k11_noLeft_front_closed`, `k11_noLeft_behind_closed`: no test "left m" is open in Q or in Q'.
  **`k11_hL`, `k11_hIn`**: the two premises of `merge_pubHeld` to the letter, at
    `(mgAll D Mg).more` where Mg.more is empty, at any place p that the written list has at 346.
  **`k11_noLeft_front`, `k11_noLeft_behind`**: at the same: `∀ m, Pub.left m ∉ Q`;
    `∀ q ∈ Q', ∀ m, q ≠ .left m`.
  `merge_pubHeld_full`: `merge_pubHeld` with hL, hIn and hsub paid.
  NEGATIVE TESTS, by the kernel too: with one entry fewer in keep24 the first fact fails;
    "hasRow 24" and the test on "merged" are not asked in front; "left 24" is open at an earlier
    border.
Limits. The full size's written list alone. AT THE TABLE's ROWS AND THE LIST OF EXTRA PUBLIC TESTS
AS IMPORTED: another form of either owes these again. `merge_pubHeld_full` keeps the premises
hkeep, hRow, hlk, hst, hr, hMade: shown at no value here. D.links = linksFull and Mg.more = {} are
premises.
Facts on the table alone: nothing on any verifier's state; nothing on soundness.

-/
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Driver.Chain
import Johnson.Desc.Sound.MgAt.K11Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Link Claim Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning More pubSets openSets stepOpen rowOf
  pubStep pubRowM pubOfItems pubHeld flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headMergeDecide)
open Johnson.Desc.First.Walk.Law (hasRow)

local notation "psW" => flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "OW" => (openSets linksFull psW (First.start linksFull))[346]?.getD []
set_option quotPrecheck false in
local notation "QW[" M "]" => (pubSets M linksFull psW)[346]?.getD []

/-- The place number 346 of the full size's written list. -/
def k11PlaceW : Place := { chain := 1, link := some 24, piece := 9, kind := .K11 }

set_option maxRecDepth 1000000 in
theorem k11_place : psW[346]? = some k11PlaceW := by decide +kernel

/-- The public tests that other authors' lemmas carry across the merge. -/
def keep24 : List Pub :=
  [.lookOut 24 3, .lookOut 24 8, .formsIn 24 3 "objects", .formsIn 24 3 "planes",
    .formsIn 24 4 "join", .formsIn 24 4 "own", .formsIn 24 6 "small", .formsIn 24 8 "objects"]

/-- Not of the form "left m". -/
def notLeftB : Pub → Bool
  | .left _ => false
  | _ => true

/-! ### At the closed list of extra public tests -/

set_option maxRecDepth 1000000 in
theorem k11_hL_closed :
    ∀ q ∈ pubStep QW[moreAll] (pubRowM moreAll linksFull k11PlaceW) ++
        pubOfItems (stepOpen OW (rowOf linksFull k11PlaceW)),
      q ∈ [Pub.ledger 24, .freeAbove 24, .leftOn 24, .indexIs, .indexThere, .hasRow 24,
        .formsIn 24 9 "merged"] ++ keep24 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_hIn_closed :
    ∀ q ∈ [Pub.ledger 24, .freeAbove 24, .indexIs, .indexThere] ++ keep24,
      q ∈ QW[moreAll] ++ pubOfItems OW := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_noLeft_front_closed : QW[moreAll].all notLeftB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_noLeft_behind_closed :
    (pubStep QW[moreAll] (pubRowM moreAll linksFull k11PlaceW)).all notLeftB = true := by
  decide +kernel

/-! ### Negative tests -/

set_option maxRecDepth 1000000 in
theorem k11_hL_needs_all_of_keep :
    ¬ ∀ q ∈ pubStep QW[moreAll] (pubRowM moreAll linksFull k11PlaceW) ++
        pubOfItems (stepOpen OW (rowOf linksFull k11PlaceW)),
      q ∈ [Pub.ledger 24, .freeAbove 24, .leftOn 24, .indexIs, .indexThere, .hasRow 24,
        .formsIn 24 9 "merged"] ++ keep24.tail := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_hasRow_not_in_front : Pub.hasRow 24 ∉ QW[moreAll] ++ pubOfItems OW := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_merged_not_in_front : Pub.formsIn 24 9 "merged" ∉ QW[moreAll] ++ pubOfItems OW := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k11_left_open_earlier :
    ∃ k ∈ List.range 346, Pub.left 24 ∈ (pubSets moreAll linksFull psW)[k]?.getD [] := by
  decide +kernel

/-! ### At the composed meaning -/

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **merge_pubHeld's premise hL.** -/
theorem k11_hL (hM : Mg.more = {}) (p : Place) (hp : psW[346]? = some p) :
    ∀ q ∈ pubStep QW[(mgAll D Mg).more] (pubRowM (mgAll D Mg).more linksFull p) ++
        pubOfItems (stepOpen OW (rowOf linksFull p)),
      q ∈ [Pub.ledger 24, .freeAbove 24, .leftOn 24, .indexIs, .indexThere, .hasRow 24,
        .formsIn 24 9 "merged"] ++ keep24 := by
  obtain rfl : k11PlaceW = p := Option.some.inj (k11_place.symm.trans hp)
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  exact k11_hL_closed

/-- **merge_pubHeld's premise hIn.** -/
theorem k11_hIn (hM : Mg.more = {}) :
    ∀ q ∈ [Pub.ledger 24, .freeAbove 24, .indexIs, .indexThere] ++ keep24,
      q ∈ QW[(mgAll D Mg).more] ++ pubOfItems OW := by
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  exact k11_hIn_closed

/-- **No "left m" is open in front of the merge.** -/
theorem k11_noLeft_front (hM : Mg.more = {}) : ∀ m, Pub.left m ∉ QW[(mgAll D Mg).more] := by
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  exact fun m hm => Bool.false_ne_true (List.all_eq_true.1 k11_noLeft_front_closed _ hm)

/-- **Nor behind it.** -/
theorem k11_noLeft_behind (hM : Mg.more = {}) (p : Place) (hp : psW[346]? = some p) :
    ∀ q ∈ pubStep QW[(mgAll D Mg).more] (pubRowM (mgAll D Mg).more linksFull p),
      ∀ m, q ≠ .left m := by
  obtain rfl : k11PlaceW = p := Option.some.inj (k11_place.symm.trans hp)
  rw [mgAll_more_closed D Mg hM, mgMore_is]
  intro q hq m e
  subst e
  exact Bool.false_ne_true (List.all_eq_true.1 k11_noLeft_behind_closed _ hq)

/-- `merge_pubHeld` with its three closed facts on the table paid. -/
theorem merge_pubHeld_full (hl : D.links = linksFull) (hM : Mg.more = {}) (Pm : HeadMergeP)
    (p : Place) (hp : psW[346]? = some p) (z : P) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide Pm a rs = .ok b)
    (hkeep : ∀ q ∈ keep24, (mgAll D Mg).pub q (z, a) = true → (mgAll D Mg).pub q (z, b) = true)
    (hRow : hasRow D.d1.lay (D.d1.ncl 24) D.d1.lin b = true)
    (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S))
    (hlk : D.lk 24 = some l)
    (hst : ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (hMade : K9.formsIn (K9.Readers.ofStates (mergeStates "the merge")) (D.N.group 24) 8
      "the merge" b = true) :
    pubHeld (mgAll D Mg) OW QW[(mgAll D Mg).more] (z, a) = true →
      pubHeld (mgAll D Mg) (stepOpen OW (rowOf linksFull p))
        (pubStep QW[(mgAll D Mg).more] (pubRowM (mgAll D Mg).more linksFull p)) (z, b) = true :=
  merge_pubHeld D Mg Pm 24 _ _ _ _ keep24 z hy (k11_hL D Mg hM p hp) (k11_hIn D Mg hM)
    (by rw [hl]; decide +kernel) hkeep hRow l name r hlk hst hr hMade

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.k11_place
#print axioms VerifiableInference.Desc.Sound.k11_hL_closed
#print axioms VerifiableInference.Desc.Sound.k11_hIn_closed
#print axioms VerifiableInference.Desc.Sound.k11_hL_needs_all_of_keep
#print axioms VerifiableInference.Desc.Sound.k11_hasRow_not_in_front
#print axioms VerifiableInference.Desc.Sound.k11_merged_not_in_front
#print axioms VerifiableInference.Desc.Sound.k11_left_open_earlier
#print axioms VerifiableInference.Desc.Sound.k11_hL
#print axioms VerifiableInference.Desc.Sound.k11_hIn
#print axioms VerifiableInference.Desc.Sound.k11_noLeft_front
#print axioms VerifiableInference.Desc.Sound.k11_noLeft_behind
#print axioms VerifiableInference.Desc.Sound.merge_pubHeld_full
