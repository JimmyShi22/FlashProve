-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean: KIND K5's TESTS ON THE WRITTEN LISTS, DECIDED ONCE BY THE KERNEL, AT THE FULL SIZE: twenty-five segments (twelve groups of
a layers' and an attention segment; the head's), the driver's own flat list of places, the border in front of the kind's place in group g: 14 (2 g + 1) + 4.

Why. Some twenty premises of the kind's law at the table of joints read nothing but the written list of segments, the list of places and the lists of extra public tests.
Here each is a theorem: a closed, decidable sentence which Lean's kernel reduces to true ("decide +kernel": no native code, no axiom beyond
propext).

The wider list has a fourth name ("K5.rowsBare"; Johnson/Desc/First/Att/Door/Plus.lean): eight tests in the place of seven.
A ninth test: TiedObjAt.
The wider list has a fifth name ("K5.lookLeft"; Plus.lean): one of twenty; OpenQ has fourteen fields; k5_tiedR's two facts at the border stand under the narrow promise; and SEVEN
MORE TESTS, of k5_tiedAtR_owes (K5TiedOwes.lean): five at each group, two on the whole lists.
The bridge stands on a widening in another file that lays the public sentences too (Johnson/Desc/Sound/PlusDoorP.lean): of its five tests on the lists four give way to that widening's ONE test doorsFitB
(Johnson/Desc/Sound/PlusDoorA.lean) at the two borders; the premise on what the wide names say beside their tests is gone. THE DECISIONS ARE CUT IN FOUR, THE NEGATIVE TESTS IN THREE (less memory at a time).

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)



Main names:
  `DoorsAt`, `DoorsAt'`, `HopenAt'`: the three tests of k5_tiedR (Johnson/Desc/First/Att/Door/Law/PlusBridge.lean), in that theorem's own words, at the composed filling's closed
    list against the wider list. `TwentyAt`: K5Table.openQ (K5AtMgPaid.lean) and hQ of k5Fill_plus (K5FillPlus.lean). `FourteenAt`: OpenQ's fourteen memberships (K5DoorAtPlus.lean).
    `TiesAt`: K5Table.tiesO at the kind's place. `TiedObjAt`: K5Table.tiedObj. `SubAt`, `PlaceAt`, `NextAt`: the segment's sort and the two places (K5Place's; hk, hk').
    `AsksAt`: hQ of k5_tiedAtR_owes. `RidersAt`: its hB.
  `k5Lists_doors`, `k5Lists_open`, `k5Lists_items`, `k5Lists_places`: four decisions; `k5Lists_full`: **all twelve tests at all twelve groups**, joined. `k5Whole_full`: readsOpen and rowsApart at the whole lists (its hr, hap).
  `k5Bite_doors`, `k5Bite_open`, `k5Bite_items`, `k5Whole_bite`: THE NEGATIVE TESTS: nineteen and two changed tests, each rejected: so each test can fail. (rowsApart reads the table's rows place by place, not the order
    of the places: doubling the list or adding a place does not turn it; its negative test hands it other rows, through rowsApartBy, which the library keeps for that.)
  `doors_full` … `riders_full`, `openQ_full`, `ledQ_full`, `readsQ_full`, `readsOpen_full`, `rowsApart_full`: each premise by itself.
  `k5_tiedR_full`: k5_tiedR with its three tests paid: so that these are its premises to the letter is Lean's word.
AT WHICH TEXTS. The list of segments is written out in this file, letter for letter as linksFull (Johnson/Desc/Sound/AtDriver.lean), which this file does not import; so
is the composed filling's closed list, as mgMore (Johnson/Desc/Sound/MgAllAt.lean) through moreOver9. OWED, each by rfl, where these files stand: linksFull = the first; mgMore = the second.
The four short names LF, PF, M9, MP are private and reducible: no new public name for a list.
DECIDED AT ONE VERSION OF THE TABLE (Johnson/Desc/First/Borders.lean) AND OF THE PARTS' LISTS. At another version the decisions are to be made anew: the file
compiles again or it does not.
Is it empty here? No: closed sentences under g < 12 alone.
Not shown: anything at another list of segments; that the lists are the right ones.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5DoorAtPlus
import Johnson.Desc.First.Att.Door.Law.PlusBridge
import Johnson.Desc.First.PubHeldStep
import Johnson.Desc.First.Att.K05Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (rowsApart rowsApartBy doorsFitB)
open VerifiableInference.Desc.First.Att.P (ridersB)

/-- The segments' sorts at the full size: the text of linksFull (Johnson/Desc/Sound/AtDriver.lean), letter for letter. -/
private abbrev LF : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]
/-- The driver's flat list of places at it. -/
private abbrev PF : List Place := flatPlacesOf LF true
/-- The composed filling's closed list of extra public tests: the text of mgMore (Johnson/Desc/Sound/MgAllAt.lean) through moreOver9. -/
private abbrev M9 : More := (moreOver9 {}).strike leavesName
/-- The wider list over the empty base. -/
private abbrev MP : More := morePlus {}

/-! ## The tests, each in the words of the premise that it pays; g: the group; the border in front of the kind's place: 14 (2 g + 1) + 4 -/

abbrev DoorsAt (g : Nat) : Prop := doorsFitB M9 MP isWideQ LF PF (14 * (2 * g + 1) + 4) = true

abbrev DoorsAt' (g : Nat) : Prop := doorsFitB M9 MP isWideQ LF PF (14 * (2 * g + 1) + 4 + 1) = true

abbrev HopenAt' (g : Nat) : Prop :=
  ∀ x ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD [],
    x ∈ (pubSets M9 LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD [] ∨ isThreeQ x = true

abbrev TwentyAt (g : Nat) : Prop :=
  ∀ q ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD [],
    q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
      q = .more (some (2 * g + 1)) "K5.lookLeft"

abbrev FourteenAt (g : Nat) : Prop :=
  ∀ q ∈ [Pub.more (some (2 * g + 1)) "K5.liveReq", .more (some (2 * g + 1)) "K5.readsThere", .look (2 * g + 1), .ledger (2 * g + 1),
      .freeAbove (2 * g + 1), .left (2 * g + 1), .more (some (2 * g + 1)) "frame.liveIs", .linkFresh (2 * g + 1),
      .more none "K12.seatsCarried", .more none "K12.msgShapes", .more (some (2 * g + 1)) "frame.sentIs",
      .more (some (2 * g + 1)) "K5.rowsBare", .more (some (2 * g + 1)) "K5.lookLeft", .callerIn (2 * g + 1)],
    q ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD []

abbrev TiesAt (g : Nat) : Prop :=
  ∀ i ∈ (openSets LF PF (start LF))[14 * (2 * g + 1) + 4]?.getD [],
    (rowOf LF ⟨1, some (2 * g + 1), 3, .K5⟩).ins.contains i = false → i ≠ .pinI →
      ∀ q ∈ tiesOf i, q = .formsInT (2 * g + 1) 2 "objects"

abbrev TiedObjAt (g : Nat) : Prop :=
  Pub.formsInT (2 * g + 1) 2 "objects" ∈ pubOfItems ((openSets LF PF (start LF))[14 * (2 * g + 1) + 4]?.getD [])

/-! ### Five more, of k5_tiedAtR_owes (Johnson/Desc/First/Att/Door/Law/K5TiedOwes.lean): the segment's sort, the two places, the base row's asks, the riders -/

abbrev SubAt (g : Nat) : Prop := LF[2 * g + 1]? = some .attention

abbrev PlaceAt (g : Nat) : Prop := PF[14 * (2 * g + 1) + 4]? = some ⟨1, some (2 * g + 1), 3, .K5⟩

abbrev NextAt (g : Nat) : Prop := PF[14 * (2 * g + 1) + 4 + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩

abbrev AsksAt (g : Nat) : Prop :=
  ∀ t ∈ (pubRowOf LF ⟨1, some (2 * g + 1), 3, .K5⟩).asks, t ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD []

abbrev RidersAt (g : Nat) : Prop := ridersB LF PF (14 * (2 * g + 1) + 4) (2 * g + 1) = true

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The bridge's three. -/
theorem k5Lists_doors : ∀ g, g < 12 → DoorsAt g ∧ DoorsAt' g ∧ HopenAt' g := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- What is open in front at the wider list. -/
theorem k5Lists_open : ∀ g, g < 12 → TwentyAt g ∧ FourteenAt g ∧ AsksAt g := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The open items. -/
theorem k5Lists_items : ∀ g, g < 12 → TiesAt g ∧ TiedObjAt g ∧ RidersAt g := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The segment's sort and the two places. -/
theorem k5Lists_places : ∀ g, g < 12 → SubAt g ∧ PlaceAt g ∧ NextAt g := by
  decide +kernel

/-- **All twelve, at all twelve groups**: four decisions of the kernel, joined. -/
theorem k5Lists_full : ∀ g, g < 12 →
    DoorsAt g ∧ DoorsAt' g ∧ HopenAt' g ∧ TwentyAt g ∧ FourteenAt g ∧ TiesAt g ∧ TiedObjAt g ∧
      SubAt g ∧ PlaceAt g ∧ NextAt g ∧ AsksAt g ∧ RidersAt g := fun g hg =>
  ⟨(k5Lists_doors g hg).1, (k5Lists_doors g hg).2.1, (k5Lists_doors g hg).2.2, (k5Lists_open g hg).1, (k5Lists_open g hg).2.1,
    (k5Lists_items g hg).1, (k5Lists_items g hg).2.1, (k5Lists_places g hg).1, (k5Lists_places g hg).2.1, (k5Lists_places g hg).2.2,
    (k5Lists_open g hg).2.2, (k5Lists_items g hg).2.2⟩

set_option maxRecDepth 1000000 in
/-- **Two tests on the whole lists**, of k5_tiedAtR_owes too. -/
theorem k5Whole_full : readsOpen LF PF (start LF) = true ∧ rowsApart LF PF = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Their negative tests: nothing open at the chain's start; rows that close "no mark". -/
theorem k5Whole_bite : readsOpen LF PF [] = false ∧
    rowsApartBy (fun p => { rowOf LF p with ins := .unmarked :: (rowOf LF p).ins }) PF = false := by
  decide +kernel

/-! ## Each test can fail: seventeen changed tests, each refused by the kernel at every group -/

/-! ## The negative tests: nineteen changed tests at each group, each rejected: in three decisions -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- (1) HopenAt' with no name let through · (2) DoorsAt with the three names alone called wide: in front the fourth and the fifth name are open at the wider list alone · (3) DoorsAt with the two lists changed round ·
(4) DoorsAt with the tied test of the run "objects" called wide too: its third part · (5) DoorsAt' with no name called wide · (6) DoorsAt' with the two lists changed round. -/
theorem k5Bite_doors : ∀ g, g < 12 →
    (¬ ∀ x ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD [], x ∈ (pubSets M9 LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD []) ∧
    (doorsFitB M9 MP isThreeQ LF PF (14 * (2 * g + 1) + 4) = false) ∧
    (doorsFitB MP M9 isWideQ LF PF (14 * (2 * g + 1) + 4) = false) ∧
    (doorsFitB M9 MP (fun q => isWideQ q || q == .formsInT (2 * g + 1) 2 "objects") LF PF (14 * (2 * g + 1) + 4) = false) ∧
    (doorsFitB M9 MP (fun _ => false) LF PF (14 * (2 * g + 1) + 4 + 1) = false) ∧
    (doorsFitB MP M9 isWideQ LF PF (14 * (2 * g + 1) + 4 + 1) = false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- (7) TwentyAt without "ledger.treesAre" · (8) TwentyAt without "K5.lookLeft" · (9) FourteenAt's sentence at an item that the kind's own row makes: it is not open in front · (10) · (11) · (12) FourteenAt's twelfth,
thirteenth and fourteenth at the border behind: the kind's rows have dropped them · (13) AsksAt at the border behind. -/
theorem k5Bite_open : ∀ g, g < 12 →
    (¬ ∀ q ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD [], q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨
      q = .more (some (2 * g + 1)) "K5.lookLeft") ∧
    (¬ ∀ q ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD [], q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨
      q = .more (some (2 * g + 1)) "ledger.treesAre") ∧
    (¬ Pub.more (some (2 * g + 1)) "K5.okAt" ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD []) ∧
    (¬ Pub.more (some (2 * g + 1)) "K5.rowsBare" ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD []) ∧
    (¬ Pub.more (some (2 * g + 1)) "K5.lookLeft" ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD []) ∧
    (¬ Pub.callerIn (2 * g + 1) ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD []) ∧
    (¬ ∀ t ∈ (pubRowOf LF ⟨1, some (2 * g + 1), 3, .K5⟩).asks, t ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4 + 1]?.getD []) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- (14) TiesAt at another run's name · (15) TiedObjAt one border earlier: the item is not yet open there · (16) RidersAt at the next attention segment's number · (17) SubAt at the layers' segment in front ·
(18) PlaceAt one place later · (19) NextAt one place earlier. -/
theorem k5Bite_items : ∀ g, g < 12 →
    (¬ ∀ i ∈ (openSets LF PF (start LF))[14 * (2 * g + 1) + 4]?.getD [],
      (rowOf LF ⟨1, some (2 * g + 1), 3, .K5⟩).ins.contains i = false → i ≠ .pinI →
        ∀ q ∈ tiesOf i, q = .formsInT (2 * g + 1) 2 "planes") ∧
    (¬ Pub.formsInT (2 * g + 1) 2 "objects" ∈ pubOfItems ((openSets LF PF (start LF))[14 * (2 * g + 1) + 3]?.getD [])) ∧
    (¬ ridersB LF PF (14 * (2 * g + 1) + 4) (2 * g + 3) = true) ∧
    (¬ LF[2 * g]? = some .attention) ∧
    (¬ PF[14 * (2 * g + 1) + 4 + 1]? = some ⟨1, some (2 * g + 1), 3, .K5⟩) ∧
    (¬ PF[14 * (2 * g + 1) + 4]? = some ⟨1, some (2 * g + 1), 4, .K1⟩) := by
  decide +kernel


/-! ## Each premise, in its own words -/

section
variable {g : Nat} (hg : g < 12)
include hg

/-- hD of k5_tiedR. -/
theorem doors_full : DoorsAt g := (k5Lists_doors g hg).1
/-- hD' of k5_tiedR. -/
theorem doors_full' : DoorsAt' g := (k5Lists_doors g hg).2.1
theorem hopen_full' : HopenAt' g := (k5Lists_doors g hg).2.2
/-- K5Table.openQ, and hQ of k5Fill_plus at m := 2 g + 1. -/
theorem twenty_full : TwentyAt g := (k5Lists_open g hg).1
theorem fourteen_full : FourteenAt g := (k5Lists_open g hg).2.1
/-- K5Table.tiesO at the kind's place. -/
theorem ties_full : TiesAt g := (k5Lists_items g hg).1
/-- K5Table.tiedObj. -/
theorem tiedObj_full : TiedObjAt g := (k5Lists_items g hg).2.1
theorem sub_full : SubAt g := (k5Lists_places g hg).1
theorem place_full : PlaceAt g := (k5Lists_places g hg).2.1
theorem next_full : NextAt g := (k5Lists_places g hg).2.2
/-- hQ of k5_tiedAtR_owes. -/
theorem asks_full : AsksAt g := (k5Lists_open g hg).2.2
/-- hB of k5_tiedAtR_owes. -/
theorem riders_full : RidersAt g := (k5Lists_items g hg).2.2

/-- **OpenQ, whole.** -/
theorem openQ_full : OpenQ (2 * g + 1) ((pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD []) := by
  have h := fourteen_full hg
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
    h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩

/-- K5Left.ledQ. -/
theorem ledQ_full : Pub.ledger (2 * g + 1) ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD [] := (openQ_full hg).q4
/-- K5Left.readsQ. -/
theorem readsQ_full : Pub.more (some (2 * g + 1)) "K5.readsThere" ∈ (pubSets MP LF PF)[14 * (2 * g + 1) + 4]?.getD [] :=
  (openQ_full hg).q2

end

/-- hr of k5_tiedAtR_owes. -/
theorem readsOpen_full : readsOpen LF PF (start LF) = true := k5Whole_full.1
/-- hap of k5_tiedAtR_owes. -/
theorem rowsApart_full : rowsApart LF PF = true := k5Whole_full.2

/-! ## The bridge at the kind, its three tests paid -/

section
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (get : A → P × First.S) (D : PubData) (L : Laid)
  (M : List OracleShape) (base : Pub → P × S → Bool) (cs : Codes) (Rch : ℕ → A × Fr.E.Str → Prop)

/-- **k5_tiedR at the written lists**: where the filling's list of extra tests is the written closed list (the composed filling's). -/
theorem k5_tiedR_full (hm : Mg.more = (moreOver9 {}).strike leavesName) (hpub : Mg.pub = pubAll D base) (F : Facts5 get D L M cs Rch)
    {g : ℕ} (hg : g < 12) (q : Piece C Fr A Cl W)
    (hbare : ∀ a, Rch (14 * (2 * g + 1) + 4) a → onQ N Mg LF PF get (14 * (2 * g + 1) + 4) a → (get a.1).2.failed = none → bareAttB (get a.1).2 = true)
    (hleft : ∀ a, Rch (14 * (2 * g + 1) + 4) a → onQ N Mg LF PF get (14 * (2 * g + 1) + 4) a → (get a.1).2.failed = none → leftAttB (get a.1).2 = true)
    (hs : HandsOn Rch (14 * (2 * g + 1) + 4) q)
    (h : TiedAt N (mgPlus Mg {} D L M base cs) LF PF get (14 * (2 * g + 1) + 4) q) :
    TiedAtR N Mg LF PF get Rch (14 * (2 * g + 1) + 4) q :=
  k5_tiedR N Mg LF PF get {} D L M base cs Rch hpub F _ q hbare hleft (by rw [hm]; exact doors_full hg) (by rw [hm]; exact doors_full' hg)
    (by rw [hm]; exact hopen_full' hg) hs h

end

end H2K5.Door

#print axioms H2K5.Door.k5Lists_doors
#print axioms H2K5.Door.k5Lists_open
#print axioms H2K5.Door.k5Lists_items
#print axioms H2K5.Door.k5Lists_places
#print axioms H2K5.Door.k5Lists_full
#print axioms H2K5.Door.k5Whole_full
#print axioms H2K5.Door.k5Whole_bite
#print axioms H2K5.Door.k5Bite_doors
#print axioms H2K5.Door.k5Bite_open
#print axioms H2K5.Door.k5Bite_items
#print axioms H2K5.Door.doors_full
#print axioms H2K5.Door.doors_full'
#print axioms H2K5.Door.hopen_full'
#print axioms H2K5.Door.twenty_full
#print axioms H2K5.Door.fourteen_full
#print axioms H2K5.Door.ties_full
#print axioms H2K5.Door.tiedObj_full
#print axioms H2K5.Door.sub_full
#print axioms H2K5.Door.place_full
#print axioms H2K5.Door.next_full
#print axioms H2K5.Door.asks_full
#print axioms H2K5.Door.riders_full
#print axioms H2K5.Door.openQ_full
#print axioms H2K5.Door.ledQ_full
#print axioms H2K5.Door.readsQ_full
#print axioms H2K5.Door.readsOpen_full
#print axioms H2K5.Door.rowsApart_full
#print axioms H2K5.Door.k5_tiedR_full
