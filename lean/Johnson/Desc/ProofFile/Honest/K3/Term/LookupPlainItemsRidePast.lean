-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupPlainItemsRidePast.lean: the kind "lookup" (K3): which
items ride past a lookup, and that the plain ones do, at the first chain's letters at the library's
head. Theorems and one definition; nothing is evaluated here but one control.

What is shown.
  `ItemIsPlain`: the item is "no mark" or of the five plain sorts.
  `tableRowAtALink`: at a place of a link the forward row's shuts and owes are the table's.
  `openItemIsPlainAtTheCalls`: an item open at a calls' border that the row neither shuts nor owes
    is plain.
  `openItemIsSortedAtTheDigits`: at a digits' border such an item is plain, or `wo` of the link, or
    `forms` of the link, open in the table at that border and the next.
  `sortedTestCanSayNo`: the control: the library's test on the digits' riders, asked at link 0 about
    link 1, says no.
  `plainItemGoesBack`: each plain item goes back over `SameBut`.
  `plainItemRidesPast`: each plain item rides past a lookup, on the calls or on the digits.

Hypotheses that remain. `atHead`: `P5J.AtMgA`. `linkBelow`: l < 25. `keepsGivesTheLookupClause`:
the letter f at the kind K3 implies `k3KeepsAt`. Every other letter of the thread is free, and so is
`Said`.

How the proof goes. `lookupOpenItemsAreTheTables` turns the thread's open set into the table's, where
`callsPlain_full` and `digitsSorted_full` sort the riders. Sort by sort: `unmarked_back`,
`mgAll_pile_back`, `mgAll_row_back`, `mgAll_pinW_back`, `mgAll_constr_back` (with
`P5J.k03_hHeadAll`, `P5J.k03_hD`), and at the index's pin `ansJT_rows`. All go back at every base;
`goesOn_of_back` turns them forward, at base 0.

Limits. `RidesPastAtS` is a step law from the invariant: nothing here shows that the invariant holds
at any run. Of the riders that are not plain nothing is said here but their sort. Nothing on any
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupOpenItemsWritten
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.First.Look.K3RidesDigR
import Johnson.P5J.K03RidesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.First (Item ModelPart rowOf openSets start flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT GoesBack mgAll mgBase linksFull mgAll_pile_back
  mgAll_row_back mgAll_pinW_back mgAll_constr_back)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (SameBut relOf plainSort ownSort ridersPlain ridersSorted
        plain_at_calls sorted_at_digits k3K)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.FirstRows (rows rowAt)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt goesOn_of_back strs_stay stays_mono unmarked_back)

/-- The item is "no mark" or of the five plain sorts: those that read of the state only what a
lookup leaves. -/
def ItemIsPlain (i : Item) : Prop := i = .unmarked ∨ plainSort i = true

/-- At a place of a link the forward row shuts what the table's row closes and owes what it opens
and reads. Conditional on the place's naming a link. -/
theorem tableRowAtALink (links : List ModelPart) {place : Place} {link : Nat}
    (namesLink : place.link = some link) :
    (rowAt links place).shuts = (rowOf links place).ins ∧
      (rowAt links place).owes = (rowOf links place).outs ++ (rowOf links place).ctx := by
  simp [rowAt, ProofFile.Honest.FirstRows.turn, namesLink, FwdRow.of]

/-- An item open at the calls' border that the row neither shuts nor owes is "no mark" or plain.
Conditional on the link's being below 25. -/
theorem openItemIsPlainAtTheCalls {l : Nat} (linkBelow : l < 25) {i : Item}
    (opened : i ∈ fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (borderOf l false))
    (notShut : i ∉ (rows P5J.At.links P5J.At.ps (borderOf l false)).shuts)
    (notOwed : i ∉ (rows P5J.At.links P5J.At.ps (borderOf l false)).owes) :
    ItemIsPlain i := by
  obtain ⟨placeIsWritten, pieceIsLow⟩ := VerifiableInference.OnPublicFiles.k3Border_calls linkBelow
  have plain := plain_at_calls placeIsWritten rfl pieceIsLow
  rw [lookupOpenItemsAreTheTables linkBelow false] at opened
  have one := List.all_eq_true.1 plain i opened
  have rowIs : rows P5J.At.links P5J.At.ps (borderOf l false) =
      rowAt P5J.At.links (IM.k3Place l false) := by
    unfold rows
    rw [show P5J.At.ps[borderOf l false]? = some (IM.k3Place l false) from placeIsWritten]
    rfl
  rw [rowIs] at notShut notOwed
  obtain ⟨shutsAre, owesAre⟩ := tableRowAtALink P5J.At.links (place := IM.k3Place l false)
    (link := l) rfl
  rw [shutsAre] at notShut
  rw [owesAre] at notOwed
  rw [placeIsWritten] at one
  have one' : (((rowOf P5J.At.links (IM.k3Place l false)).ins ++
      (rowOf P5J.At.links (IM.k3Place l false)).ctx ++ [Item.unmarked]).contains i ||
      plainSort i) = true := one
  rcases (Bool.or_eq_true _ _).mp one' with listed | plainItem
  · have listed' := List.contains_iff_mem.1 listed
    simp only [List.mem_append, List.mem_singleton] at listed'
    rcases listed' with (closes | reads) | isUnmarked
    · exact absurd closes notShut
    · exact absurd (List.mem_append_right _ reads) notOwed
    · exact Or.inl isUnmarked
  · exact Or.inr plainItem


set_option maxRecDepth 100000 in
/-- A control: the library's test on the digits' riders, asked at link 0 about link 1, says no. No
premise: a closed fact, by the kernel. -/
theorem sortedTestCanSayNo :
    ridersSorted linksFull (flatPlacesOf linksFull true) (borderOf 0 true) 1 = false := by
  decide +kernel

/-- An item open at a digits' border that the row neither shuts nor owes is plain, or the link's
`wo`, or one of the link's `forms` that the table holds open at that border and the next.
Conditional on the link's being below 25. -/
theorem openItemIsSortedAtTheDigits {l : Nat} (linkBelow : l < 25) {i : Item}
    (opened : i ∈ fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (borderOf l true))
    (notShut : i ∉ (rows P5J.At.links P5J.At.ps (borderOf l true)).shuts)
    (notOwed : i ∉ (rows P5J.At.links P5J.At.ps (borderOf l true)).owes) :
    ItemIsPlain i ∨ i = .wo l ∨ ∃ kk ρ, i = .forms l kk ρ ∧
      i ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true) ∧
      i ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true + 1) := by
  obtain ⟨placeIsWritten, pieceIsHigh⟩ := VerifiableInference.OnPublicFiles.k3Border_digits linkBelow
  have sorted := sorted_at_digits placeIsWritten rfl pieceIsHigh rfl
  have forwardOpened := opened
  rw [lookupOpenItemsAreTheTables linkBelow true] at opened
  have one := List.all_eq_true.1 sorted i opened
  have rowIs : rows P5J.At.links P5J.At.ps (borderOf l true) =
      rowAt P5J.At.links (IM.k3Place l true) := by
    unfold rows
    rw [show P5J.At.ps[borderOf l true]? = some (IM.k3Place l true) from placeIsWritten]
    rfl
  have stillOpen : i ∈ fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps)
      (borderOf l true + 1) := by
    show i ∈ fwdStep _ _
    unfold fwdStep
    exact List.mem_append_left _ (List.mem_filter.2 ⟨forwardOpened, by
      simpa using notShut⟩)
  rw [lookupOpenItemsBehindTheDigitsAreTheTables linkBelow] at stillOpen
  rw [rowIs] at notShut notOwed
  obtain ⟨shutsAre, owesAre⟩ := tableRowAtALink P5J.At.links (place := IM.k3Place l true)
    (link := l) rfl
  rw [shutsAre] at notShut
  rw [owesAre] at notOwed
  rw [placeIsWritten] at one
  have one' : (((rowOf P5J.At.links (IM.k3Place l true)).ins ++
      (rowOf P5J.At.links (IM.k3Place l true)).ctx ++ [Item.unmarked]).contains i ||
      (plainSort i || ownSort l i)) = true := one
  rcases (Bool.or_eq_true _ _).mp one' with listed | sortedItem
  · have listed' := List.contains_iff_mem.1 listed
    simp only [List.mem_append, List.mem_singleton] at listed'
    rcases listed' with (closes | reads) | isUnmarked
    · exact absurd closes notShut
    · exact absurd (List.mem_append_right _ reads) notOwed
    · exact Or.inl (Or.inl isUnmarked)
  · rcases (Bool.or_eq_true _ _).mp sortedItem with plainItem | ownItem
    · exact Or.inl (Or.inr plainItem)
    · right
      cases i with
      | wo m =>
        left
        have e : m = l := by simpa [ownSort] using ownItem
        rw [e]
      | forms m kk ρ =>
        right
        have e : m = l := by simpa [ownSort] using ownItem
        subst e
        exact ⟨kk, ρ, rfl, opened, stillOpen⟩
      | _ => simp [ownSort] at ownItem

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- **Each plain item goes back over the same-but, at the honest letters.** Conditional on the head
and on the item's sort. -/
theorem plainItemGoesBack (base : Nat) (input : Local W₀ Rc ProofFile.Inst Tr) {i : Item}
    (plainOrUnmarked : ItemIsPlain i) :
    GoesBack (relOf SameBut base) (i.holds (LK).N ((LK).mg input)) := by
  rcases plainOrUnmarked with rfl | plainItem
  · exact unmarked_back _ _ base
  · cases i with
    | pile =>
      exact mgAll_pile_back { atHead.𝔇 with decT := fun _ _ => some (Q.cells input), cr1 := carryX }
        mgBase base
    | row m c =>
      exact mgAll_row_back { atHead.𝔇 with decT := fun _ _ => some (Q.cells input), cr1 := carryX }
        mgBase base m c
    | pinW =>
      exact mgAll_pinW_back { atHead.𝔇 with decT := fun _ _ => some (Q.cells input), cr1 := carryX }
        mgBase base (fun _ _ _ _ _ => rfl)
    | constr m p =>
      refine mgAll_constr_back
        { atHead.𝔇 with decT := fun _ _ => some (Q.cells input), cr1 := carryX } mgBase base
        (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) m p ?_ (P5J.k03_hHeadAll atHead base p)
      have digitsPartIs := P5J.k03_hD atHead
      show GoesBack (relOf SameBut base) ((atHead.toAtMg.𝔇 atHead.𝔇).digitsPart m)
      rw [digitsPartIs]
      exact fun _ _ _ _ _ _ said => said
    | pinI =>
      rintro ⟨z, front⟩ y ⟨z', behind⟩ y' v ⟨-, same, -⟩ said
      exact ProofFile.Honest.ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
        (y := y') (y' := y) (fun _ _ _ => by rw [same.st]) said
    | _ => simp [plainSort] at plainItem

/-- **Each plain item rides past a lookup, on the calls or on the digits.** Conditional on the head,
the link and the arrow from the letter f to the lookups' clause. -/
theorem plainItemRidesPast (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {l : Nat}
    (linkBelow : l < 25) (digits : Bool) {i : Item} (itemIsPlain : ItemIsPlain i) :
    RidesPastAtS (LK).thread Said (borderOf l digits) i := by
  intro k s m E s' ps v _ keeps said
  have same := lookupClauseGivesSameBut atHead linkBelow digits
    (keepsGiveTheLookupClauseAtTheBorder atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w
      keepsGivesTheLookupClause linkBelow digits keeps)
  exact goesOn_of_back
    (plainItemGoesBack atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w 0 m.st.input itemIsPlain)
    ((LK).thread.seat k m s) _ ((LK).thread.seat k m s') _ v ⟨rfl, same, stays_mono (strs_stay item n₁ n₂ E ps) (Nat.zero_le _)⟩ said

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.tableRowAtALink
#print axioms ProofFile.Honest.K3.Term.openItemIsPlainAtTheCalls
#print axioms ProofFile.Honest.K3.Term.sortedTestCanSayNo
#print axioms ProofFile.Honest.K3.Term.openItemIsSortedAtTheDigits
#print axioms ProofFile.Honest.K3.Term.plainItemGoesBack
#print axioms ProofFile.Honest.K3.Term.plainItemRidesPast
