-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchPartsEntry.lean: the kind "the code switch" (K2): WHAT
THE PARTS THAT THE KIND's ONE LOT LAYS READ OF THE PROVER's INPUT, THE DATA A LETTER. The part has
one door to the input: `switchWit` (Honest/K2/Half.lean): it reads the public instance, to which the
filling D is applied, and the readers; and the readers are handed to one function alone:
`RowData.at_` (Honest/RowData.lean), which reads them through the filling's field `entry`. SO EACH
MOVE OF EACH PART OF EACH OF THE LOT's HALVES SAYS AND HANDS THE SAME AT TWO INPUTS WITH ONE
INSTANCE AT WHOSE READERS THE FILLING's `entry` IS ONE. A FACT ON TEXTS, AS EQUATIONS BETWEEN VALUES
OF FUNCTIONS AT TWO INPUTS. Six theorems; no definition. The form is that of
Honest/K1/Law/LotPartsCells.lean, for the kind K1.

  `at_of_entry, ownBy_of_entry` where a filling's `entry` is one at two readers, so are the one call
                    `RowData.at_` and `ownBy` (Honest/K2/AtPlan.lean)
  `switchWit_of_entry` THE DOOR, the closing a letter: one instance, one `entry`, and the closing
                    one at the two readers: what the part reads is one
  `switchHalf_of_wit` where what the part reads is one, each move of the half's one part says and
                    hands the same at two states that part in the input alone
  `switchLot_of_entry` SO AT EACH OF THE LOT's HALVES, at the lot's own closing
  `switchLot_stops_none` A PART HAS TWO ROADS TO THE INPUT: its moves' states, and its second stop
                    `hid`, which is handed V. THE SECOND ROAD IS SHUT: the half lifts a part whose V
                    is `Unit`, and at each part both stops answer nothing at every argument,
                    whatever the data

Limits. EQUATIONS ON WHAT FUNCTIONS RETURN: nothing on any run, on what a view holds, or on any
property. Which fields of the readers a filling's `entry` reads is not said here. The part's coins,
own and carried, are no part of the input: they are a move's first argument, which is the same
letter on both sides. The part's other five fields (takes, spends, carries, badShare, hidShare) are
no functions of an input, by type.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

variable {W₀ Rc Xi Tr X : Type}

/-- The one call reads the readers through `entry` alone. -/
theorem at_of_entry (D : RowData) {R R' : Readers} (h : D.entry R = D.entry R') :
    D.at_ R = D.at_ R' := by
  funext hd a r j
  unfold RowData.at_
  rw [h]

/-- So do the main rows of the segments' own messages, as the lot's closing reads them. -/
theorem ownBy_of_entry (D : RowData) {R R' : Readers} (h : D.entry R = D.entry R')
    (addrs : Nat → Nat → Option MsgAddr) (shapes : Nat → Nat → OnBytes.OracleShape)
    (heard : List Fmt.Drawn) : ownBy D R addrs shapes heard = ownBy D R' addrs shapes heard := by
  funext seg m b j
  unfold ownBy
  rw [at_of_entry D h]

/-- **THE DOOR**: what the part reads of the prover's input; the closing a letter. -/
theorem switchWit_of_entry (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) {i i' : Local W₀ Rc Xi Tr} (hx : i.x = i'.x)
    (hD : (D i'.x).entry (readers i) = (D i'.x).entry (readers i'))
    (hc : closing p (D i'.x) (readers i) = closing p (D i'.x) (readers i')) :
    switchWit D readers closing p i = switchWit D readers closing p i' := by
  unfold switchWit
  rw [hx, hc, at_of_entry _ hD]

/-- **THE PART READS OF ITS INPUT WHAT THE DOOR HANDS IT, AND NOTHING ELSE.** -/
theorem switchHalf_of_wit (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    {i i' : Local W₀ Rc Xi Tr}
    (hw : switchWit D readers closing p i = switchWit D readers closing p i') :
    ∀ q ∈ (switchHalf (X := X) Sd D readers closing p).parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  intro q hq mv hmv heard own
  obtain rfl : q = _ := List.mem_singleton.1 hq
  obtain ⟨m0, -, rfl⟩ := List.mem_map.1 hmv
  refine ⟨fun c s => ?_, rfl⟩
  show m0.say c s ⟨switchWit D readers closing p i, heard, ()⟩ =
    m0.say c s ⟨switchWit D readers closing p i', heard, ()⟩
  rw [hw]

/-- **EACH MOVE OF EACH PART OF EACH OF THE LOT's HALVES**, the data and the readers letters. -/
theorem switchLot_of_entry (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (Z : Pub)
    (G : Ground) {i i' : Local W₀ Rc Xi Tr} (hx : i.x = i'.x)
    (hD : (D i'.x).entry (readers i) = (D i'.x).entry (readers i')) :
    ∀ g ∈ (switchLot (X := X) D readers).halves Z G, ∀ q ∈ g.parts, ∀ mv ∈ q.moves,
      ∀ (heard : List Fmt.Drawn) (own : X),
        (∀ c s, mv.say c s ⟨i, heard, own⟩ = mv.say c s ⟨i', heard, own⟩) ∧
          mv.hand ⟨i, heard, own⟩ = mv.hand ⟨i', heard, own⟩ := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 (show g ∈ (switchPlaces Z G).map _ from hg)
  exact switchHalf_of_wit _ D readers _ p (switchWit_of_entry D readers _ p hx hD (by
    funext heard k
    simp only [ownBy_of_entry (D i'.x) hD]))

/-- **THE SECOND ROAD IS SHUT**: at each part of each of the lot's halves both stops answer nothing,
at every argument, whatever the data and the readers. -/
theorem switchLot_stops_none (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (Z : Pub)
    (G : Ground) :
    ∀ g ∈ (switchLot (X := X) D readers).halves Z G, ∀ q ∈ g.parts,
      (∀ v a b, q.hid v a b = none) ∧ ∀ a b, q.bad a b = none := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 (show g ∈ (switchPlaces Z G).map _ from hg)
  intro q hq
  obtain rfl : q = _ := List.mem_singleton.1 hq
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.at_of_entry
#print axioms ProofFile.Honest.K2.Law.ownBy_of_entry
#print axioms ProofFile.Honest.K2.Law.switchWit_of_entry
#print axioms ProofFile.Honest.K2.Law.switchHalf_of_wit
#print axioms ProofFile.Honest.K2.Law.switchLot_of_entry
#print axioms ProofFile.Honest.K2.Law.switchLot_stops_none
