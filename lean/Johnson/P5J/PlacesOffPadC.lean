-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PlacesOffPadC.lean: A TEST WITH CODE FOR `PlacesOffPad` (HidBears.lean) AT THE SEATS OFF
    THE LAYOUT, AND "H DOES NOT READ THE PADS" IN THE TABLE'S OWN WORDS ON A WITNESS'S COMPONENTS.
  `placesOffC`: for every entry of the 25 lists: the array that its label names is there in the
      layout, and every copy of its
    message in the segment's own group has a shape at which the array misses the pad:
        `copiesMiss`
    (Johnson/Desc/Kinds/Law/PadFreeByBlocks.lean), ONE TEST AN ENTRY, by the array's laid blocks.
        `padsFreeC` asks the like
    at the 24 seams alone.
  **`placesOffPad_of_C`**: laidThere · placesOffC · "no matrix from segment 25 on" ⟹ PlacesOffPad …
      (seatBy (fLay layout num) X s).
  **`hid_bears_turn`**: two witnesses that agree in every component but the pads of a list L (the
      table's `Comp`, `sameQ`) have the same
    hidden values and the same "packing of small integers" , segment by segment. ITS PREMISE is, to
        the token, the body of
    PadsTurn L w w'; ITS END IS STRONGER than the named premise HidBears H L m asks
        (there: the token, and from
    segment m on the packing and that segment's matrices): that follows by rewriting.
Limits. The test has run nowhere.
    (Where this and lean/THEOREM.md differ, the page
    holds.) A rule over letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.HidBears
import Johnson.Desc.Kinds.Law.PadFreeByBlocks
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Params (ReqArray ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit laidAt arrayOf)
open VerifiableInference.Desc.First (Numbers Comp)
open VerifiableInference.Desc.Sound (Mem MsgT OffPad SeatsNamed GroupsSeated sameQ)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (copiesMiss offPad_of_miss)

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- **The test: one `copiesMiss` an entry of the 25 lists.** -/
def placesOffC : Bool :=
  (List.range 25).all fun k => (List.range (s k).NM).all fun a =>
    match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
    | none => false
    | some A => copiesMiss cs arr ms N k (num (ownerK (labAt X k a)) A.message) A

variable {cs arr ms N X s layout num}

/-- **An accept of the test gives the condition.** -/
theorem placesOffPad_of_C (T : laidThere X s layout = true)
    (h : placesOffC cs arr ms N X s layout num = true) (hK : ∀ k, 25 ≤ k → (s k).NM = 0) :
    PlacesOffPad cs arr ms N s (seatBy (fLay layout num) X s) := by
  intro k μ r c hr hc
  by_cases hk : k < 25
  · obtain ⟨A, x, hA, -, -, hl, hs⟩ := seat_of_laidThere T num hk μ hr hc
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 h k (List.mem_range.2 hk)) μ.val
      (List.mem_range.2 μ.isLt)
    simp only [hA] at h1
    rw [hs]
    exact offPad_of_miss cs arr ms N h1 hl
  · exact absurd (hK k (by omega) ▸ μ.isLt : μ.val < 0) (Nat.not_lt_zero _)

end

/-- **H DOES NOT READ THE PADS, IN THE TABLE's WORDS ON COMPONENTS.** L: whichever pads may differ.
    -/
theorem hid_bears_turn {Cells Tok : Type} {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
    {N : Numbers} {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    (X : Model.Verify.Public) {P : Type} {rows cols : ℕ} (tokV : Tok → Fin ppref.V)
    (req : P × TS → TReq) (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE))
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N)
    (hO : PlacesOffPad cs arr ms N s seat) (L : List (ℕ × ℕ)) (w w' : Wit Cells Tok MsgT)
    (h : ∀ c : Comp, (∀ x ∈ L, c ≠ .pad x.1 x.2) → sameQ c w w') :
    (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).hid w' =
        (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).hid w ∧
      ∀ j, (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).base j w' ↔
        (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).base j w :=
  hid_bears X tokV req dec hN hG hO w w'
    (funext fun n => (h (.msg n) fun _ _ => Comp.noConfusion).symm)
    (h .tok fun _ _ => Comp.noConfusion).symm

end P5J

#print axioms P5J.placesOffPad_of_C
#print axioms P5J.hid_bears_turn
