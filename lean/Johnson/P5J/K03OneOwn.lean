-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OneOwn.lean: THE LOOKUP ARGUMENT's LAW: ITS TWO PREMISES "one" AND "own" AT EVERY
ELEMENT, FROM TESTS WITH CODE THAT WALK THE ENTRIES OF A LINK's LIST, NOT THEIR ELEMENTS. Two
definitions with code; three theorems, proved.

  `oneB`: at every entry μ of link k's list: the array A that the entry's label names is there;
    where the place `idx n` of its number n := num o A.message lies in the calls' list: the list's
    entry has THE SHAPE OF THE ORACLE MESSAGE THAT A NAMES, and the seat at that place bears the
    number wn n.
  `namedB`: at every entry: the array is there and just one tenant of link k's group bears the
    number n: "own"'s first half. ITS SECOND HALF (off the pad, at every member of that number) HAS
    ITS TEST AND ITS THEOREM ALREADY: `P5J.placesOffC` | `placesOffPad_of_C`
    (Johnson/P5J/PlacesOffPadC.lean, over `copiesMiss`): no twin is typed here.
  `fLay_number`: under the test `laidThere`, within the sizes: `fLay layout num (labAt X k μ)
    i c = (num o A.message, x.1, x.2)`, A the array that the label names, `laidAt A i c = some x`:
    SO AN ELEMENT's NUMBER DOES NOT HANG ON (i, c). (`seat_of_laidThere`,
    Johnson/Goal/Meaning/HidSeatsOf.lean, with `seatBy` unfolded.)
  `oneNumber_of_B`: k < 25 · laidThere · the programs' three tests on codes, shape and layout ·
    `oneB … = true` give `OneNumber` (Johnson/Desc/First/Look/K3CopiesOne.lean) AT EVERY ELEMENT:
    the pad's clause by `laidAt_inside` (Johnson/Goal/Meaning/LaidInside.lean) at the
    shape of the message that the array names.
  `ownNamed_of`: k < 25 · laidThere · `namedB … = true` · `PlacesOffPad` give `OwnNamed`
    (K3CopiesRead.lean), both halves, at every element.
CAN THE PREMISES BE MET? BY A RUN, at a stored full-size set's three public files, at the terms of
the composed meaning's parameters: oneB accepted at all 24 links in front of the head's (the 24
entries whose array another link owns among them), and rejected at all 24 with arr, or with idx, one
higher. namedB: not yet asked by a run under its name when this head was written.
(Where this and lean/THEOREM.md differ, the page
holds.)
Limits. Nothing at the digits. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3CopiesRead
import Johnson.Goal.Meaning.LaidInsideSeats
import Johnson.P5J.PlacesOffPadC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.K03
open OnBytes OnBytes.Model
open VerifiableInference.Desc (arrayOf laidAt)
open OnBytes.Params (ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf)
open VerifiableInference.Desc.Sound (Mem namedOnce)
open VerifiableInference.OnPublicFiles (OneNumber OwnNamed)
open _root_.Meaning (labAt ownerK ownerA nameOf messageAt fLay seatBy laidThere seat_of_laidThere
  laidAt_inside arrayOf_mem)

def oneB (X : Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ)
    (tls : ℕ → HTailF2) (k : ℕ) (st : ℕ → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (wn : ℕ → ℕ) : Bool :=
  (List.range (szOf (tls k)).NM).all fun μ =>
    match arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
    | none => false
    | some A =>
      match (sigListCalls D rad k)[idx (num (ownerK (labAt X k μ)) A.message)]?,
          messageAt D.shape (ownerK (labAt X k μ)) A.message with
      | some e, some m => e.1 == m.shape &&
          arr (st (idx (num (ownerK (labAt X k μ)) A.message))).1
            (st (idx (num (ownerK (labAt X k μ)) A.message))).2 ==
            wn (num (ownerK (labAt X k μ)) A.message)
      | some _, none => false
      | none, _ => true

def namedB (X : Verify.Public) (D : Sent) (num : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2) (k : ℕ)
    (arr : ℕ → ℕ → ℕ) (N : Numbers) : Bool :=
  (List.range (szOf (tls k)).NM).all fun μ =>
    match arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
    | none => false
    | some A => namedOnce arr N k (num (ownerK (labAt X k μ)) A.message)

/-- **An element's number does not hang on the element.** -/
theorem fLay_number {X : Verify.Public} {s : ℕ → Size} {layout : ReqLayout}
    (T : laidThere X s layout = true) (num : ℕ → ℕ → ℕ) {k : ℕ} (hk : k < 25) {μ : ℕ}
    (hμ : μ < (s k).NM) {i c : ℕ} (hi : i < Alg.symRows ((s k).m μ)) (hc : c < (s k).k μ) :
    ∃ A x, arrayOf layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) = some A ∧
      laidAt A i c = some x ∧
      fLay layout num (labAt X k μ) i c = (num (ownerK (labAt X k μ)) A.message, x.1, x.2) := by
  obtain ⟨A, x, hA, -, -, hl, hs⟩ := seat_of_laidThere T num hk ⟨μ, hμ⟩ hi hc
  exact ⟨A, x, hA, hl, hs⟩

section
variable {X : Verify.Public} {D : Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ}
  {tls : ℕ → HTailF2} {k : ℕ} {st : ℕ → ℕ × ℕ} {arr : ℕ → ℕ → ℕ} {wn : ℕ → ℕ}

/-- **"one", at every element, from a test that walks the entries.** -/
theorem oneNumber_of_B (hk : k < 25)
    (T : laidThere X (fun j => szOf (tls j)) D.layout = true)
    (hC : D.codes.lengthsOk = true) (hS : reqShapeOk D.shape = true)
    (hL : reqLayoutOk D.codes D.shape D.layout = true)
    (hB : oneB X D rad num idx tls k st arr wn = true) :
    OneNumber X D rad num idx tls k (fun j => st j.1) arr wn := by
  intro μ i c hμ hi hc
  obtain ⟨A, x, hA, hl, hs⟩ := fLay_number (s := fun j => szOf (tls j)) T num hk hμ hi hc
  rw [hs]
  intro hk'
  obtain ⟨as, hla, hmem⟩ := arrayOf_mem hA
  obtain ⟨m, hm, -, -, hpad⟩ := laidAt_inside hC hS hL hla hmem (r := x.1) (p := x.2) hl
  have h1 := List.all_eq_true.1 hB μ (List.mem_range.2 hμ)
  have he : (sigListCalls D rad k)[idx (num (ownerK (labAt X k μ)) A.message)]? =
      some ((sigListCalls D rad k).get ⟨idx (num (ownerK (labAt X k μ)) A.message), hk'⟩) :=
    List.getElem?_eq_getElem hk'
  simp only [hA, he, hm, Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1 ▸ hpad, h1.2⟩

/-- **"own", both halves, at every element.** -/
theorem ownNamed_of {ms : List Mem} {N : Numbers} (hk : k < 25)
    (T : laidThere X (fun j => szOf (tls j)) D.layout = true)
    (hB : namedB X D num tls k arr N = true)
    (hO : PlacesOffPad D.codes arr ms N (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))) :
    OwnNamed X D num tls k arr ms N := by
  intro μ i c hμ hi hc
  refine ⟨?_, hO k ⟨μ, hμ⟩ i c hi hc⟩
  obtain ⟨A, x, hA, -, hs⟩ := fLay_number (s := fun j => szOf (tls j)) T num hk hμ hi hc
  rw [hs]
  have h1 := List.all_eq_true.1 hB μ (List.mem_range.2 hμ)
  simp only [hA] at h1
  exact h1

end

end P5J.K03

#print axioms P5J.K03.fLay_number
#print axioms P5J.K03.oneNumber_of_B
#print axioms P5J.K03.ownNamed_of
