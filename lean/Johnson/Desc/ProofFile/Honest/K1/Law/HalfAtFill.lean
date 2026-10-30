-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HalfAtFill.lean: THE SHARED "SENDING" (the kind K1): THE SIDE
THAT THE PROVER OF onlineProverFromPublicFiles HOLDS AT K1's 51 PLACES IN THE SEGMENTS, AT A FILLING THAT IS A LETTER:
WHEREVER THE FILLING HOLDS K1's LOT AND EVERY OTHER LOT's HALVES STAND AT PLACES OF OTHER KINDS, OR
BEHIND THE SEGMENTS. Three theorems; no definition.

THE PREMISES, THE SAME IN ALL THREE: hA: onlineProverFromPublicFiles returns A at the three files, at the filling P: P IS
A LETTER · wit, no, Dt: THREE LETTERS: the reader of a place's input, the number that a place's
first new message gets, the data of the main rows · hex: SOME LOT OF P.lots HAS, AT A's PUBLIC PART
AND GROUND, THE HALVES OF K1's LOT (lotHalves wit no Dt, Honest/K1/PlaceJob.lean) · ho: EVERY LOT OF
P.lots HAS THERE THESE HALVES, OR HALVES OF WHICH EACH THAT STANDS AT A PLACE OF THE KIND K1 STANDS
AT ONE THAT BEARS NO LINK. WHY SO AND NOT "AT PLACES OF OTHER KINDS ALONE": W's sending is of the
kind K1 too, at the place (1, none, 4, K1), behind the segments; its side is no half of K1's lot: at
a filling that holds it as a lot of its own a premise by the kind alone would fail, and these laws
would say nothing there. K1's 51 places in the segments each bear a link.

  - k1_first_fill: the side found at the first segment's opening IS placeHalf wit at the opening's
    job.
  - k1_reads_fill, k1_digits_fill: at a built segment's reads and digits (hX, hN: the segment and
    its numbers): the like.

Why. H2's k1_first_wider, k1_reads_wider, k1_digits_wider (Honest/Thread/FirstFillK1At.lean: NOT
IMPORTED HERE) say this at the filling widerFillAt, under WiderKinds. A law that is nailed to one
filling does not carry over to a wider one. These do: the form is that of another house's law on its
own kind (hA, hex, ho).

The road. ProofFile's atPure_first_find (Honest/FirstFind.lean), which goes by the place; H2's
k1_find_first, k1_find_reads, k1_find_digits (Honest/Thread/K1Finds.lean), which are general in wit,
no and the data.

Limits. THAT onlineProverFromPublicFiles RETURNS, hex AND ho ARE PREMISES: PROVED HERE OF NO FILLING. W's sending is not
here: K1's lot has no side at it. An equation between two texts of a side, found by place: it names
no input and no run. It stands over files of ProofFile's and of H2's that are on no seal. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.FirstFind
import Johnson.Desc.ProofFile.Honest.Thread.K1Finds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Place)
open OnBytes.Model.Stages (LinkH)

variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
  (wit : Local W₀ Rc Inst Tr → PlaceIn Inst) (no : Place → Nat)
  (Dt : Pub → Ground → RowDataOf Inst)
  (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
  (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
    M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
include hA hex ho

/-- **THE SIDE THAT IS FOUND AT THE FIRST SEGMENT's OPENING**, at a filling that holds K1's lot. -/
theorem k1_first_fill :
    A.H.first.find? (fun g => g.place == ⟨1, some 0, 1, .K1⟩) =
      some (placeHalf wit (placeJob (K1.firstPar A.G.first (K1.gpOf A.Z))
        (no ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first) (Dt A.Z A.G))) := by
  obtain ⟨M, hM, eM⟩ := hex
  refine atPure_first_find hA hM (fun M' hM' => ?_)
    (by rw [eM]; exact FirstFill.k1_find_first wit no Dt A.Z A.G)
  rw [eM]
  refine (ho M' hM').imp_left fun hk x hx e => ?_
  have q := hk x hx (by rw [e])
  rw [e] at q
  cases q

variable {l pr pd : Nat} {Y : LinkH} {r d : Option (List Nat)}

/-- **AT A BUILT SEGMENT's READS.** -/
theorem k1_reads_fill (hX : A.G.built[l]? = some Y)
    (hN : K1.linkNumbers A.G Y = some (pr, pd, r, d)) :
    A.H.first.find? (fun g => g.place == ⟨1, some l, pr, .K1⟩) =
      some (placeHalf wit (laterJobAt A.G.first (K1.gpOf A.Z) l pr 1
        (no ⟨1, some l, pr, .K1⟩) (Dt A.Z A.G))) := by
  obtain ⟨M, hM, eM⟩ := hex
  refine atPure_first_find hA hM (fun M' hM' => ?_)
    (by rw [eM]; exact FirstFill.k1_find_reads wit no Dt A.Z A.G hX hN)
  rw [eM]
  refine (ho M' hM').imp_left fun hk x hx e => ?_
  have q := hk x hx (by rw [e])
  rw [e] at q
  cases q

/-- **AT A BUILT SEGMENT's DIGITS.** -/
theorem k1_digits_fill (hX : A.G.built[l]? = some Y)
    (hN : K1.linkNumbers A.G Y = some (pr, pd, r, d)) :
    A.H.first.find? (fun g => g.place == ⟨1, some l, pd, .K1⟩) =
      some (placeHalf wit (laterJobAt A.G.first (K1.gpOf A.Z) l pd 2
        (no ⟨1, some l, pd, .K1⟩) (Dt A.Z A.G))) := by
  obtain ⟨M, hM, eM⟩ := hex
  refine atPure_first_find hA hM (fun M' hM' => ?_)
    (by rw [eM]; exact FirstFill.k1_find_digits wit no Dt A.Z A.G hX hN)
  rw [eM]
  refine (ho M' hM').imp_left fun hk x hx e => ?_
  have q := hk x hx (by rw [e])
  rw [e] at q
  cases q

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_first_fill
#print axioms ProofFile.Honest.K1.k1_reads_fill
#print axioms ProofFile.Honest.K1.k1_digits_fill
