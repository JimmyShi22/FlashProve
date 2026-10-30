-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DigitsRow.lean: THE TABLE's TWO ROWS AT THE DIGITS' LOOKUP's PLACE. Facts on the
table alone; cut out of Johnson/Desc/Sound/K3AtDriver.lean so that a kind's files
can call them without the driver's cone. NO RESULT ON THE PROTOCOL.

What is said.
  `rowQ_at`: the row of block number k is the row of the place that stands at k.
  `digits_row`, `digits_asks`: at the digits' lookup's place the table's row closes, opens and reads
    just what the lookup's files' theorem takes as premises; and its row in the promise's table
    asks four items: the ledger, `lookIn`, `linkFresh`, `freeAbove`.
  `digits_lookIn_open`: so where `pubFit` says yes (at a filling M of the table's door), the four
    are open in front.

Limits. Nothing is said of any block. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.OnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Model (Aff)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Pub start segRow shift pubRowOf pubFit
  pubRowM pubStartM More)

/-- The row of block number k is the row of the place that stands at k. -/
theorem rowQ_at (links : List ModelPart) (ps : List Place) (k : ℕ) (a : Place) (h : ps[k]? = some a) :
    rowQ links ps k = First.rowOf links a := by
  unfold rowQ
  rw [h]
  rfl

/-- **The table's row at the digits' lookup's place.** -/
theorem digits_row (links : List ModelPart) (a : Place) (i : ℕ) (sub : ModelPart) (hl : a.link = some i)
    (hs : links[i]? = some sub) (hpc : a.piece = 7 + shift sub) :
    (First.rowOf links a).ins = [.constr i .lookDigits] ∧
      (First.rowOf links a).outs = [.forms i (7 + shift sub) "objects",
        .worth i (7 + shift sub) "planes", .worth i (7 + shift sub) "keys"] ∧
      (First.rowOf links a).ctx = [.pin i 2, .pin i 0, .pin i 1] := by
  cases sub <;> simp [First.rowOf, segRow, shift, hl, hs, hpc]

/-- What the promise's table asks in front of it. -/
theorem digits_asks (links : List ModelPart) (a : Place) (i : ℕ) (sub : ModelPart) (hl : a.link = some i)
    (hs : links[i]? = some sub) (hpc : a.piece = 7 + shift sub) :
    (pubRowOf links a).asks =
      [.ledger i, .lookIn i (7 + shift sub), .linkFresh i, .freeAbove i] := by
  cases sub <;> simp [pubRowOf, shift, hl, hs, hpc]

/-- So where the test on the promise's table says yes, `lookIn` is open in front of the block. -/
theorem digits_lookIn_open (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (a : Place)
    (i : ℕ) (sub : ModelPart) (hfit : pubFit M links ps = true) (hk : ps[k]? = some a)
    (hl : a.link = some i) (hs : links[i]? = some sub) (hpc : a.piece = 7 + shift sub) :
    ∀ x ∈ [Pub.ledger i, .lookIn i (7 + shift sub), .linkFresh i, .freeAbove i],
      x ∈ pubQ M links ps k := fun x hx =>
  asks_open (pubRowM M links) ps (pubStartM M) k a hfit hk x
    (List.mem_append_left _ (by rw [digits_asks links a i sub hl hs hpc]; exact hx))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowQ_at
#print axioms VerifiableInference.Desc.Sound.digits_row
#print axioms VerifiableInference.Desc.Sound.digits_asks
#print axioms VerifiableInference.Desc.Sound.digits_lookIn_open
