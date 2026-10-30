-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSplit.lean: THE BATCHING's STEP ON SHAPES (`batchGS`, BatchAtHead.lean)
CUT BETWEEN TWO OF ITS RUNS OF CLAIMS: `batchFrontG` (the draw, the guard behind it, the gathering
over the first runs) AND `batchBackG` (the gathering over the rest, the adding, the test on the
mark); AND THE STEP IS THE ONE, THEN THE OTHER: `batchGS_split`, `batchGS_cut`. No premise. Three
definitions, three theorems. General; nothing is evaluated.

Purpose. At an attention link the whole step was too dear for Lean's kernel in one line of a
bearable size (timed trials; not shown here). The gathering (`gatherFrom`,
Johnson/Desc/First/Batch/Shape/BatchFold.lean) already carries what is gathered so far as its state:
a list of claims' shapes and the chain's shape. So the step can be shown in two pieces with that
state written between them.

Main names.
* **`gatherFrom_append`**: gatherFrom k g (o₁ ++ o₂) x = (gatherFrom k g o₁ x).bind (gatherFrom k g
  o₂).
* `batchFrontG k g rows o₁ a`, `batchBackG k g o₂ y`: the lines of batchGS, batchG, addsG and
  gatherG (BatchAtHead.lean; Batch/Shape/BatchMember.lean; BatchFold.lean), regrouped. (The short
  names frontG and backG are K4's two runs on shapes: not these.)
* **`batchGS_split`**: batchGS rows k g (o₁ ++ o₂) a = (batchFrontG k g rows o₁ a).bind (batchBackG
  k g o₂). **`batchGS_cut`**: the same at a whole order, cut behind its first j runs: j is a letter.
* `batchBackGL`: a pair: batchBackG with the adding's second text (`addListS_eq`,
  Batch/Shape/AddLight.lean), made by Lean, and the tie.

Limits. Equalities of functions. batchBackGL's second text can be read nowhere here: `#print` shows
it. What either half costs is not said. Nothing says that a step returns. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchAtHead
import Johnson.Desc.First.Batch.Shape.AddLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape (ChainSh ClaimSh)
open VerifiableInference.Desc.K9 (SegSort)
open VerifiableInference.Desc.K9.Shape

section
variable (k : SegSort)
  (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))

/-- **The gathering over two lists of runs, one behind the other, is the gathering over the first,
then over the second from what the first has gathered.** -/
theorem gatherFrom_append : ∀ (o₁ o₂ : List (Nat × String)) (x : List ClaimSh × ChainSh),
    gatherFrom k g (o₁ ++ o₂) x = (gatherFrom k g o₁ x).bind (gatherFrom k g o₂)
  | [], _, _ => rfl
  | o :: os, o₂, x => by
    show (stepG k g x o).bind (gatherFrom k g (os ++ o₂)) =
      ((stepG k g x o).bind (gatherFrom k g os)).bind (gatherFrom k g o₂)
    cases stepG k g x o with
    | error e => rfl
    | ok y => exact gatherFrom_append os o₂ y

/-- The batching's step as far as the runs o₁: the draw, the guard behind it, the gathering over
o₁. What it returns: the claims' shapes gathered so far, and the chain's shape. -/
def batchFrontG (rows : Nat) (o₁ : List (Nat × String)) (a : ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  (drawG rows a).bind fun a' =>
    if thereB a' && (a'.link.map (·.handed)).getD false then gatherFrom k g o₁ ([], a')
    else .error "K9.draw-has-run"

/-- The rest of the batching's step: the gathering over o₂ from what is gathered, the adding, the
test on the mark. -/
def batchBackG (o₂ : List (Nat × String)) (y : List ClaimSh × ChainSh) : Except String ChainSh :=
  ((gatherFrom k g o₂ y).bind laidG).bind fun u => if u.marked then .error "marked" else .ok u

/-- **THE BATCHING's STEP ON SHAPES, CUT BETWEEN TWO RUNS.** -/
theorem batchGS_split (rows : Nat) (o₁ o₂ : List (Nat × String)) (a : ChainSh) :
    batchGS rows k g (o₁ ++ o₂) a = (batchFrontG k g rows o₁ a).bind (batchBackG k g o₂) := by
  unfold batchGS batchG batchFrontG batchBackG
  cases drawG rows a with
  | error e => rfl
  | ok a' =>
    show (addsG k g (o₁ ++ o₂) a').bind _ = _
    unfold addsG gatherG
    by_cases h : (thereB a' && (a'.link.map (·.handed)).getD false) = true
    · show (if _ then _ else _ : Except String ChainSh).bind _ =
        (if _ then _ else _ : Except String (List ClaimSh × ChainSh)).bind _
      rw [if_pos h, if_pos h, gatherFrom_append]
      cases gatherFrom k g o₁ ([], a') <;> rfl
    · show (if _ then _ else _ : Except String ChainSh).bind _ =
        (if _ then _ else _ : Except String (List ClaimSh × ChainSh)).bind _
      rw [if_neg h, if_neg h]
      rfl

/-- The same at a whole order, cut behind its first j runs. -/
theorem batchGS_cut (rows j : Nat) (order : List (Nat × String)) (a : ChainSh) :
    batchGS rows k g order a =
      (batchFrontG k g rows (order.take j) a).bind (batchBackG k g (order.drop j)) := by
  rw [← batchGS_split, List.take_append_drop]

end

/-- batchBackG with the adding's second text (AddLight.lean: addListS_eq). The first field is made
by Lean: the closing rfl fills it. The second field is the tie. -/
def batchBackGL : { f : SegSort →
      (Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)) →
      List (Nat × String) → List ClaimSh × ChainSh → Except String ChainSh //
    ∀ k g o₂ y, batchBackG k g o₂ y = f k g o₂ y } :=
  ⟨_, fun k g o₂ y => by
    delta batchBackG laidG
    simp -zeta only [addListS_eq]
    rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.gatherFrom_append
#print axioms Johnson.AtFull.Shape.batchFrontG
#print axioms Johnson.AtFull.Shape.batchBackG
#print axioms Johnson.AtFull.Shape.batchGS_split
#print axioms Johnson.AtFull.Shape.batchGS_cut
#print axioms Johnson.AtFull.Shape.batchBackGL
