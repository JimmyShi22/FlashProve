-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadDoorRowsLaw.lean: what acceptance by the two public tests planK6Row and
padsRow (Johnson/Desc/Kinds/HeadDoorRows.lean) implies, where their five further arguments are read
off arr, num, the table of numbers N and the typed oracle messages ms. Theorems.

What is proved. lettersOf arr num N ms: the five arguments so read.
  labs_eq, nas_eq   the light readers of the public part are Meaning.labAt and Hd.shapeA's.
  planK6_of_row     planK6Row Z (lettersOf arr num N ms) = true and Meaning.laidThere Z.p.X (sizesOf
          Z.p.X) Z.first.layout = true imply the four clauses named, seats, maskNamed, maskIn of
          PlanK6 (Law/K6Cut.lean) at cs := Z.first.codes, Wp := Z.p.X, lay6 := Z.first.layout, n :=
          num 24 0, rb := 0.
  named_of_row      the first premise alone implies namedOnce arr N 24 (num 24 0) = true.
  padsFree_of_row   padsRow Z (lettersOf arr num N ms) = true and Meaning.laidThere Z.p.X s
          Z.first.layout = true imply PadsFree Z.first.codes arr ms N s (seatBy (fLay Z.first.layout
          num) Z.p.X s) Z.p.X.

No existential quantifier in these statements.
Not proved here. That the arguments which the list of public tests passes are lettersOf at the
composed statement's own arr, num, N, ms: Law/HeadDoorAtZLaw.lean. Meaning.laidThere. The full size
only. Nothing on soundness.

-/
import Johnson.Desc.Kinds.HeadDoorRows
import Johnson.Desc.Kinds.Law.PadsDoorLaw
import Johnson.Desc.Kinds.Law.PlanK6DoorMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Road
open OnBytes.Model.Verify (borderOf)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem namedOnce)
open P5J (PadsFree)

/-- The five arguments, read off arr, num, N and ms. -/
def lettersOf (arr num : ℕ → ℕ → ℕ) (N : Numbers) (ms : List Mem) : DoorLetters :=
  { arr := arr, num := num, group := N.group, sent0 := N.sent 24 0, mems := plainOf ms }

theorem labs_eq (X : Model.Verify.Public) : labsOf X = Meaning.labAt X := rfl

theorem nas_eq (X : Model.Verify.Public) : nasOf X = fun g => (Hd.shapeA X g).cf.NAs := rfl

variable (Z : ProofFile.Pub) (arr num : ℕ → ℕ → ℕ) (N : Numbers) (ms : List Mem)

/-- **Acceptance by the first test implies PlanK6's four clauses.** -/
theorem planK6_of_row (h : planK6Row Z (lettersOf arr num N ms) = true)
    (T : Meaning.laidThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true) :
    (∀ (μ : Fin (Meaning.sizesOf Z.p.X 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Z.p.X 24).m μ) → c < (Meaning.sizesOf Z.p.X 24).k μ →
      ColFour Z.p.X.hS Z.p.X.HLy (borderOf Z.p.X.y) μ.val c →
      namedOnce arr N 24 (seatLay Z.p.X Z.first.layout num 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Z.p.X 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Z.p.X 24).m μ) → c < (Meaning.sizesOf Z.p.X 24).k μ →
      ColFour Z.p.X.hS Z.p.X.HLy (borderOf Z.p.X.y) μ.val c →
      InCopy Z.first.codes arr (ms0 ms N) ms N 24 (seatLay Z.p.X Z.first.layout num 24 μ r c).1
        false (seatLay Z.p.X Z.first.layout num 24 μ r c).2.1
        (seatLay Z.p.X Z.first.layout num 24 μ r c).2.2) ∧
    (∀ j, j < Z.p.X.H.ns → namedOnce arr N 24 (plAt (num 24 0) 0 j).1 = true) ∧
    (∀ j, j < Z.p.X.H.ns → InCopy Z.first.codes arr (ms0 ms N) ms N 24 (plAt (num 24 0) 0 j).1
      (plAt (num 24 0) 0 j).2.1 (plAt (num 24 0) 0 j).2.2.1 (plAt (num 24 0) 0 j).2.2.2) :=
  planK6_of_door Z.first.codes arr ms N Z.p.X Z.first.layout num (num 24 0) 0 T h

/-- **And that exactly one oracle message of the head's segment has the mask row's message's
number.** -/
theorem named_of_row (h : planK6Row Z (lettersOf arr num N ms) = true) :
    namedOnce arr N 24 (num 24 0) = true :=
  named_of_door Z.first.codes arr ms N Z.p.X Z.first.layout num (num 24 0) 0 h

/-- **Acceptance by the second test implies PadsFree.** -/
theorem padsFree_of_row (s : ℕ → Size) (h : padsRow Z (lettersOf arr num N ms) = true)
    (T : Meaning.laidThere Z.p.X s Z.first.layout = true) :
    PadsFree Z.first.codes arr ms N s (Meaning.seatBy (Meaning.fLay Z.first.layout num) Z.p.X s)
      Z.p.X :=
  padsFree_of_door Z.first.codes arr ms N Z.p.X Z.first.layout num s T h

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_of_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.named_of_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_of_row
