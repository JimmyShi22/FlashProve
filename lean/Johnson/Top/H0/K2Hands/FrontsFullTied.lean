-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontsFullTied.lean: the code switch: A CLOSED FACT ON THE 25 WRITTEN ENTRIES
OF THE FULL SIZE, BY LEAN's KERNEL: each typed structure's list of new members is tied to what the
switch into its group announces at the written shape. It is the closed premise htied of
`frontSide_of` (Johnson/Top/H0/K2Caller/FrontSide.lean).

Main names:
  `sentW g`: the notices of the switch into group g at the written shape: at a link and at the
    output head the plan's own (`K2.targetAt`, `K2.othersAt`:
    Johnson/Goal/Meaning/K2Share/FrontNotices.lean); at the finish the target's with the one fold
    mask's.
  `tied_full`: the test `tiedB` (TiedAt.lean) accepts at all 25 entries of `tableFullLit`.
    `tied_at`: at an entry.
  `tied_other`, `tied_other'`: two negative tests: an entry against a neighbour's notices: the test
    rejects.
Limits. It speaks of the written shape; that a real front's notices are these is left to a law
along the fold, in other files. Nothing at the small size. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Hands.FrontsFull
import Johnson.Top.H0.K2Hands.TiedAt
import Johnson.Goal.Meaning.K2Share.FrontNotices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open Johnson.G (fxAt)
open _root_.Tw.K2 (switchNotices)

/-- **What the code switch into group g announces, at the written shape**: at a link and at the
    output
head the plan's own notices; at the finish (group 25) the target's with the one fold mask's. -/
def sentW (g : ℕ) : List OracleNotice :=
  (switchNotices (K2.targetAt shW g)
    (if g = 25 then #[foldMaskNotice ((K2.frameAtLink shW 25).foldShape 25 {})]
      else K2.othersAt shW g)).toList

/-- The test: the typed structure's list of new members is tied to these notices. -/
def tiedFullB (i : ℕ) : Bool := (tableFullLit[i]?).any fun r => tiedB r.l (sentW (i + 1))

/-- **It accepts at all 25 written entries**: by Lean's kernel. -/
theorem tied_full : (List.range 25).all tiedFullB = true := by decide +kernel

theorem tied_at {i : ℕ} {r : SwRow} (hi : i < 25) (h : tableFullLit[i]? = some r) :
    tiedB r.l (sentW (i + 1)) = true := by
  have k := List.all_eq_true.1 tied_full i (List.mem_range.2 hi)
  unfold tiedFullB at k
  rw [h] at k
  exact k

/-- **A negative test**: the first entry against the second switch's notices: it rejects. -/
theorem tied_other :
    (tableFullLit[0]?).map (fun r => tiedB r.l (sentW 2)) = some false := by decide +kernel

/-- **A second**: the second entry against the first switch's notices: it rejects. -/
theorem tied_other' :
    (tableFullLit[1]?).map (fun r => tiedB r.l (sentW 1)) = some false := by decide +kernel

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.tied_full
#print axioms VerifiableInference.Desc.First.K2Hands.tied_at
#print axioms VerifiableInference.Desc.First.K2Hands.tied_other
#print axioms VerifiableInference.Desc.First.K2Hands.tied_other'
