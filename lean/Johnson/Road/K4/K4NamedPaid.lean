-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4NamedPaid.lean: THE NINE NAMED TESTS OF K4's ROW AT THE COMPOSED MEANING's CLOSED
CONSTANT, WITH SEVEN OF THE NINE PAID: the field named of the structure of K4's law's conditions, to
the letter, out of the head, three conditions on the three public files, and TWO families of tests
that stay. One structure, two statements with their proofs: A JOIN: no new argument.

  `K4NamedTwo hA`: WHAT STAYS A TEST: front and row, twelve Bools each, with code, on the public
    parameters alone (their layers; the group's own list of numbers; for row the first chain's
    shape of the test on the committed table). WHY THEY STAY: Johnson/Road/K4/K4NamedConst.lean's
    head.
  `left_of_written`: K4NamedLeft (that file's structure of five) out of K4NamedTwo and hL, W, hc.
  **`named_const`**: hA · hL · W · hc · K4NamedTwo hA ⟹ K4NamedW at the constant, at every opening,
    g < 12, x, b under K4Here.
THE NINE, EACH BY ITS KIND:
  A THEOREM THAT ASKS NO PART OF Zp TO BE A WRITTEN VALUE: lookIn · readsP (laws on the planner and
    on the maker of the built segments: 24 of the tests) · toldFit (another file's theorem on the
    description, in scope; it spends the head's test planOk and one closed fact on the table's own
    two lists) · book (by the make of the numbers: no content).
  A CLOSED FACT BY LEAN's KERNEL AT WRITTEN VALUES, WITH ITS TIE: fence (W, hc; negative tests at
    the walk; A LIMIT OF THE TEST: it bounds a tenant's tree from above and says nothing else of
    it: Johnson/Road/K4/K4NamedFence.lean's head) · room1 (W, hc; two) · maskP (W, hc, hL; two).
  STAYS A TEST, ASKED BY NOBODY: front · row.
THE PREMISES, AND WHO PAYS: hA: the one head · hL : `At.laid?`, the reader of the chain's listed
seats, returns L (under W it returns: `laid_written`, K4PinsPaid.lean) · W : WrittenAt Zp · hc:
the first chain's cut is the written one: both are compared by rows of the verifier's entry tests
(madeRow, cutRow: the ninth and the tenth of `LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean); THIS
TREE's LIST, FOURTEEN ROWS, ASKS BOTH; that the frozen verify() holds this list is not shown in this
file.
K4NamedTwo: NO ROW OF THE VERIFIER's ENTRY TESTS ASKS IT; under the head (a member of the head is
proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/)) it is a theorem
(`k4Row_two` at `k4Row_of_head`: Johnson/Road/K4/K4RowTestLaws.lean, K4RowOfHead.lean).
CAN THEY BE MET? NO FILE JOINS THEM TO THE HEAD's MEMBER. Evaluated: both rows true at five sets of
public files in the goals' scope (a run, not shown here); front and row true x12 in the form in
which they stand here, at ONE set (the shipped full-size one), with negative tests that reject x12
(a file of evaluations). Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT
secondHashFunction; SIDE LIBRARY AtFullSide/Top/). The full size alone. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4NamedConst
import Johnson.Road.K4.K4NamedFence
import Johnson.Road.K4.K4NamedWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Total (rowB frontB)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutFirstFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **What stays a test of the nine.** SHOWN TO HOLD NOWHERE BY LEAN. Under the head (A MEMBER OF
THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); NO FILE
JOINS `K4NamedTwo` TO THAT MEMBER) it is a
theorem (`k4Row_two` at `k4Row_of_head`: K4RowTestLaws.lean, K4RowOfHead.lean). -/
structure K4NamedTwo (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : Prop where
  front : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
    frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo = true
  row : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
    rowB (P5J.At.X Zp).layers g hp.NCL hA.𝔇.d1.lin = true

/-- The structure of five, out of the two that stay and the three conditions. -/
theorem left_of_written (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L)
    (W : WrittenAt Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (R : K4NamedTwo hA) : K4NamedLeft hA L := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  exact
    { fence := fence_const hA W hc
      room1 := fun _ hg => room1_const hA L O W hc hg
      maskP := fun _ hg => maskP_const hA hL W hc hg
      front := R.front
      row := R.row }

/-- **UNDER hA, hL, W, hc AND K4NamedTwo (ALL PREMISES; SHOWN TO HOLD NOWHERE): the field named at
the constant.** -/
theorem named_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L)
    (W : WrittenAt Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    (R : K4NamedTwo hA) :
    ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b →
      K4NamedW hA.𝔇 (eAll Zp cF L) (28 * g + 4) (2 * g) (parOf x)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id)
        (Forest.elems (P5J.At.X Zp).y.fo) :=
  named_of_left hA (left_of_written hA hL W hc R)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.left_of_written
#print axioms OnBytes.Road.K4.named_const
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @OnBytes.Road.K4.named_const
