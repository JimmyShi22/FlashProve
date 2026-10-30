-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/SplitWritten.lean: splitB (RecFacts.lean) ACCEPTS AT THE WRITTEN VALUES, AT BOTH SHARED PROXIMITY TESTS: the closed fact behind the premises fSp9 | fSp10 of the ledger's top row and fSp of the seam's newer form, DECIDED BY LEAN's KERNEL at realSized | codesFull2 and at K12's files' written places piUFull | piOFull (Johnson/Desc/K12/Law/PlacesFull.lean).
  split_any        (realSized.any fun p => splitB … piUFull && splitB … piOFull) = true: by the kernel. splitB says no at a place without stages: so it holds its own «not empty»; «any» is false at none.
  split_not        negative twins, each = false, by the kernel: a place without stages · o_sp's code := 0 · a first stage whose Z.a is 0.
  split_congr      splitB reads of the place its nums.stages ALONE.
  fSp_written_U | fSp_written_O   at every x that realSized returns and EVERY place π whose stages are piUFull's | piOFull's: the three clauses of fSp, to the letter of split_of_B's conclusion.
Limits. That a seat's place has the written place's stages is K12's files' to say. The layout of o_omega's sending is read through getD: that it is there: ToldFitWritten.lean's threeSome_any. The full size; the proof file. No soundness is claimed.

-/
import Johnson.Second.Seam.RecFacts
import Johnson.Second.Seam.ToldFitWritten
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12)
open H2K.Member (piUFull piOFull)

theorem split_any : (realSized.any fun p =>
    splitB codesFull2 p.1.shape (layOAt p.1) piUFull &&
      splitB codesFull2 p.1.shape (layOAt p.1) piOFull) = true := by decide +kernel

theorem split_not :
    (realSized.any fun p => splitB codesFull2 p.1.shape (layOAt p.1)
      { piUFull with nums := { piUFull.nums with stages := [] } }) = false ∧
    (realSized.any fun p => splitB codesFull2
      { p.1.shape with sharedSplit := { p.1.shape.sharedSplit with code := 0 } } (layOAt p.1)
      piOFull) = false ∧
    (realSized.any fun p => splitB codesFull2 p.1.shape (layOAt p.1)
      { piUFull with nums := { piUFull.nums with
          stages := piUFull.nums.stages.map fun a => { a with Z := { a.Z with a := 0 } } } }) =
      false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem split_congr (cs : Codes) (S : LinShape) (layO : TreeLay) {π π' : P12}
    (h : π.nums.stages = π'.nums.stages) : splitB cs S layO π = splitB cs S layO π' := by
  unfold splitB
  rw [h]


theorem fSp_written_U (x : LinSized) (hx : realSized = some (x, codesFull2)) (π : P12)
    (hπ : π.nums.stages = piUFull.nums.stages) :
    ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < x.shape.sharedSplit.maskRows ∧
      codesFull2.base.size ≤ x.shape.sharedSplit.code ∧
      ((layOAt x).shapes.getD ((layOAt x).tree.getD 1 0) default).logN ≤ a₀.Z.a := by
  have t := split_any
  rw [hx] at t
  simp only [Option.any_some, Bool.and_eq_true] at t
  exact split_of_B ((split_congr _ _ _ hπ).trans t.1)


theorem fSp_written_O (x : LinSized) (hx : realSized = some (x, codesFull2)) (π : P12)
    (hπ : π.nums.stages = piOFull.nums.stages) :
    ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < x.shape.sharedSplit.maskRows ∧
      codesFull2.base.size ≤ x.shape.sharedSplit.code ∧
      ((layOAt x).shapes.getD ((layOAt x).tree.getD 1 0) default).logN ≤ a₀.Z.a := by
  have t := split_any
  rw [hx] at t
  simp only [Option.any_some, Bool.and_eq_true] at t
  exact split_of_B ((split_congr _ _ _ hπ).trans t.2)

end Second.Seam

#print axioms Second.Seam.split_any
#print axioms Second.Seam.split_not
#print axioms Second.Seam.fSp_written_U
#print axioms Second.Seam.fSp_written_O
