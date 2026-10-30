-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/MatTieOfReaderCells.lean: kind K13 (the members' batching): the
kind's tie `MatTie` (ExchangeAtM3.lean of this folder), the premise hM of its statements at numbers
355 and 356 of the proof file's first chain, where the Script's cells are defined from the entries
that the reader of the index reads. Under the hypothesis h (`P5J.AtMgA`), at the frame's own
parameters of the first chain's thread (`lettersHead`, Honest/Thread/FirstHead.lean). Two statements
with their proofs; no definition.

Main names.
  `k13_matTie_of_readerCells`: `MatTie` from hc: where the one input w₁ is admitted, each cell of
    the Script's cells at w₁ is the image in the extension field of the entry that `weights` reads
    off w₁'s index at that row and column. Under h this hc says the same as `MatTie`: the statement
    only restates it, cell by cell.
  `k13_matTie_of_cellsOfF`: **`MatTie` where the Script's cells at w₁ are the library's matrix of
    cells of that reader** (`Bind.ForProver.cellsOfF`, Johnson/Bind/ForProver/CellsInField.lean).
    The tie is then true by construction: the one side is defined from the other.

General in the type of the index, the reader `weights`, the prover, the Script's other fields and
the thread's other parameters. Nothing is asked of the index: not that it is in any range. Out of
range the tie still holds, and then says little: see Limits.

How. `matTie_iff_at_head` (MatTieAtHead.lean of this folder), from right to left; under h every row
and column of its right side lies inside the cells' shape (`k13_cellAtNo_in_range`,
BoundsAtHead.lean); the reader's value is the field's map (`val_eOfF`, CellsCast.lean).

Limits. Conditional on h and hc. hc is a sentence on the Script's field `cells` and the reader, at
one input: both sides are functions of the prover's input alone. It says nothing on what a prover
stores, sends or commits to, and nothing ties `weights` here to the reader that a prover's side is
handed. That the matrix of cells is in range (`Flat.InRange`: it holds a well-formed index), and
that it is what a stored table decodes to, is not shown
here. The statements hold values of the index's own entries: they are not to stand in front of a law
over coins.

What is not claimed. Neither is one of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.BoundsAtHead
import Johnson.Desc.ProofFile.Honest.K13.CellsCast
import Johnson.Bind.ForProver.CellsInField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (numsRef)
open OnBytes.Slice (frS frZ)
open Inst.Model.Layout (kRef hRef)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`MatTie` where each of the Script's cells is the reader's entry.** hc: where the one
input is admitted, each cell at it is the image of the entry that `weights` reads at that row and
column. pl: a pile's filler, which neither matrix reads. -/
theorem k13_matTie_of_readerCells {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst}
    (hc : Vd w₁ → ∀ (i : Fin hRef) (C : Fin (2 ^ kRef)),
      Q.cells w₁ i C = algebraMap Cb.Gl.F Cb.Gl.E ((weights w₁.w₀).entry i.val C.val)) :
    MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h) :=
  (matTie_iff_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).2 fun hV i C hi hC => by
    obtain ⟨h1, h2, e⟩ := k13_cellAtNo_in_range h (Q.cells w₁) hi hC
    rw [e, val_eOfF]
    exact hc hV ⟨i, h1⟩ ⟨C, h2⟩

/-- **`MatTie` where the Script's cells at the one input are the library's matrix of cells of the
reader.** -/
theorem k13_matTie_of_cellsOfF {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst}
    (hc : Q.cells w₁ =
      Bind.ForProver.cellsOfF frS frZ 402653181 numsRef (weights w₁.w₀).entry) :
    MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h) :=
  k13_matTie_of_readerCells h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ fun _ i C => by
    rw [hc]
    rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_matTie_of_readerCells
#print axioms ProofFile.Honest.K13.k13_matTie_of_cellsOfF
