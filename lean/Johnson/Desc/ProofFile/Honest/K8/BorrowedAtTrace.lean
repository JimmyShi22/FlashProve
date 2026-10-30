-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/BorrowedAtTrace.lean: the honest side of the smallness test (K8):
AT THE READER OF CELLS THAT A TRACE GIVES (`cellOf` X T, Johnson/HonestTrace/Full.lean), THE PACKING
AT A MATRIX's OWNER IS THE PACKING AT THE SEGMENT's OWN NUMBER, at each matrix of each of the 25
segments, the owner read off the written labels (`K8Q35.labW`, Johnson/K8Q35R/MatsAtHead.lean, with
`Meaning.ownerK`, `ownerA`, Johnson/Goal/Meaning/HidOwner.lean). Under a condition on X and one on
the trace. Two definitions, a public test. Lemmas; none of the library's goals.

  `borOkAt`, `borOk`   A PUBLIC TEST: segment l has a matrix number μ in its list of names; the
                     owner that the sizes' table gives it (`Sz.ref.owner`,
                     Johnson/HonestTrace/Places.lean) has the link and the number that the label
                     names; both have one shape. The second: at the matrix's own written label
  `borW`             BY LEAN's KERNEL: the test says yes at each matrix of each segment
  `borW_shifted`     A CONTROL THAT SAYS NO: with the label of the next matrix in the stead
  `packed_is_of`     under the condition on X the packing of the trace's reader is the packing of
                     the trace's integers (`packedOf`, Johnson/HonestTrace/Packed.lean)
  `bor_of_trace`     THE END

By, of other authors: `owner_entry_of_same` (Johnson/HonestTrace/CellOfOwner.lean): the trace holds
at the owner's number the entries of the segment's own number · `cellOf_label`
(Johnson/HonestTrace/CellOfAt.lean) · `packedOf_eq_cells` (Packed.lean) · `Seg.of_ofNo`
(Johnson/HonestTrace/Names.lean). Near: `cellOf_owner` (CellOfOwner.lean): the same of one cell, by
segment and name; here it is said of the packing, by the written labels' numbers.
A twin, on no row, so not imported: `packedOf_eq_cellOf` (Johnson/HonestTrace/PackedJoins.lean) is
`packed_is_of` with the two sides changed about, by the same call: this one falls when that one is
in the library.

What stays a hypothesis. N: `PartsFit` X: X has the numbers of parts 3, 1, 1, 4. B: `BorrowedSame` X
T: each borrowed matrix has its owner's entries in T (`borrowedSame_of_meetsAll`, CellOfOwner.lean,
has it from `MeetsAll`). Neither is shown here of any X or trace.

Limits. An equation between two readings of one trace. It names a trace: a sentence on the hidden
input. That any reader of a prover's input is `cellOf` X T is not said. Nothing on a witness, a
Script or a committed array. One choice of sizes (`Sz.ref`). Closed facts by Lean's kernel, with an
option raised. One instance is taken away, as in the files beneath (no default table of scales). It
takes a file under Johnson/Goal/Meaning/. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.HonestTrace.CellOfOwner
import Johnson.HonestTrace.Packed
import Johnson.K8Q35R.MatsAtHead
import Johnson.Goal.Meaning.HidOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.HonestTrace
open Meaning (ownerK ownerA)
open K8Q35 (labW nmW)

/-- **A PUBLIC TEST** on a segment's number, a matrix's number and a label. -/
def borOkAt (l μ lab : ℕ) : Bool :=
  match Seg.ofNo 12 l with
  | none => false
  | some σ =>
    match (MatName.all 3 1 1 4 σ)[μ]? with
    | none => false
    | some nm =>
      (Sz.ref.owner σ nm).1.no 12 == ownerK lab &&
        MatName.no? 3 1 1 4 (Sz.ref.owner σ nm).1 (Sz.ref.owner σ nm).2 == some (ownerA lab) &&
        Sz.ref.shapeNo (ownerK lab) (ownerA lab) == Sz.ref.shapeNo l μ

/-- The test at the matrix's own written label. -/
def borOk (l μ : ℕ) : Bool := borOkAt l μ (labW l μ)

set_option maxRecDepth 1000000 in
/-- **At the written labels the test says yes.** -/
theorem borW : ((List.range 25).all fun l => (List.range (nmW l)).all (borOk l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the next matrix's label in the stead no matrix of any segment passes. -/
theorem borW_shifted : ((List.range 25).any fun l => (List.range (nmW l)).any fun μ =>
    borOkAt l μ (labW l (μ + 1))) = false := by
  decide +kernel

variable {X : Model.Verify.Public} {T : Tr}

/-- **The packing of the trace's reader of cells is the packing of the trace's integers.** -/
theorem packed_is_of (N : PartsFit X) (T : Tr) (l mu r c : ℕ) :
    packedCells Sz.ref (cellOf X T) l mu r c = packedOf Sz.ref T l mu r c :=
  (packedOf_eq_cells Sz.ref T (cellOf X T) (fun σ μ a hσ ha ρ γ => by
    have hb : σ.Below 12 := hσ
    have hn : MatName.no? 3 1 1 4 σ μ = some a := by
      have q := ha
      unfold Sz.mu at q
      rw [if_pos hσ] at q
      exact q
    exact cellOf_label N T hb hn ρ γ) l mu r c).symm

/-- **At a trace's reader of cells the packing at a matrix's owner is the packing at the segment's
own number.** -/
theorem bor_of_trace (N : PartsFit X) (B : BorrowedSame X T) {l : ℕ} (hl : l < 25) {μ : ℕ}
    (hμ : μ < nmW l) (r c : ℕ) :
    packedCells Sz.ref (cellOf X T) (ownerK (labW l μ)) (ownerA (labW l μ)) r c =
      packedCells Sz.ref (cellOf X T) l μ r c := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 borW l (List.mem_range.2 hl)) μ
    (List.mem_range.2 hμ)
  unfold borOk borOkAt at t
  cases hσ : Seg.ofNo 12 l with
  | none => rw [hσ] at t; cases t
  | some σ =>
    rw [hσ] at t
    cases hnm : (MatName.all 3 1 1 4 σ)[μ]? with
    | none => simp only [hnm] at t; cases t
    | some nm =>
      simp only [hnm, Bool.and_eq_true, beq_iff_eq] at t
      obtain ⟨⟨t1, t2⟩, t3⟩ := t
      obtain ⟨hB, hno⟩ := Seg.of_ofNo hσ
      rw [packed_is_of N, packed_is_of N]
      unfold packedOf
      rw [t3]
      have e : ∀ ρ, T (ownerK (labW l μ)) (ownerA (labW l μ)) ρ c = T l μ ρ c := by
        intro ρ
        obtain ⟨a, -, ha, hT⟩ := owner_entry_of_same N B hB hnm ρ c
        obtain rfl : a = ownerA (labW l μ) := Option.some.inj (ha.symm.trans t2)
        rw [t1, hno] at hT
        exact hT
      simp only [e]

end ProofFile.Honest.K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K8.borOkAt
#print axioms ProofFile.Honest.K8.borOk
#print axioms ProofFile.Honest.K8.borW
#print axioms ProofFile.Honest.K8.borW_shifted
#print axioms ProofFile.Honest.K8.packed_is_of
#print axioms ProofFile.Honest.K8.bor_of_trace
