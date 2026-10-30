-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/LawsAtIndex.lean: the premise under which the kind's exchange stands at an index that is
a letter: the conclusion of `laws_of_readyInput` (Johnson/HonestTrace/ReadyAtFullIn.lean), at a return
A of the maker. The online prover's index is a matrix, and its trace goes through the index that the
matrix holds; carrying that law there is the work of the laws' own authors, not of this kind.
One definition, a named premise, and the law that the stop's measure asks of the cells:
`ready_cells_small`. Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.HonestTrace.ReadyAtFullIn
import Johnson.HonestTrace.DigitsAtTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open ProofFile.Honest
open OnBytes.HonestTrace
open VerifiableInference.Desc (FileDescription)
open Inst.Model (Instance ppref)

variable {W₀ Rc X₀ X : Type}

/-- **At an input that meets `ReadyInput`** there are an index and an instance: the index serves the
instance, the input's cells are the model's trace's, with five laws on that trace. -/
def ReadyLaws (Fd : FileDescription ProofFile.Inst) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) : Prop :=
  ∀ v : Local W₀ Rc ProofFile.Inst Cells, ReadyInput Fd A.H v →
    ∃ (i : Cm.Idx) (x : Instance ppref), ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X i x ∧
      v.trace = ⟨cellOf A.Z.p.X (theTrace A.Z.p.X i x)⟩ ∧
      MeetsAll A.Z.p.X i x (theTrace A.Z.p.X i x) ∧
      BorrowedSame A.Z.p.X (theTrace A.Z.p.X i x) ∧
      NamesFit A.Z.p.X (theTrace A.Z.p.X i x) ∧ PartsFit A.Z.p.X ∧ PlanMarks A.Z.p.X

/-- **The door of the stop's measure**: at an input that meets `ReadyInput` every cell of every place's
matrices is at most 128 in size, at every list of names. At a name that is no label the cells are 0.
Under the named premise alone. -/
theorem ready_cells_small {Fd : FileDescription ProofFile.Inst} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : ReadyLaws Fd A) {v : Local W₀ Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v)
    (p : VerifiableInference.Desc.First.K8.Par) (mats : List (Nat × String × Nat)) :
    VerifiableInference.Desc.First.K8.Honest.cellsSmall p (cellsAtOf v.trace mats) = true := by
  obtain ⟨i, x, -, -, hc, M, -⟩ := hL v hv
  rw [hc]
  exact cellsSmall_cellOf M.small p mats

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.ready_cells_small
#print axioms ProofFile.Honest.K8.ReadyLaws
