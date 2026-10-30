-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/DataAtWritten.lean: at the full size: the proof file's and the key file's data at
the written lists, laid at the frame's depth, are these data themselves. So "the description's own
road makes the data at the written lists" is, to the letter, the first clause of what is left of the
proof file's hypothesis (`ProofPlainLeft`, Johnson/Flat/Dec/ProofPlainLeft.lean) at the frame whose
data are the written ones.

Why. That clause reads `F.data "proof file" = .ok (DP.at frS.P.T.a)`, DP a letter of the frame. A
test on a description's declared rounds against the written lists gives `F.data "proof file" = .ok
(WholeD.of 32 (wholeAt (some dryProofFull)))`. The two right sides are not one text. At DP :=
`writtenPFull` (Johnson/Flat/Dec/FitAtWritten.lean) they are one value.
  `WholeD.of_at`: data made at the depth a, laid at a, are themselves.
  `writtenPFull_at`, `writtenKFull_at`: so at the frame's depth (`fr_a`: it is 32).
  `data_at_written`, `data_at_writtenK`: the equation on a description's road, carried from the one
  right side to the other.
Limits. Equations of values. That the data of a frame of which a goal speaks are the written ones is
not said here. No description is named. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Desc.BlockSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice OnBytes.RunA Johnson.G Johnson.G.OfPlan
open VerifiableInference.Desc

/-- Data made at the depth a, laid at a, are themselves. -/
theorem _root_.OnBytes.Maker.WholeD.of_at (a : ℕ) (W : _) :
    (WholeD.of a W).at a = WholeD.of a W := rfl

/-- The proof file's written data at the frame's depth. -/
theorem writtenPFull_at : writtenPFull.at frS.P.T.a = writtenPFull := by
  rw [Johnson.G.fr_a]
  exact WholeD.of_at 32 _

/-- The key file's. -/
theorem writtenKFull_at : writtenKFull.at frS.P.T.a = writtenKFull := by
  rw [Johnson.G.fr_a]
  exact WholeD.of_at 32 _

/-- **The two right sides are one value**, at the frame whose proof file's data are the written
ones. -/
theorem data_at_written {Xi : Type} (F : FileDescription Xi) (file : String)
    (h : F.data file = .ok (WholeD.of 32 (wholeAt (some dryProofFull)))) :
    F.data file = .ok (writtenPFull.at frS.P.T.a) := by
  rw [writtenPFull_at]
  exact h

/-- The key file's. -/
theorem data_at_writtenK {Xi : Type} (F : FileDescription Xi) (file : String)
    (h : F.data file = .ok (WholeD.of 32 (wholeAt (some dryKeyFull)))) :
    F.data file = .ok (writtenKFull.at frS.P.T.a) := by
  rw [writtenKFull_at]
  exact h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.writtenPFull_at
#print axioms VerifiableInference.OnPublicFiles.data_at_written
#print axioms VerifiableInference.OnPublicFiles.data_at_writtenK
