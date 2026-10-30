-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastVis.lean: the half on W of (Dot), in the form that `door_dot` asks, from `w_is_at_stand` (E2E/FirstHWIs.lean).

  `matBits`, `matBits_low`: the matrix by bits, at an entry.
  `vis_rows`: `WIs` at that matrix gives `VIs` at the rows.

What stays open. The call at a stand of the first thread at 19, and that the two chains hold one matrix.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.FirstHWIs
import E2E.KeyDotMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.K13.Law (WIs lowBits ρg)
open _root_.Desc.K14.Law (VIs)

/-- The matrix by bits. -/
def matBits (S : LinShape) (entry : Nat → Nat → GF) : Fin S.matrixRows → (Fin S.kCol → Bool) → GE :=
  fun i b => algebraMap GF GE (entry i.val (Sz.rowNo b))

theorem matBits_low (S : LinShape) (entry : Nat → Nat → GF) (i : Fin S.matrixRows) (e : Nat) (he : e < 2 ^ S.kCol) :
    matBits S entry i (lowBits S.kCol e) = algebraMap GF GE (entry i.val e) := by
  unfold matBits
  rw [AtPublicFiles.FirstH.rowNo_lowBits S.kCol e he]

/-- **`WIs` gives `VIs` at the rows that the shared chain lays.** -/
theorem vis_rows (S : LinShape) (entry pad tail : Nat → Nat → GF) (m : OnBytes.Means.Words GE) (ws : List Tensor) (w : Nat)
    (lay : VectorLay) (hW : WIs (matBits S entry) m ws w lay) :
    VIs S (fun y => (ws.map fun g => ρg.val (g.entry y)).sum)
      (fun r k => ρg.val (ProofFile.Honest.K14.rowsOf S ⟨entry⟩ ⟨pad, tail⟩ r k)) (fun c => m w .main (lay.index c)) :=
  AtPublicFiles.KeyDotMeets.vis_of_wIs S _ _ m ws w lay hW fun i e he => by
    rw [matBits_low S entry i e he, AtPublicFiles.Key.matOf_rowsOf S entry pad tail i.val e i.isLt]

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.matBits_low
#print axioms AtPublicFiles.KeyLastChain.vis_rows
