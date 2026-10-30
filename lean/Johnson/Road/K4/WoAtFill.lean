-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WoAtFill.lean: FROM «THE ROW THAT THE LINK's FRAME's READER GIVES AT THE VERIFIER's
STATE HOLDS, IN THE PILE's SENSE» TO THE ROW's SENTENCE `Plan4K.WoRow`. One statement with its
proof: a joining of three rules; no new argument. General in the pile's witness: no
layer's definition is named.

OBJECT: `Holds Reading.gl wK r` (Johnson/Desc/K13/Law/Means.lean) at a witness wK of the pile's
type, of nR rows and kC column bits, and the row r that `Johnson.Desc.First.Walk.Law.rowAt` gives at
a state s of the verifier; `hasRow` (Johnson/Top/H0/Walk/FrameRow.lean): the public Bool "the reader
gives a row". USER: `k4Lines_wo_at` (K4LinesWo.lean).

  `Plan4K.woRow_of_holds`: where the first chain's seat finds in s what K4's hearing holds, o (the
    Lean structure `Own`) (ho), the reader gives a row at s, at the plan's layout (hh), and every
    row that it gives there holds of wK (hw): `WoRow par o mm`: by `rowSays_iff_holds`
    (Johnson/Top/H0/MergeLaw/RowHolds.lean: the pile's `Holds` is `RowSays`), `row_tie` and
    `pending_sizes`, and `Plan4K.woRow_of_rowAt` (WoRowAt.lean).

Limits. FIVE TIES STAY PREMISES: hk, hnR: the pile's witness has the plan's layout's numbers of
column bits and rows: two equations on the plan's numbers · hzero: the value's cells `Wn` at the
message are 0 from row nR on · hmat: wK's matrix IS these cells · hmask: its mask entry at the name
that the row bears IS the value's message at c7. hh is a premise: WITHOUT IT hw HOLDS FOR NOTHING
WHERE THE READER GIVES NONE. Nothing on soundness.
-/
import Johnson.Road.K4.WoRowAt
import Johnson.Top.H0.MergeLaw.RowHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (row_tie pending_sizes rowSays_iff_holds)
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.Walk.Law (leftOf hasRow)
open Inst.Model (Scl)

variable [scl : Scl] {Mm : Type}

/-- **Where the frame's reader's row holds in the pile's sense, the row's sentence holds**: where
the seat finds o in s (ho), the reader gives a row (hh), and the pile's witness is tied to the value
(hk, hnR, hzero, hmat, hmask). -/
theorem Plan4K.woRow_of_holds (QK : Plan4K Mm S) {par : Par} {n : ℕ} {lin : Params.LinShape}
    {nR kC : ℕ} {s : S} {mm : Mm} {o : Own}
    (wK : VerifiableInference.Desc.K13.Law.Wit Cb.Gl.E nR kC) (ho : seatS.own s = some o)
    (hh : hasRow par.P.wsLay n lin s = true)
    (hw : ∀ r, Johnson.Desc.First.Walk.Law.rowAt par.P.wsLay n lin s = some r →
      VerifiableInference.Desc.K13.Law.Holds Reading.gl wK r)
    (hk : kC = par.P.wsLay.lk) (hnR : nR = par.P.wsLay.m0)
    (hzero : ∀ j, nR ≤ j → ∀ C, QK.toL.plan.full.Wn (QK.toL.plan.full.msg mm) j C = 0)
    (hmat : ∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC →
      wK.mat i (lowBits kC C) = QK.toL.plan.full.Wn (QK.toL.plan.full.msg mm) i C)
    (hmask : ∀ r, Johnson.Desc.First.Walk.Law.rowAt par.P.wsLay n lin s = some r →
      ∀ t ∈ r.masks, wK.mask t.1 = QK.toL.plan.full.msg mm QK.toL.plan.full.c7) :
    QK.WoRow par o mm := by
  subst hk hnR
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hh
  have hH := hw r hr
  obtain ⟨w0, wp, l, c, l', _, b2, _, _, b5, b6, _, _⟩ := row_tie (left := leftOf) hr
  obtain ⟨z1, z2⟩ := pending_sizes b2
  have hpsi : r.psi.length = par.P.wsLay.lk := by
    rw [b5]
    show wp.psi.length = par.P.wsLay.lk
    rw [b6, List.length_reverse, Array.length_toList, z1]
  exact QK.woRow_of_rowAt ho hr (fun _ _ => rfl)
    ((rowSays_iff_holds (QK.toL.plan.full.Wn (QK.toL.plan.full.msg mm))
      (fun _ => QK.toL.plan.full.msg mm QK.toL.plan.full.c7) r wK hpsi z2 hzero hmat
      (hmask r hr)).2 hH)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.woRow_of_holds
