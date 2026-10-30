-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoRow4.lean: THE NAMED SENTENCE `WoSays` AGAINST THE ROW THAT `pendingRowO` RETURNS.
WoLed.lean says `WoSays` in words on the return of `wsPending`, a routine of `verify-on-bytes`. The
seated text makes the row that a link's end lays on the pile by another routine: `pendingRowO`
(Johnson/Desc/First/Pend/Row.lean). Johnson/Top/H0/MergeLaw/PendRow.lean ties the two (`pend_inv`).
Here `WoSays` is said of that row's own four fields: `wsPending` LEAVES THE STATEMENT. One statement
and its proof.

  `woSays_iff_row`: where `pendingRowO lay im wo claims S os = .ok (r, os')`: `WoSays P st wo mm`
    holds exactly if the sum over the cube's rows of `pendWeight gl r.g j` times the committed
    matrix's row j read at the point `r.psi` turned round, plus the sum over the row's named mask
    entries of the entry times its factor, is the reading of `r.target`: the sentence `RowSays` of
    Johnson/Top/H0/MergeLaw/WoRow.lean, written out, at the cells `P.Wn (P.msg mm)`.

NO NEW ARGUMENT: `woSays_iff_list` (WoLed.lean); `pend_inv`.

Limits. `wsPending` stays IN THE PROOF: `pend_inv` and `pending_port_free` speak of it.
hs and ho name `wsClaimShape`, `wsRowPart` and `wsEpsT` (OnBytes/Model/Weights.lean): routines
of `verify-on-bytes` on data. PREMISES: as `woSays_iff_list`'s, but that `wsPending` returns; and
hidx: the index masks' entry that the row names is the typed mask entry `P.msg mm P.c7`. The cells
are `P.Wn (P.msg mm)` by the statement: that another file's cells are these is not said. The claims'
list cr is a letter. im, os, claims and S are letters: that a layers' link's end calls `pendingRowO`
at the index masks' number, the statement's messages, the plan's count and this wo is not said here.
`RowSays` is, by its own file's head, a stand-in for the notion that the pile's law will have; that
the right side here is `RowSays` is seen by eye: WoRow.lean is not imported. An equivalence of two
sentences on numbers: no draw. Nothing on soundness.
-/
import Johnson.Road.K4.WoLed
import Johnson.Top.H0.MergeLaw.PendRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (WsLay WsClaim WsForkOut wsEpsT wsRowPart wsClaimShape)
open Cb.Pv.Lay.At (tval)
open Inst.Model.Layout.Tensor (matOf)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)
open Inst.Model (Scl)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.MergeLaw (pend_inv)

variable [scl : Scl] {M X : Type}

/-- **The named sentence, of the row that `pendingRowO` returns.** -/
theorem woSays_iff_row (P : FullPar GE M X) (st : St7 GE P.wp0.n × GE) (wo : WsForkOut) (mm : M)
    (lay : WsLay) (hk : P.kW = lay.lk) (claims : ℕ) (S : Params.LinShape)
    (cr : List (WsClaim × E)) (hn : cr.length = P.nW)
    (hco : ∀ a : Fin P.nW, st.2 ^ (a : ℕ) = gl.val (cr.get (a.cast hn.symm)).2)
    (hu : ∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ y ∈ cr, wsClaimShape lay y.1 = .ok ())
    (H : ∀ a : Fin P.nW,
      tval (P.wp0.ten a st.1) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
        claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm))) (cr.get (a.cast hn.symm)).1)
    (ho : wo.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)))
    {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO lay im wo claims S os = .ok (r, os')) (idx : ℕ → GE)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = P.msg mm P.c7) :
    WoSays P st wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl lay.lk r.psi.reverse.toArray (P.Wn (P.msg mm)) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  obtain ⟨w, l, c, l', hw, _, _, er, _, e6, e7, e8⟩ := pend_inv hr
  rw [woSays_iff_list P st wo mm lay hk claims S cr hn hco hu hs H ho hw]
  have hi := hidx (⟨im, c⟩, w.beta) (by rw [er]; exact List.mem_singleton.2 rfl)
  have hp : r.psi.reverse.toArray = wo.rm := by
    rw [er]
    show w.psi.reverse.toArray = _
    rw [e6, List.reverse_reverse]
  rw [hp, er]
  show _ ↔ _ + ([(idx c * gl.val w.beta)]).sum = gl.val w.target
  rw [List.sum_singleton, e7, e8]
  have hi' : idx c = P.msg mm P.c7 := hi
  rw [hi']

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.woSays_iff_row
