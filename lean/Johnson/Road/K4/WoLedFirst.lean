-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoLedFirst.lean: THE FIRST GROUP's NAMED SENTENCE `WoSaysF`
(Johnson/Road/K4/OwnAt.lean) IN THE PROGRAM's OWN WORDS, AND AGAINST THE ROW THAT `pendingRowO`
RETURNS. In the first group the merge has one claim more than there are typed pairs of the panels:
the embedding's, under the next power of the combining element (`rowWF`,
Cb/Pv/Lay/End/WeightsPay.lean). The twins of WoLed.lean's `woSays_iff_list` and of WoRow4.lean's
`woSays_iff_row`. Statements and proofs.

  `rowWF_snoc`: the first group's row weights are `rowW` over one pair more: the pairs of the
    claims, then the added pair; the coefficients are the powers of α.
  `woSaysF_iff_list`: `WoSaysF P st α wo mm ↔ ∑ j ∈ range (2 ^ S.kRow), pendWeight gl w.g j * rowAt
    gl lay.lk wo.rm (P.Wn (P.msg mm)) j + P.msg mm P.c7 * gl.val wo.beta = gl.val wo.fvp`, at a list
    cr of P.nW + 1 claims with their coefficients, where `wsPending` returns w.
  `woSaysF_iff_row`: the same on the four fields of the row r that `pendingRowO` returns.

NO NEW ARGUMENT: `rows_pend_at` (WoLed.lean), which is general in the number of the claims, the
coefficients and the pairs; `pend_inv` (Johnson/Top/H0/MergeLaw/PendRow.lean).

Limits. PREMISES: as `woSays_iff_list`'s and `woSays_iff_row`'s, at P.nW + 1 claims: the typed
matrix has as many column bits as the layout; the powers of α are the readings of the coefficients;
the units, `UnitOK`, `wsClaimShape`; (H): each typed pair `P.wp0.ten a st` and claim number a take
one value at the matrix `starW`; (HE): SO DO THE ADDED PAIR `tenEF P st` AND THE LAST CLAIM; the
record's `recs` are made of the claims as the program's text makes them; that the routine returns;
hidx. The list cr, st, α, idx and mm are letters: that they are a hearing's is not said here. The
cells are `P.Wn (P.msg mm)` by the statement: that another file's cells are these is not said.
`wsPending` stands in `woSaysF_iff_list` and leaves `woSaysF_iff_row`'s statement, in whose proof it
stays; hs and ho name `wsClaimShape`, `wsRowPart` and `wsEpsT` (OnBytes/Model/Weights.lean):
routines of `verify-on-bytes` on data. im, os, claims and S are letters. Equivalences of two
sentences on numbers: no draw. Nothing on soundness.
-/
import Johnson.Road.K4.WoRow4
import Johnson.Road.K4.OwnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (WsLay WsClaim WsForkOut WsPending wsEpsT wsRowPart wsClaimShape wsPending)
open Cb.Pv.Lay.At (tval)
open Cb.Pv.Lay.End.Gated (Pending tenEF)
open Inst.Model.Layout.Tensor (matOf)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)
open Inst.Model (Scl)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.MergeLaw (pend_inv)

/-- **The first group's row weights are the row weights over one pair more.** -/
theorem rowWF_snoc {E : Type} [Field E] [Fintype E] (P : FootW0 E)
    (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E)) (st : St7 E P.n) (α : E)
    (ψ : Fin P.k → E) (r : Fin P.h) :
    Gated.rowWF P tenE st α ψ r =
      Gated.rowW (fun a : Fin (P.n + 1) => α ^ (a : ℕ))
        (Fin.snoc (α := fun _ => (Fin P.h → E) × ((Fin P.k → Bool) → E))
          (fun a => P.ten a st) (tenE st)) ψ r := by
  unfold Gated.rowWF Gated.rowW
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

variable [scl : Scl] {M X : Type}

/-- **The first group's named sentence in the program's own words**, the claims and their
coefficients as one list. -/
theorem woSaysF_iff_list (P : FullFPar GE M X) (st : St7 GE P.wp0.n) (α : GE) (wo : WsForkOut)
    (mm : M) (lay : WsLay) (hk : P.kW = lay.lk) (claims : ℕ) (S : Params.LinShape)
    (cr : List (WsClaim × E)) (hn : cr.length = P.nW + 1)
    (hco : ∀ a : Fin (P.nW + 1), α ^ (a : ℕ) = gl.val (cr.get (a.cast hn.symm)).2)
    (hu : ∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ y ∈ cr, wsClaimShape lay y.1 = .ok ())
    (H : ∀ a : Fin P.nW,
      tval (P.wp0.ten a st) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
        claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm)))
          (cr.get (a.castSucc.cast hn.symm)).1)
    (HE : tval (tenEF P st) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
      claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm)))
        (cr.get ((Fin.last P.nW).cast hn.symm)).1)
    (ho : wo.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)))
    {w : WsPending} (hw : wsPending lay wo claims S = .ok w) :
    WoSaysF P st α wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j +
        P.msg mm P.c7 * gl.val wo.beta = gl.val wo.fvp := by
  have el : (List.ofFn fun a : Fin (P.nW + 1) =>
      ((cr.get (a.cast hn.symm)).1, (cr.get (a.cast hn.symm)).2)) = cr := by
    apply List.ext_get
    · rw [List.length_ofFn, hn]
    · intro i h1 h2
      rw [List.get_ofFn]
      rfl
  have H' : ∀ a : Fin (P.nW + 1),
      tval ((Fin.snoc (α := fun _ => (Fin P.hW → GE) × ((Fin P.kW → Bool) → GE))
          (fun a => P.wp0.ten a st) (tenEF P st) : Fin (P.nW + 1) → _) a)
          (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
        claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm))) (cr.get (a.cast hn.symm)).1 := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Fin.snoc_last]
      exact HE
    · rw [Fin.snoc_castSucc]
      exact H i
  have e := rows_pend_at gl gl_numerals lay hk (P.Wn (P.msg mm)) wo claims S (h := P.hW)
    (fun a : Fin (P.nW + 1) => α ^ (a : ℕ))
    (Fin.snoc (α := fun _ => (Fin P.hW → GE) × ((Fin P.kW → Bool) → GE))
      (fun a => P.wp0.ten a st) (tenEF P st))
    (fun a => (cr.get (a.cast hn.symm)).1) (fun a => (cr.get (a.cast hn.symm)).2) hco
    (fun a => hu _ (List.get_mem _ _)) (fun a => hs _ (List.get_mem _ _)) H'
    (by rw [el]; exact ho) hw
  unfold WoSaysF Pending
  have e1 : (∑ r, Gated.rowW (fun a : Fin (P.wp0.n + 1) => α ^ (a : ℕ))
        (Fin.snoc (α := fun _ => (Fin P.wp0.h → GE) × ((Fin P.wp0.k → Bool) → GE))
          (fun a => P.wp0.ten a st) (tenEF P st))
        (fun i => gl.val (wo.rm.getD i.1 zeroE)) r *
      Alg.mle (P.wp0.Wm (P.msg mm) r) (fun i => gl.val (wo.rm.getD i.1 zeroE))) =
      ∑ j ∈ range (2 ^ S.kRow),
        pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j := e
  have e2 : (∑ r, Gated.rowWF P.wp0 (tenEF P) st α (fun i => gl.val (wo.rm.getD i.1 zeroE)) r *
      Alg.mle (P.wp0.Wm (P.msg mm) r) (fun i => gl.val (wo.rm.getD i.1 zeroE))) =
      ∑ j ∈ range (2 ^ S.kRow),
        pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j := by
    rw [← e1]
    exact Finset.sum_congr rfl fun r _ => by rw [rowWF_snoc]
  rw [e2]
  exact Iff.rfl

/-- **The first group's named sentence, of the row that `pendingRowO` returns.** -/
theorem woSaysF_iff_row (P : FullFPar GE M X) (st : St7 GE P.wp0.n) (α : GE) (wo : WsForkOut)
    (mm : M) (lay : WsLay) (hk : P.kW = lay.lk) (claims : ℕ) (S : Params.LinShape)
    (cr : List (WsClaim × E)) (hn : cr.length = P.nW + 1)
    (hco : ∀ a : Fin (P.nW + 1), α ^ (a : ℕ) = gl.val (cr.get (a.cast hn.symm)).2)
    (hu : ∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ y ∈ cr, wsClaimShape lay y.1 = .ok ())
    (H : ∀ a : Fin P.nW,
      tval (P.wp0.ten a st) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
        claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm)))
          (cr.get (a.castSucc.cast hn.symm)).1)
    (HE : tval (tenEF P st) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
      claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm)))
        (cr.get ((Fin.last P.nW).cast hn.symm)).1)
    (ho : wo.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)))
    {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO lay im wo claims S os = .ok (r, os')) (idx : ℕ → GE)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = P.msg mm P.c7) :
    WoSaysF P st α wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl lay.lk r.psi.reverse.toArray (P.Wn (P.msg mm)) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  obtain ⟨w, l, c, l', hw, _, _, er, _, e6, e7, e8⟩ := pend_inv hr
  rw [woSaysF_iff_list P st α wo mm lay hk claims S cr hn hco hu hs H HE ho hw]
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

#print axioms OnBytes.Road.K4.rowWF_snoc
#print axioms OnBytes.Road.K4.woSaysF_iff_list
#print axioms OnBytes.Road.K4.woSaysF_iff_row
