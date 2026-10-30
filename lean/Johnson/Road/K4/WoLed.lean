-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoLed.lean: THE NAMED SENTENCE `WoSays` IN THE PROGRAM's OWN WORDS. `WoSays P st wo
m` (OwnPending.lean) is the library's pending row at the merge's record's words, with its row
weights AT THE TYPED STATE st. Here it is the sentence on what the program's `wsPending` returns on
that record: the sum over the cube's rows of `pendWeight` times the committed matrix's row read at
the merge's point, plus the mask entry times the factor, is the shown value. It has the shape of
`RowSays` (Johnson/Top/H0/MergeLaw/WoRow.lean: "a row on the committed matrix holds") at the row
made of that return; two ties to it stay owed (Limits). `WoSays` here is OnBytes.Road.K4.WoSays, not
the sentence of that name in Johnson/Top/H0/K11Caller. Statements and proofs.

  `rows_pend_at`: `rows_pend` (WoJoint.lean) at a number k of column bits that is the layout's by an
    equation, not by its text.
  `woSays_iff`: `WoSays P st wo mm ↔ ∑ j ∈ range (2 ^ S.kRow), pendWeight gl w.g j * rowAt gl lay.lk
    wo.rm (P.Wn (P.msg mm)) j + P.msg mm P.c7 * gl.val wo.beta = gl.val wo.fvp`.
  `woSays_iff_list`: the same with the claims and their coefficients as one list cr, as the
    program's text has them.

NO NEW ARGUMENT: `rows_pend`; the definitions of `WoSays`, `Pending` and `wPar`
(Cb/Pv/Lay/At/SeamW.lean).

Limits. PREMISES: the typed matrix has as many column bits as the layout; (H): EACH TYPED PAIR
`P.wp0.ten a st.1` AND ITS CLAIM `cs a` ARE ONE FUNCTIONAL at the matrix `starW`; the layout has
each claim's unit, `UnitOK`, `wsClaimShape`; the powers of st.2 are the readings of the program's
coefficients; the record's `recs` are made of the claims as the program's text makes them;
`wsPending` returns. The claims cs and the coefficients rho are letters: that they are the hearing's
is not said here. OWED TOWARDS `RowSays`: that its cells are `P.Wn (P.msg mm)`, and that its index
masks' entry is `P.msg mm P.c7`. An equivalence of two sentences on numbers: no draw. Nothing on
soundness.
-/
import Johnson.Road.K4.WoJoint
import Johnson.Road.K4.OwnPending

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Reading WsLay WsUnit WsClaim WsForkOut WsPending wsEpsT wsRowPart
  wsClaimShape wsPending)
open Cb.Pv.Lay.At (tval summand)
open Cb.Pv.Lay.End.Gated (Pending)
open Inst.Model.Layout.Tensor (matOf)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)
open Inst.Model (Scl)

/-- `rows_pend` at a number of column bits that is the layout's by an equation. -/
theorem rows_pend_at {K : Type} [Field K] (ρ : Reading K) (hρ : Numerals ρ) (lay : WsLay) {k : ℕ}
    (hk : k = lay.lk) (M : Wm K) (o : WsForkOut) (claims : ℕ) (S : Params.LinShape) {h n : ℕ}
    (co : Fin n → K) (ten : Fin n → (Fin h → K) × ((Fin k → Bool) → K)) (cs : Fin n → WsClaim)
    (rho : Fin n → E) (hco : ∀ a, co a = ρ.val (rho a))
    (hu : ∀ a, ∃ u, lay.U[(cs a).ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ a, wsClaimShape lay (cs a) = .ok ())
    (H : ∀ a, tval (ten a) (matOf (starW ρ k o.rm M)) = claimVal ρ lay (starW ρ k o.rm M) (cs a))
    (ho : o.recs = (List.ofFn fun a => (cs a, rho a)).map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (hw : wsPending lay o claims S = .ok w) :
    ∑ r, Cb.Pv.Lay.End.Gated.rowW co ten (fun i : Fin k => pt ρ o.rm i) r *
        Alg.mle (matOf (h := h) M r) (fun i : Fin k => pt ρ o.rm i) =
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ lay.lk o.rm M j := by
  subst hk
  exact rows_pend ρ hρ lay M o claims S co ten cs rho hco hu hs H ho hw

variable [scl : Scl] {M X : Type}

/-- **The named sentence in the program's own words.** -/
theorem woSays_iff (P : FullPar GE M X) (st : St7 GE P.wp0.n × GE) (wo : WsForkOut) (mm : M)
    (lay : WsLay) (hk : P.kW = lay.lk) (claims : ℕ) (S : Params.LinShape)
    (cs : Fin P.nW → WsClaim) (rho : Fin P.nW → E)
    (hco : ∀ a : Fin P.nW, st.2 ^ (a : ℕ) = gl.val (rho a))
    (hu : ∀ a, ∃ u, lay.U[(cs a).ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ a, wsClaimShape lay (cs a) = .ok ())
    (H : ∀ a, tval (P.wp0.ten a st.1) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
      claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm))) (cs a))
    (ho : wo.recs = (List.ofFn fun a => (cs a, rho a)).map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)))
    {w : WsPending} (hw : wsPending lay wo claims S = .ok w) :
    WoSays P st wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j +
        P.msg mm P.c7 * gl.val wo.beta = gl.val wo.fvp := by
  have e := rows_pend_at gl gl_numerals lay hk (P.Wn (P.msg mm)) wo claims S (h := P.hW)
    (fun a : Fin P.nW => st.2 ^ (a : ℕ)) (fun a => P.wp0.ten a st.1) cs rho hco hu hs H ho hw
  unfold WoSays Pending
  have e2 : (∑ r, Cb.Pv.Lay.End.Gated.rowW (fun c : Fin P.wp0.n => st.2 ^ (c : ℕ))
        (fun c => P.wp0.ten c st.1) (fun i => gl.val (wo.rm.getD i.1 zeroE)) r *
      Alg.mle (P.wp0.Wm (P.msg mm) r) (fun i => gl.val (wo.rm.getD i.1 zeroE))) =
      ∑ j ∈ range (2 ^ S.kRow),
        pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j := e
  rw [e2]
  exact Iff.rfl

/-- **The same with the claims and their coefficients as ONE LIST**, as the program's text has them
(`flatForkEnd`, OnBytes/K/Kc/QuietLink.lean: `(cl.zip rho).toList`). -/
theorem woSays_iff_list (P : FullPar GE M X) (st : St7 GE P.wp0.n × GE) (wo : WsForkOut) (mm : M)
    (lay : WsLay) (hk : P.kW = lay.lk) (claims : ℕ) (S : Params.LinShape)
    (cr : List (WsClaim × E)) (hn : cr.length = P.nW)
    (hco : ∀ a : Fin P.nW, st.2 ^ (a : ℕ) = gl.val (cr.get (a.cast hn.symm)).2)
    (hu : ∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ y ∈ cr, wsClaimShape lay y.1 = .ok ())
    (H : ∀ a : Fin P.nW,
      tval (P.wp0.ten a st.1) (matOf (starW gl P.kW wo.rm (P.Wn (P.msg mm)))) =
        claimVal gl lay (starW gl P.kW wo.rm (P.Wn (P.msg mm))) (cr.get (a.cast hn.symm)).1)
    (ho : wo.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)))
    {w : WsPending} (hw : wsPending lay wo claims S = .ok w) :
    WoSays P st wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl w.g j * rowAt gl lay.lk wo.rm (P.Wn (P.msg mm)) j +
        P.msg mm P.c7 * gl.val wo.beta = gl.val wo.fvp := by
  have el : (List.ofFn fun a : Fin P.nW =>
      ((cr.get (a.cast hn.symm)).1, (cr.get (a.cast hn.symm)).2)) = cr := by
    apply List.ext_get
    · rw [List.length_ofFn, hn]
    · intro i h1 h2
      rw [List.get_ofFn]
      rfl
  refine woSays_iff P st wo mm lay hk claims S (fun a => (cr.get (a.cast hn.symm)).1)
    (fun a => (cr.get (a.cast hn.symm)).2) hco (fun a => hu _ (List.get_mem _ _))
    (fun a => hs _ (List.get_mem _ _)) H ?_ hw
  rw [el]
  exact ho

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rows_pend_at
#print axioms OnBytes.Road.K4.woSays_iff
#print axioms OnBytes.Road.K4.woSays_iff_list
