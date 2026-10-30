-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Port.lean: the proved block's second output claim at the record G is the pending row AS wsPending RETURNS IT.

Prog.lean reads the row on the end value (MergeL.EV) as an equation with the row weights Gam that wsPending folds. wsPending then cuts the stretch of the claims' units out of Gam and spells it as
a list of vectors of product form. Johnson/Road/Rows/PendingPort.lean and StretchLaws.lean follow that step (pending_port_free). Here the two are joined:
    G_EV_port   EV at the output o  ⇔  the sum over the rows j of the cube of (the sum of the returned vectors' entries at j, read) * (row j of W read at the point)
                                        + (the entry cAt) * beta = the end value
    G_EV_row    the same with beta and the end value as the returned record has them, where the typed output's are their readings
The premises: those of Prog.lean's G_EV_pending, with «the fold returns» replaced by «wsPending returns», and: what the merge leaves of the claims (recs) is what wsForkEnd makes.
SPENT OF THE LIBRARY: OnBytes.Road.Rows.pending_port_free (Johnson/Road/Rows/StretchLaws.lean): a statement on the pure function wsPending and plain records.
Limits: how the test on the matrix reads the returned record is not looked at. Nothing on the state's reading. On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.Prog
import Johnson.Road.Rows.StretchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (Reading WsClaim WsForkOut WsPending wsPending wsEpsT wsRowPart)
open OnBytes.Road (Numerals rowAt)
open OnBytes.Road.Rows (pendWeight)
open Finset

variable {E' : Type} [Field E'] [Fintype E'] {ρ : Reading E'}

/-- **The row on the end value is the pending row as wsPending returns it.** -/
theorem G_EV_port (hρ : Numerals ρ) (P : Place) (T : Letters E' P) (o : (G P T).L.T.par.Out) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (rho : Fin P.n → E) (wo : WsForkOut) (hk : 0 < P.lay.lk) (F : Fit ρ P T o.st.1 cl) (hr : ∀ a, ρ.val (rho a) = o.st.2 ^ (a : ℕ))
    (hp : (G P T).L.oPt o = pointOf ρ P.lay.lk wo.rm)
    (ho : wo.recs = (List.ofFn fun a => (cl a, rho a)).map fun y => wsRowPart P.lay y.1 (mulE y.2 (wsEpsT P.lay y.1 wo.rm)))
    {claims : ℕ} {S : Params.LinShape} {w : WsPending} (h : wsPending P.lay wo claims S = .ok w) :
    (G P T).L.EV o m ↔
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ P.lay.lk wo.rm (Wof P fun rc => m (.inl rc)) j +
        m (.inr T.cAt) * (G P T).L.oBe o = o.vals () := by
  obtain ⟨-, -, -, e⟩ := OnBytes.Road.Rows.pending_port_free ρ hρ P.lay (Wof P fun rc => m (.inl rc)) wo claims S _ ho h
  unfold Cb.Pv.Lay.MergeL.EV
  rw [hp, show (G P T).L.f o.st m (pointOf ρ P.lay.lk wo.rm) = _ from G_f_fmAt hρ P T o.st.1 o.st.2 m cl rho wo.rm hk F hr, e]
  exact Iff.rfl

/-- The same, with beta and the end value as the returned record has them. -/
theorem G_EV_row (hρ : Numerals ρ) (P : Place) (T : Letters E' P) (o : (G P T).L.T.par.Out) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (rho : Fin P.n → E) (wo : WsForkOut) (hk : 0 < P.lay.lk) (F : Fit ρ P T o.st.1 cl) (hr : ∀ a, ρ.val (rho a) = o.st.2 ^ (a : ℕ))
    (hp : (G P T).L.oPt o = pointOf ρ P.lay.lk wo.rm)
    (ho : wo.recs = (List.ofFn fun a => (cl a, rho a)).map fun y => wsRowPart P.lay y.1 (mulE y.2 (wsEpsT P.lay y.1 wo.rm)))
    (hb : (G P T).L.oBe o = ρ.val wo.beta) (hv : o.vals () = ρ.val wo.fvp)
    {claims : ℕ} {S : Params.LinShape} {w : WsPending} (h : wsPending P.lay wo claims S = .ok w) :
    (G P T).L.EV o m ↔
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ P.lay.lk wo.rm (Wof P fun rc => m (.inl rc)) j +
        m (.inr T.cAt) * ρ.val w.beta = ρ.val w.target := by
  obtain ⟨-, e2, e3, -⟩ := OnBytes.Road.Rows.pending_port_free ρ hρ P.lay (Wof P fun rc => m (.inl rc)) wo claims S _ ho h
  rw [G_EV_port hρ P T o m cl rho wo hk F hr hp ho h, hb, hv, e2, e3]

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.G_EV_port
#print axioms VerifiableInference.Desc.First.K11Caller.G_EV_row
