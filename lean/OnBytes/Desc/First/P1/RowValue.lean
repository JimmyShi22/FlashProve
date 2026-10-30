-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/RowValue.lean: WHAT A SUMCHECK'S OWN ROW IS WORTH, AS A VALUE, not only
whether it is worth 0. `SumSaid.row` (OnBytes/Tie/Pv/Lay/SumSaid.lean) and `row_uForm`
(RowForms.lean) say when the record's row form is worth 0. Beneath them lies the equation
`seam_value` (OnBytes/Tie/Pv/Seam.lean), stated under the record `RowTie`. Here `RowTie` is had from
`SumSaid`, and the equation is said at the typed output `sumOut`; then for the form that the layers'
text makes of the terms' sumcheck (the row without summand and kept terms, scaled). Statements and
proofs.

  `said_rowTie`: under a lawful pick, and (D1), (D2) at every m in the worlds of a ledger H: `RowTie
    ρ L.T.par H mask entry p (sumOut …)`.
  `said_row_value`: so `(p.rowForm S0 kept).value ρ W = hU … + eps * hPsi … * inc st m + eps *
    kept.value ρ W - (fin - eps * ρ.val S0)`, W the world of H at m, eps and fin the typed output's.
  `tie_scaled_over`, `said_scaled_over`: for a word k with ρ.val k * ρ.val p.eps = -1: `((p.rowForm
    zeroE {}).scale k).value ρ W = overAt L.T.par (sumOut …) m + ‹the summand's public part at the
    output›` (`overAt`, Cb/Pv/Lay/Over.lean).

NO NEW ARGUMENT: `rowTie_of_tie` (OnBytes/Tie/Pv/SeamRun.lean), `outS_shortV`, `zip_ne`
(OnBytes/Tie/Pv/Att/RowTie.lean), `seam_value`, `Aff.value_scale`; a division by eps.

Limits. (D1), (D2), the lawful pick and hk ARE PREMISES. Equations in one world: no draw. Nothing on
soundness.
-/
import OnBytes.Tie.Pv.Lay.SumSaid
import OnBytes.Tie.Pv.SeamRun
import OnBytes.Tie.Pv.Att.RowTie
import Cb.Pv.Lay.Over

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv (RowTie rowTie_of_tie seam_value)
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Road.Hd (place)
open OnBytes.Psc (Weight)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **`RowTie` from `SumSaid`.** -/
theorem said_rowTie {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (H : Fork) (mask : (L.T.par.J → K) → ℕ → K)
    (entry : (L.T.par.J → K) → ℕ → ℕ → ℕ → K)
    (D1 : ∀ m, L.T.par.W st m =
      place (H.worldOf ρ (mask m) (entry m)).slot (L.T.par.vars st) p.first)
    (D2 : ∀ m, L.T.par.inc st m =
      ρ.val p.target - p.start.value ρ (H.worldOf ρ (mask m) (entry m))) :
    RowTie ρ L.T.par H mask entry p (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) := by
  have e : outS L.T.par (ρ.val p.target, st) (F st) Ex
      (((), ρ.val mu), ρ.val p.eps, sumTr ρ L rs sentY beta hβ vals) =
      sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals :=
    outS_shortV L.T.par F hF Ex y (ρ.val p.target, st) _
  have hne : L.T.par.fmt ≠ [] := by
    show ldPartFmt K L.S.k L.M.n ++ [pDummy K L.M.DY] ≠ []
    simp
  have t := rowTie_of_tie ρ L.T.par Ex H mask entry p ws (rs ++ [(sentY, beta)]) mu st (F st)
    (sumTr ρ L rs sentY beta hβ vals) s.psc s.fits s.reads
    (zip_ne ρ _ _ _ _ _ _ _ hne s.fits s.reads) D1 D2
  rw [e] at t
  exact t

/-- **What the record's row form is worth.** -/
theorem said_row_value {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (H : Fork) (mask : (L.T.par.J → K) → ℕ → K)
    (entry : (L.T.par.J → K) → ℕ → ℕ → ℕ → K)
    (D1 : ∀ m, L.T.par.W st m =
      place (H.worldOf ρ (mask m) (entry m)).slot (L.T.par.vars st) p.first)
    (D2 : ∀ m, L.T.par.inc st m =
      ρ.val p.target - p.start.value ρ (H.worldOf ρ (mask m) (entry m)))
    (m : L.T.par.J → K) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ (H.worldOf ρ (mask m) (entry m)) =
      hU (L.T.par.vars st) (L.T.par.W st m)
          (L.T.par.hp st (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).pt) +
        (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).eps *
          hPsi (L.T.par.vars st)
            (L.T.par.hp st (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).pt) *
          L.T.par.inc st m +
        (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).eps *
          kept.value ρ (H.worldOf ρ (mask m) (entry m)) -
        ((sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).fin -
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).eps * ρ.val S0) :=
  seam_value (said_rowTie ρ s hF Ex y H mask entry D1 D2) m S0 kept

omit [Fintype K] in
/-- The row without summand and kept terms, scaled by minus the inverse of eps: under `RowTie`. -/
theorem tie_scaled_over {Y : PscPar K} {H : Fork} {mask : (Y.J → K) → ℕ → K}
    {entry : (Y.J → K) → ℕ → ℕ → ℕ → K} {p : OnBytes.Model.Psc} {o : Y.Out}
    (t : RowTie ρ Y H mask entry p o) (m : Y.J → K) (k : E)
    (hk : ρ.val k * ρ.val p.eps = -1) :
    ((p.rowForm zeroE {}).scale k).value ρ (H.worldOf ρ (mask m) (entry m)) =
      overAt Y o m + Y.S0 o.st (Y.hp o.st o.pt) o.vals := by
  have hne : ρ.val p.eps ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    have h1 : (1 : K) = 0 := by linear_combination hk
    exact one_ne_zero h1
  have hk' : ρ.val k = -(ρ.val p.eps)⁻¹ := by
    field_simp
    linear_combination hk
  rw [Aff.value_scale, seam_value t m zeroE {}, Aff.value_empty, ρ.zero]
  unfold overAt
  rw [t.eps, hk']
  field_simp
  ring

/-- **The row without summand and kept terms, scaled by minus the inverse of eps.** -/
theorem said_scaled_over {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (H : Fork) (mask : (L.T.par.J → K) → ℕ → K)
    (entry : (L.T.par.J → K) → ℕ → ℕ → ℕ → K)
    (D1 : ∀ m, L.T.par.W st m =
      place (H.worldOf ρ (mask m) (entry m)).slot (L.T.par.vars st) p.first)
    (D2 : ∀ m, L.T.par.inc st m =
      ρ.val p.target - p.start.value ρ (H.worldOf ρ (mask m) (entry m)))
    (m : L.T.par.J → K) (k : E) (hk : ρ.val k * ρ.val p.eps = -1) :
    ((p.rowForm zeroE {}).scale k).value ρ (H.worldOf ρ (mask m) (entry m)) =
      overAt L.T.par (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) m +
        L.T.par.S0 st
          (L.T.par.hp st (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).pt)
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals := by
  exact tie_scaled_over ρ (said_rowTie ρ s hF Ex y H mask entry D1 D2) m k hk

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.said_rowTie
#print axioms OnBytes.Desc.First.P1.said_row_value
#print axioms OnBytes.Desc.First.P1.tie_scaled_over
#print axioms OnBytes.Desc.First.P1.said_scaled_over
