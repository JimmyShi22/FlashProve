-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/RowValueAt.lean: WHAT A SUMCHECK'S OWN ROW IS WORTH, AT ONE m IN ONE WORLD.
RowValue.lean says it under the record `RowTie` (OnBytes/Tie/Pv/Seam.lean), whose fields
`hid` and `inc` ask their ties AT EVERY m, in the worlds of one ledger with masks and entries as
functions of m. Where one mask row, one table of entries and one m are given, a constant function of
m does not meet these fields; whether other functions that take the given row at the given m do has
been held by nobody. Here the record is cut in two: `RowAt` holds what speaks of no world
(`RowTie`'s first four fields), and the two ties are asked at the one m, in any world. Definitions,
statements and proofs.

  `RowAt ρ Y p o`: the record's walk matches the typed variables at the output's point; it is not
    empty; the output's eps and last claim are the record's, read.
  `rowAt_of_tie`, `said_rowAt`: `RowAt` at the short sumcheck's output, and from `SumSaid` at
    `sumOut`.
  `RowAt.value`: under (D1) and (D2) at m in the world W: `(p.rowForm S0 kept).value ρ W = hU … +
    eps * hPsi … * inc st m + eps * kept.value ρ W - (fin - eps * ρ.val S0)`.
  `RowAt.scaled_over`, `scaled_over_at`: for a word k with ρ.val k * ρ.val p.eps = -1: `((p.rowForm
    zeroE {}).scale k).value ρ W = overAt Y o m + ‹the summand's public part at the output›`; the
    second at `sumOut`, from `SumSaid`.

NO NEW ARGUMENT: the proofs of `rowTie_of_tie` (OnBytes/Tie/Pv/SeamRun.lean) and
`seam_value` (OnBytes/Tie/Pv/Seam.lean), each of which reads one m at a time; `tie_scaled_over`'s
algebra (RowValue.lean).

Limits. (D1), (D2) at m, the lawful pick and hk ARE PREMISES. Equations in one world: no draw.
Nothing on soundness.
-/
import OnBytes.Desc.First.P1.RowValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Road.Hd Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight)

section Row
variable {K : Type} [Field K] (ρ : Reading K)

/-- How the output statement o lies against the record p, as far as no world is spoken of. -/
structure RowAt (Y : PscPar K) (p : Psc) (o : Y.Out) : Prop where
  walk : Match ρ (zipT p.vars.toList p.r.toList) (Y.vars o.st) (Y.hp o.st o.pt)
  ne : zipT p.vars.toList p.r.toList ≠ []
  eps : o.eps = ρ.val p.eps
  fin : o.fin = ρ.val p.claim

variable {ρ}

/-- **What the record's row form is worth, at one m in one world.** -/
theorem RowAt.value {Y : PscPar K} {p : Psc} {o : Y.Out} (t : RowAt ρ Y p o) (W : World K)
    (m : Y.J → K) (hid : Y.W o.st m = place W.slot (Y.vars o.st) p.first)
    (inc : Y.inc o.st m = ρ.val p.target - p.start.value ρ W) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ W =
      hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
        o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
        o.eps * kept.value ρ W - (o.fin - o.eps * ρ.val S0) := by
  obtain ⟨a1, a2⟩ := walk_hU ρ W.slot _ _ _ p.first t.ne t.walk
  have b1 : sumFrom (fun j y => ρ.val y * W.slot j) p.first p.walk.1 =
      hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) := by
    rw [hid]
    exact a1
  have b2 : ρ.val p.walk.2 = hPsi (Y.vars o.st) (Y.hp o.st o.pt) := a2
  rw [Psc.rowForm_value, b1, b2, ← inc, ← t.eps, ← t.fin]

/-- The row without summand and kept terms, scaled by minus the inverse of eps, at one m. -/
theorem RowAt.scaled_over {Y : PscPar K} {p : Psc} {o : Y.Out} (t : RowAt ρ Y p o) (W : World K)
    (m : Y.J → K) (hid : Y.W o.st m = place W.slot (Y.vars o.st) p.first)
    (inc : Y.inc o.st m = ρ.val p.target - p.start.value ρ W) (k : E)
    (hk : ρ.val k * ρ.val p.eps = -1) :
    ((p.rowForm zeroE {}).scale k).value ρ W =
      overAt Y o m + Y.S0 o.st (Y.hp o.st o.pt) o.vals := by
  have hne : ρ.val p.eps ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    have h1 : (1 : K) = 0 := by linear_combination hk
    exact one_ne_zero h1
  have hk' : ρ.val k = -(ρ.val p.eps)⁻¹ := by
    field_simp
    linear_combination hk
  rw [Aff.value_scale, t.value W m hid inc zeroE {}, Aff.value_empty, ρ.zero]
  unfold overAt
  rw [t.eps, hk']
  field_simp
  ring

end Row

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- `RowAt` at the short sumcheck's output. -/
theorem rowAt_of_tie (Y : PscPar K) (Ex : ExtSpec) (p : Psc) (ws : List Weight)
    (rs : List (List E × E)) (mu : E) (st : Y.St) (Fx : HFixs (Y.vars st))
    (τ : Tr (sRounds Y.fmt ++ [pRoundV K Y.A])) (hp : PscAt p ws rs mu)
    (hF : Fits ρ ws Y.fmt (Y.dat st) Fx) (hR : ReadsAs ρ rs Y.fmt [pRoundV K Y.A] τ)
    (hne : ws.zip (rs.map (·.2)) ≠ []) :
    RowAt ρ Y p (outS Y (ρ.val p.target, st) Fx Ex (((), ρ.val mu), ρ.val p.eps, τ)) where
  walk := by
    rw [zipT_eq, hp.vars, hp.r]
    exact match_of ρ ws rs Y.fmt (Y.dat st) Fx [pRoundV K Y.A] τ
      (ρ.val mu + ρ.val p.eps * ρ.val p.target) hF hR
  ne := by
    rw [zipT_eq, hp.vars, hp.r]
    exact hne
  eps := rfl
  fin := by
    have hc := claimAfter_hFin ρ ws rs Y.fmt (Y.dat st) Fx [pRoundV K Y.A] τ
      (addE mu (mulE p.eps p.target)) hF hR
    rw [← hp.claim, ρ.add, ρ.mul] at hc
    exact hc.symm

/-- **`RowAt` from `SumSaid`.** -/
theorem said_rowAt {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) :
    RowAt ρ L.T.par p (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) := by
  have e : outS L.T.par (ρ.val p.target, st) (F st) Ex
      (((), ρ.val mu), ρ.val p.eps, sumTr ρ L rs sentY beta hβ vals) =
      sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals :=
    outS_shortV L.T.par F hF Ex y (ρ.val p.target, st) _
  have hne : L.T.par.fmt ≠ [] := by
    show ldPartFmt K L.S.k L.M.n ++ [pDummy K L.M.DY] ≠ []
    simp
  have t := rowAt_of_tie ρ L.T.par Ex p ws (rs ++ [(sentY, beta)]) mu st (F st)
    (sumTr ρ L rs sentY beta hβ vals) s.psc s.fits s.reads
    (zip_ne ρ _ _ _ _ _ _ _ hne s.fits s.reads)
  rw [e] at t
  exact t

/-- **The row without summand and kept terms, scaled, at one m in one world, at `sumOut`.** -/
theorem scaled_over_at {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (m : L.T.par.J → K)
    (D1 : L.T.par.W st m = place W.slot (L.T.par.vars st) p.first)
    (D2 : L.T.par.inc st m = ρ.val p.target - p.start.value ρ W) (k : E)
    (hk : ρ.val k * ρ.val p.eps = -1) :
    ((p.rowForm zeroE {}).scale k).value ρ W =
      overAt L.T.par (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) m +
        L.T.par.S0 st
          (L.T.par.hp st (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).pt)
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals :=
  (said_rowAt ρ s hF Ex y).scaled_over W m D1 D2 k hk

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.RowAt.value
#print axioms OnBytes.Desc.First.P1.RowAt.scaled_over
#print axioms OnBytes.Desc.First.P1.rowAt_of_tie
#print axioms OnBytes.Desc.First.P1.said_rowAt
#print axioms OnBytes.Desc.First.P1.scaled_over_at
