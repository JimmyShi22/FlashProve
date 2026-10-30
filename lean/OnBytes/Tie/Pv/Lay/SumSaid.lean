-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/SumSaid.lean: what the typed output says of the port's record of a masked
sumcheck, in one record, from what the port's seams give.

The seams of the port's engines (OnBytes/Tie/Pv/Psc/Run/) end in the same facts on the sumcheck's
record behind the round of the end values (`Ended`). This file turns these, for parameters `SumL`
and a pick under which the port's weights fit, into the facts on the typed output of
OnBytes/Tie/Pv/Lay/SumTie.lean, once for all engines.

Main names:
  `sizes_of`: each round has one scalar fewer than its weight's number of coefficients.
  `map_ofFn`: a list of length k, mapped, as a list by a function on the numbers below k.
  `SumSaid`: of the typed output `sumOut` on what was heard: the port's rounds are read as its
    transcript; its eps, last value, point and last coordinate are the record's and the lists',
    read; its end values are the function vals that is given; the record is as `PscAt` asks.
  `sum_said`: `SumSaid` from `Ended`, `Fits` and the rounds' lengths.
  `SumSaid.row`: the record's row form at a summand S0 and a kept form is worth 0 exactly if the
    typed row claim holds, under a lawful pick and (D1) to (D4) of `sum_row`.

Limits: as in OnBytes/Tie/Pv/Lay/SumTie.lean. The end values vals are a free letter of `SumSaid`:
that they are the readings of the scalars that were heard hangs on the numbering of the end values,
and is said where a numbering is given (`sum_end_world`, OnBytes/Tie/Pv/Lay/SumTie.lean; `tok_tie`,
OnBytes/Tie/Pv/Lay/SumTop.lean).
-/
import OnBytes.Tie.Pv.Lay.SumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att
open OnBytes.Psc (Weight)

theorem sizes_of : ∀ (ws : List Weight) (rs : List (List E × E)), rs.length = ws.length →
    (∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d) → rs.map (·.1.length) = ws.map fun w => w.d - 1
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | w :: ws, r :: rs, h, hs => by
    have h0 : r.1.length + 1 = w.d := hs (w, r) (by simp)
    have h1 := sizes_of ws rs (by simpa using h) fun x hx => hs x (by
      simp only [List.zip_cons_cons, List.mem_cons]
      exact Or.inr hx)
    rw [List.map_cons, List.map_cons, h1]
    congr 1
    omega

theorem map_ofFn {α β : Type} (f : α → β) (d : α) : ∀ (k : ℕ) (l : List α), l.length = k →
    l.map f = List.ofFn fun i : Fin k => f (l.getD i.1 d)
  | 0, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | k + 1, [], h => by simp at h
  | k + 1, a :: l, h => by
    rw [List.ofFn_succ, List.map_cons, map_ofFn f d k l (by simpa using h)]
    rfl

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- What the typed output says of the port's record. -/
structure SumSaid (L : SumL K) (F : ∀ st, HFixs (L.T.par.vars st)) (st : L.St)
    (p : OnBytes.Model.Psc) (ws : List Weight) (mu : E) (rs : List (List E × E)) (sentY : List E)
    (beta : E) (hβ : ρ.val beta ≠ 0) (vals : L.S.A → K) : Prop where
  fits : Fits ρ ws L.T.par.fmt (L.T.par.dat st) (F st)
  lens : rs.map (·.1.length) = List.ofFn L.M.n
  lenY : sentY.length = L.M.DY
  reads : ReadsAs ρ (rs ++ [(sentY, beta)]) L.T.par.fmt [pRoundV K L.T.par.A]
    (sumTr ρ L rs sentY beta hβ vals)
  psc : PscAt p ws (rs ++ [(sentY, beta)]) mu
  eps : (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).eps = ρ.val p.eps
  fin : (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).fin = ρ.val p.claim
  pt : ∀ i : Fin L.S.k, L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) i =
    ρ.val (rs.getD i.1 ([], zeroE)).2
  last : L.Q.outB L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) = ρ.val beta
  vals : (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals = vals

theorem sum_said (L : SumL K) (F : ∀ st, HFixs (L.T.par.vars st)) (st : L.St)
    {p : OnBytes.Model.Psc} {C : Aff} {τ mu eps : E} {first : ℕ} {ws : List Weight}
    {rs : List (List E × E)} {sentY : List E} {beta : E}
    (a : Ended p C τ mu eps first ws rs L.M.DY sentY beta) (hβ : ρ.val beta ≠ 0)
    (vals : L.S.A → K)
    (hfit : Fits ρ (ws ++ [Weight.atZero (L.M.DY + 1)]) L.T.par.fmt (L.T.par.dat st) (F st))
    (hl : rs.map (·.1.length) = List.ofFn L.M.n) (hY : sentY.length = L.M.DY) :
    SumSaid ρ L F st p (ws ++ [Weight.atZero (L.M.DY + 1)]) mu rs sentY beta hβ vals where
  fits := hfit
  lens := hl
  lenY := hY
  reads := sum_reads ρ L rs sentY beta hβ vals hl hY
  psc := ended_pscAt a
  eps := rfl
  fin := by
    rw [sum_fin ρ L F st _ _ _ rs sentY beta hβ vals _ hfit hl hY, a.claim, a.eps, a.target]
  pt := sum_ini ρ L F st _ _ _ rs sentY beta hβ vals
  last := sum_last ρ L F st _ _ _ rs sentY beta hβ vals
  vals := sum_vals ρ L F st _ _ _ rs sentY beta hβ vals

theorem SumSaid.row {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (S0 : E) (kept : Aff) (m : L.J → K)
    (D1 : L.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.T.par.vars st) p.first)
    (D2 : L.T.par.inc st m = ρ.val p.target - p.start.value ρ W)
    (D3 : ∑ b, L.Q.polB st
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) vals b *
        L.Q.Fb st m b
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) =
      kept.value ρ W)
    (D4 : L.S.pol st (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))
        vals = ρ.val S0) :
    (p.rowForm S0 kept).value ρ W = 0 ↔
      L.T.par.UHolds (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) m :=
  sum_row ρ L F st mu rs sentY beta hβ vals hF Ex y W p ws S0 kept m s.psc s.fits s.lens s.lenY
    D1 D2 (by rw [s.vals]; exact D3) (by rw [s.vals]; exact D4)

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_said
#print axioms OnBytes.Tie.Pv.Lay.Eng.SumSaid.row
