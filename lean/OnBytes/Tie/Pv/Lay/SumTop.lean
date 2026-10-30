-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/SumTop.lean: from what was heard of a masked sumcheck and the port's record
behind it to the typed output, for every sumcheck of the layers' sub-proof; the token sumcheck; the
batched sumcheck.

Main names:
  `sum_tie`: for parameters `SumL` and a pick under which the port's weights fit: if the rounds were
    heard from a context with `NzCtx` (`Parts`) and the record behind them is as `Ended` says, then
    the context that is left has `NzCtx`, the reading of beta is not 0, and `SumSaid` holds of the
    typed output (OnBytes/Tie/Pv/Lay/SumSaid.lean).
  `tok_fits`, `tok_tie`: the token sumcheck (tscIn, OnBytes/Model/Tsc.lean; its seam:
    OnBytes/Tie/Pv/Psc/Run/PscToken.lean), for parameters all of whose variables are in the equality
    form, of degree 2, under the pick `F₀`: what the seam says; the reading of the record's target
    is the reading of the claimed sum that was sent; `NzCtx` behind; `SumSaid`; and the typed claim
    on an end value holds exactly if the map at the point is what the end value's slot is worth in
    the world of the state that is left.
  `plain2_fits`, `plain2_tie`: a sumcheck of plain rounds of degree 2 (the batched sumcheck of the
    inner products), under `pick`: `sum_tie` at the port's weights.

Limits: one direction: from what was heard. `NzCtx` at the start, the readings of the equality
point, the degrees and the numbering of the end values are premises. tscIn makes no row:
`SumSaid.row` serves for the row that a caller makes. The batched sumcheck's tie starts from `Parts`
and `Ended`: the caller's routine notes values between the engine's calls, and to cut its run is the
caller's.
-/
import OnBytes.Tie.Pv.Lay.SumSaid
import OnBytes.Tie.Pv.Lay.SumFits
import OnBytes.Tie.Pv.Psc.Run.PscToken
import OnBytes.Tie.Pv.Psc.Run.NzRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att
open OnBytes.Psc (Weight hidingEntries)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem sum_tie (L : SumL K) (F : ∀ st, HFixs (L.T.par.vars st)) (st : L.St) {c c1 c' : Ctx}
    {riders : List E} {mu eps : E} {ws : List Weight} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {v : List E} {p : OnBytes.Model.Psc} {C : Aff} {τ : E} {first : ℕ}
    (a : Parts c c1 c' riders mu eps ws rs L.M.DY sentY beta v)
    (e : Ended p C τ mu eps first ws rs L.M.DY sentY beta) (hlen : rs.length = ws.length)
    (hsz : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d)
    (hd : (ws.map fun w => w.d - 1) = List.ofFn L.M.n) (hY : sentY.length = L.M.DY)
    (hfit : Fits ρ (ws ++ [Weight.atZero (L.M.DY + 1)]) L.T.par.fmt (L.T.par.dat st) (F st))
    (hc : NzCtx ρ c) (vals : L.S.A → K) :
    NzCtx ρ c' ∧ ∃ hβ : ρ.val beta ≠ 0,
      SumSaid ρ L F st p (ws ++ [Weight.atZero (L.M.DY + 1)]) mu rs sentY beta hβ vals := by
  obtain ⟨n1, n2⟩ := parts_nz ρ a hc
  exact ⟨n2, n1, sum_said ρ L F st e n1 vals hfit (by rw [sizes_of ws rs hlen hsz, hd]) hY⟩

/-! ## The token sumcheck -/

theorem tok_weights (P : Array E) (k : ℕ) (h : k ≤ P.size) :
    tokenWeights P k =
      List.ofFn fun i : Fin k => Weight.equality ((P.toList.take k).getD i.1 zeroE) 3 :=
  map_ofFn _ zeroE k _ (by rw [List.length_take, Array.length_toList]; omega)

theorem tok_fits (L : SumL K) (st : L.St) (P : Array E) (h : L.S.k ≤ P.size)
    (hn : ∀ i, L.M.n i = 2)
    (hw : ∀ i : Fin L.S.k, L.S.w st i = some (ρ.val ((P.toList.take L.S.k).getD i.1 zeroE))) :
    Fits ρ (tokenWeights P L.S.k ++ [Weight.atZero (L.M.DY + 1)]) L.T.par.fmt (L.T.par.dat st)
      (F₀ L.T.par st) := by
  have e : tokenWeights P L.S.k = List.ofFn fun i : Fin L.S.k =>
      Weight.equality ((P.toList.take L.S.k).getD i.1 zeroE) (L.M.n i + 1) := by
    rw [tok_weights P L.S.k h]
    congr 1
    funext i
    rw [hn i]
  rw [e]
  exact sum_fits_eq ρ L st _ hw

theorem tok_tie (L : SumL K) (P : Array E) (shown : ℕ) (F G : Fork) (c c' : Ctx) (t : Tsc)
    (h : tscIn P L.S.k shown L.M.DY F c = .ok ((t, G), c')) (hs : Sized F) (hc : NzCtx ρ c)
    (st : L.St) (hn : ∀ i, L.M.n i = 2)
    (hw : ∀ i : Fin L.S.k, L.S.w st i = some (ρ.val ((P.toList.take L.S.k).getD i.1 zeroE)))
    (num : L.S.A → ℕ) (hnum : ∀ a, num a < shown) :
    ∃ (x mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) (F1 : Fork)
      (c1 : Ctx),
      Parts c c1 c' [x] mu t.p.eps (tokenWeights P L.S.k) rs L.M.DY sentY beta v ∧
      v.length = shown ∧
      Ended t.p (Aff.slot F.next) (addE zeroE (mulE oneE x)) mu t.p.eps (F.next + 1)
        (tokenWeights P L.S.k) rs L.M.DY sentY beta ∧
      t.sCl = F.next ∧ t.r.toList = rs.map (·.2) ∧
      t.sEnd = t.p.first + hidingEntries (tokenWeights P L.S.k ++ [Weight.atZero (L.M.DY + 1)]) ∧
      Filled (taken F 1) F1 F.next [x] oneE ∧
      Filled (taken F1 (1 + 2 * L.S.k + L.M.DY + shown)) G t.sEnd v beta ∧
      ρ.val t.p.target = ρ.val x ∧ NzCtx ρ c' ∧ ∃ hβ : ρ.val beta ≠ 0,
        SumSaid ρ L (F₀ L.T.par) st t.p (tokenWeights P L.S.k ++ [Weight.atZero (L.M.DY + 1)]) mu
          rs sentY beta hβ (fun a => ρ.val (v.getD (num a) zeroE)) ∧
        ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : L.J → K),
          (∀ a, m (L.M.cAt a) = mask (t.sEnd + num a)) → ∀ a : L.S.A,
          (L.T.par.EHolds (sumOut ρ L (F₀ L.T.par) st t.p.target mu t.p.eps rs sentY beta hβ
              fun a => ρ.val (v.getD (num a) zeroE)) m a ↔
            L.S.F st m a (L.Q.outPt L.M (sumOut ρ L (F₀ L.T.par) st t.p.target mu t.p.eps rs
                sentY beta hβ fun a => ρ.val (v.getD (num a) zeroE))) =
              (G.worldOf ρ mask entry).slot (t.sEnd + num a)) := by
  obtain ⟨x, mu, rs, sentY, beta, v, F1, c1, a1, a2, a3, a4, _, a6, a7, _, _, a10, a11, a12, _,
    a14, a15, a16⟩ := tscIn_seam P L.S.k shown L.M.DY F G c c' t h hs
  have hd : ((tokenWeights P L.S.k).map fun w => w.d - 1) = List.ofFn L.M.n := by
    rw [tok_weights P L.S.k a2, List.map_ofFn]
    congr 1
    funext i
    exact (hn i).symm
  obtain ⟨n2, n1, s⟩ := sum_tie ρ L (F₀ L.T.par) st a1 a10
    (by rw [a3, tokenWeights_length P L.S.k a2]) a4 hd a6 (tok_fits ρ L st P a2 hn hw) hc
    (fun a => ρ.val (v.getD (num a) zeroE))
  refine ⟨x, mu, rs, sentY, beta, v, F1, c1, a1, a7, a10, a11, a12, a14, a15, a16, ?_, n2, n1, s,
    ?_⟩
  · rw [a10.target, ρ.add, ρ.mul, ρ.zero, ρ.one, zero_add, one_mul]
  · intro mask entry m hm a
    exact sum_end_world ρ L (F₀ L.T.par) st t.p.target mu t.p.eps rs sentY beta n1 v num
      (fun a => by rw [a7]; exact hnum a) _ G t.sEnd a16 mask entry m hm a

/-! ## Plain rounds of degree 2 -/

theorem plain2_fits (L : SumL K) (st : L.St) (hn : ∀ i, L.M.n i = 2)
    (hw : ∀ i, L.S.w st i = none) :
    Fits ρ (List.replicate L.S.k (Weight.plain 3) ++ [Weight.atZero (L.M.DY + 1)]) L.T.par.fmt
      (L.T.par.dat st) (pick (L.T.par.vars st)) := by
  have h := sum_fits_plain ρ L st hw (fun i => by rw [hn i]; norm_num)
  have e : plainWs (List.ofFn L.M.n) L.M.DY =
      List.replicate L.S.k (Weight.plain 3) ++ [Weight.atZero (L.M.DY + 1)] := by
    unfold plainWs
    rw [show L.M.n = fun _ => 2 from funext hn, List.ofFn_const, List.map_replicate]
  rw [e] at h
  exact h

theorem plain2_tie (L : SumL K) (st : L.St) (hn : ∀ i, L.M.n i = 2)
    (hw : ∀ i, L.S.w st i = none) {c c1 c' : Ctx} {riders : List E} {mu eps : E}
    {rs : List (List E × E)} {sentY : List E} {beta : E} {v : List E} {p : OnBytes.Model.Psc}
    {C : Aff} {τ : E} {first : ℕ}
    (a : Parts c c1 c' riders mu eps (List.replicate L.S.k (Weight.plain 3)) rs L.M.DY sentY beta
      v)
    (e : Ended p C τ mu eps first (List.replicate L.S.k (Weight.plain 3)) rs L.M.DY sentY beta)
    (hlen : rs.length = L.S.k)
    (hsz : ∀ x ∈ (List.replicate L.S.k (Weight.plain 3)).zip rs, x.2.1.length + 1 = x.1.d)
    (hY : sentY.length = L.M.DY) (hc : NzCtx ρ c) (vals : L.S.A → K) :
    NzCtx ρ c' ∧ ∃ hβ : ρ.val beta ≠ 0,
      SumSaid ρ L (fun st => pick (L.T.par.vars st)) st p
        (List.replicate L.S.k (Weight.plain 3) ++ [Weight.atZero (L.M.DY + 1)]) mu rs sentY beta
        hβ vals :=
  sum_tie ρ L (fun st => pick (L.T.par.vars st)) st a e (by rw [hlen]; simp) hsz
    (by
      rw [List.map_replicate, show L.M.n = fun _ => 2 from funext hn, List.ofFn_const]
      rfl) hY (plain2_fits ρ L st hn hw) hc vals

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_tie
#print axioms OnBytes.Tie.Pv.Lay.Eng.tok_tie
#print axioms OnBytes.Tie.Pv.Lay.Eng.plain2_tie
