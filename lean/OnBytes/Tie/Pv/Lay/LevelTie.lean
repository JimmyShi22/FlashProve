-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/LevelTie.lean: the port's routine for one layer of a product tree, where it
succeeds, has heard a transcript of the typed product layer, and its record is the block's output on
that transcript, read.

levelIn (OnBytes/Model/Psc.lean) receives the messages of a layer's masked sumcheck, makes its row,
and draws the point on the line between the two end values. The typed side is the product layer
`ProdL` (Cb/Pv/Lay/Prod.lean), in the chain as `ProdL.toSum` (Cb/Pv/Lay/OwnParts.lean) under the
pick `F₀`, with a stage of its own for the draw.

Main names:
  `lvNum`, `lvVals`: the left end value has the number 0 and the name false, the right one 1 and
    true; the two end values, read, under their names.
  `level_fits`: the port's weights of a layer fit the typed variables, if the typed equality point
    at the coordinate that round j binds is the reading of the port's coordinate for the j-th member
    of the order.
  `level_tie`: if levelIn succeeds from a state whose arrays on slots have their length and from a
    context with `NzCtx`, then for all parameters L with as many variables, and every state st with
    that premise on the point: what the seam says (`levelIn_seam`,
    OnBytes/Tie/Pv/Psc/Run/PscLayer.lean: the rounds heard, the draw of the line's point, the
    record, the row, the slots, the two fillings of the state); the context that is left has
    `NzCtx`; the reading of beta is not 0; `SumSaid` holds of the typed output; the typed summand at
    the output's point and values is the reading of the port's; the row is worth 0 exactly if the
    typed row claim holds, for every world and all entries with (D1) and (D2); and the typed claim
    on an end value holds exactly if the map at the point is what the end value's slot is worth in
    the world of the state behind the messages, for entries whose places are the slots' mask
    entries.

Limits: one direction: from the routine's success. `NzCtx` at the start, the premise on the point,
(D1), (D2) and the places of the mask entries are premises. What the challenges' order says of the
record's r (`placed`) is left as the seam gives it.
-/
import OnBytes.Tie.Pv.Lay.SumSaid
import OnBytes.Tie.Pv.Lay.SumFits
import OnBytes.Tie.Pv.Psc.Run.PscLayer
import OnBytes.Tie.Pv.Psc.Run.NzRounds
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att
open OnBytes.Psc (Weight)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- the number of an end value -/
def lvNum (b : Bool) : ℕ := if b then 1 else 0

/-- the two end values, read, under their names -/
def lvVals (vL vR : E) : Bool → K := fun b => ρ.val ([vL, vR].getD (lvNum b) zeroE)

theorem level_fits (L : ProdL K) (st : L.St) (rho : Array E) (order : List Nat)
    (ho : order.length = L.k)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE)) :
    Fits ρ (levelWeights L.k rho order ++ [Weight.atZero (2 + 1)]) L.toSum.T.par.fmt
      (L.toSum.T.par.dat st) (F₀ L.toSum.T.par st) := by
  have e : levelWeights L.k rho order = List.ofFn fun i : Fin L.k =>
      Weight.equality (rho.getD (L.k - 1 - order.getD i.1 0) zeroE) (2 + 1) :=
    map_ofFn _ 0 L.k order ho
  rw [e]
  exact sum_fits_eq ρ L.toSum st (fun i => rho.getD (L.k - 1 - order.getD i.1 0) zeroE)
    fun i => congrArg some (hp i)

theorem level_tie (L : ProdL K) (rho : Array E) (C : Aff) (order : List Nat) (F G : Fork)
    (c c' : Ctx) (o : Level) (h : levelIn L.k rho C order F c = .ok ((o, G), c')) (hs : Sized F)
    (hc : NzCtx ρ c) (st : L.St)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE)) :
    ∃ (τ mu eps : E) (rs : List (List E × E)) (sentY : List E) (beta vL vR : E) (cL : Ctx)
      (p : OnBytes.Model.Psc) (F1 : Fork),
      Parts c c cL [] mu eps (levelWeights L.k rho order) rs 2 sentY beta [vL, vR] ∧
      (Blk.closeOne "LINE" .elems 0).Yields cL o.tau c' ∧
      F.publicPart C = some τ ∧
      Ended p C τ mu eps F.next (levelWeights L.k rho order) rs 2 sentY beta ∧
      o.r = placed L.k (Array.replicate L.k zeroE) order (rs.map (·.2)) ∧
      o.row = p.rowForm (mulE vL vR) {} ∧
      o.sL = F.next + (1 + 2 * L.k + 2) ∧ o.sR = o.sL + 1 ∧
      Filled (taken F (1 + 2 * L.k + 2 + 2)) F1 o.sL [vL, vR] beta ∧
      Filled F1 G F.next (List.replicate p.walk.1.length zeroE) (subE zeroE oneE) ∧
      NzCtx ρ c' ∧ ∃ hβ : ρ.val beta ≠ 0,
        SumSaid ρ L.toSum (F₀ L.toSum.T.par) st p
          (levelWeights L.k rho order ++ [Weight.atZero (2 + 1)]) mu rs sentY beta hβ
          (lvVals ρ vL vR) ∧
        L.toSum.S.pol st
            (L.toSum.Q.outPt L.toSum.M (sumOut ρ L.toSum (F₀ L.toSum.T.par) st p.target mu p.eps
              rs sentY beta hβ (lvVals ρ vL vR))) (lvVals ρ vL vR) = ρ.val (mulE vL vR) ∧
        (∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
          L.toSum.T.par.W st m =
            OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) p.first →
          L.toSum.T.par.inc st m = ρ.val p.target - p.start.value ρ W →
          (o.row.value ρ W = 0 ↔
            L.toSum.T.par.UHolds (sumOut ρ L.toSum (F₀ L.toSum.T.par) st p.target mu p.eps rs
              sentY beta hβ (lvVals ρ vL vR)) m)) ∧
        ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : L.J → K),
          (∀ b, m (L.cAt b) = mask (o.sL + lvNum b)) → ∀ b : Bool,
          (L.toSum.T.par.EHolds (sumOut ρ L.toSum (F₀ L.toSum.T.par) st p.target mu p.eps rs
              sentY beta hβ (lvVals ρ vL vR)) m b ↔
            L.toSum.S.F st m b
                (L.toSum.Q.outPt L.toSum.M (sumOut ρ L.toSum (F₀ L.toSum.T.par) st p.target mu
                  p.eps rs sentY beta hβ (lvVals ρ vL vR))) =
              (F1.worldOf ρ mask entry).slot (o.sL + lvNum b)) := by
  obtain ⟨τ, mu, eps, rs, sentY, beta, vL, vR, cL, p, F1, a1, a2, a3, _, a5, a6, a7, _, a9, a10,
    a11, a12, a13, a14, a15, a16⟩ := levelIn_seam L.k rho C order F G c c' o h hs
  obtain ⟨n1, n2⟩ := parts_nz ρ a1 hc
  have n3 := keeps_closeOne ρ _ _ _ _ _ _ n2 a2
  have hl : rs.map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [sizes_of _ rs a6 a7]
    show (order.map fun v => Weight.equality (rho.getD (L.k - 1 - v) zeroE) 3).map _ = _
    rw [List.map_map, map_ofFn _ 0 L.k order a3]
    rfl
  have s := sum_said ρ L.toSum (F₀ L.toSum.T.par) st a9 n1 (lvVals ρ vL vR)
    (level_fits ρ L st rho order a3 hp) hl a10
  have hD4 : L.toSum.S.pol st
      (L.toSum.Q.outPt L.toSum.M (sumOut ρ L.toSum (F₀ L.toSum.T.par) st p.target mu p.eps
        rs sentY beta n1 (lvVals ρ vL vR))) (lvVals ρ vL vR) = ρ.val (mulE vL vR) := by
    rw [ρ.mul]
    show ([(1 : K) * [lvVals ρ vL vR false, lvVals ρ vL vR true].prod]).sum = _
    simp [lvVals, lvNum]
  refine ⟨τ, mu, eps, rs, sentY, beta, vL, vR, cL, p, F1, a1, a2, a5, a9, a11, a12, a13, a14, a15,
    a16, n3, n1, s, hD4, ?_, ?_⟩
  · intro Ex y W m D1 D2
    rw [a12]
    exact s.row ρ (F₀_ok _ (L.eq0 : Eq0 L.toSum.T.par)) Ex y W _ {} m D1 D2
      (by
        rw [Aff.value_empty]
        exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) hD4
  · intro mask entry m hm b
    exact sum_end_world ρ L.toSum (F₀ L.toSum.T.par) st p.target mu p.eps rs sentY beta n1
      [vL, vR] lvNum (fun b => by cases b <;> simp [lvNum]) _ F1 o.sL a15 mask entry m hm b

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.level_fits
#print axioms OnBytes.Tie.Pv.Lay.Eng.level_tie
