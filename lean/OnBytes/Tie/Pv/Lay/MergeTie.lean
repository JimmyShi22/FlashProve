-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/MergeTie.lean: the port's routines for the merge of a sub-proof's weight claims,
where they succeed, have heard a transcript of the typed merge, and their record is the block's
output on that transcript, read.

wsForkMerge (OnBytes/Model/Merge.lean) draws the element that batches the claims, receives the
messages of a masked sumcheck over the column bits and reads off what was shown for its one end
value. pscRow at that value makes the merge's row (wsForkLin). The typed side is `MergeL`
(Cb/Pv/Lay/Merge.lean), in the chain as `MergeL.toSum` (Cb/Pv/Lay/OwnParts.lean) under `pick`.

Main names:
  `wsForkRounds_ok`: the loop of the plain rounds of degree 2, as the block's listener hears it.
  `merge_seam`: where wsForkMerge succeeds: the draw of the batching element; the rounds heard
    (`Parts`); the record behind the end value's round (`Ended`); the merge's point, the shown value
    and its slot (that the record's field beta is the challenge of the further variable is not shown
    here); how the end value was put under its slot (`Filled`).
  `merge_tie`: from a context with `NzCtx`, for all parameters L with as many variables and every
    state: what the seam says; the context that is left has `NzCtx`; the reading of beta is not 0;
    `SumSaid` holds of the typed output; the record's row form at the shown value is worth 0 exactly
    if the typed row claim holds, under (D1) and (D2); the typed claim on the end value holds
    exactly if the summand's map at the point is the shown value, read, less the mask entry times
    the reading of beta.

Limits: one direction: from the routine's success. `NzCtx` at the start, (D1) and (D2) are premises.
By the port's text the mask of the merge's end value is an entry of the request's index-mask message
and not of the sub-proof's own mask row: so the claim on the end value is stated with the mask entry
m (cAt) itself, and nothing is said of the world's worth of the slot sFv. What wsForkEnd forms of
each claim behind the merge (recs) is not treated.
-/
import OnBytes.Model.Merge
import OnBytes.Tie.Pv.Lay.SumSaid
import OnBytes.Tie.Pv.Lay.SumFits
import OnBytes.Tie.Pv.Att.NzSub
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att
open OnBytes.Psc (Weight hearMany)

theorem weight_sum2 (z : E) (d : Nat) : RoundForm.weight .sum2 z d = some (Weight.plain 3) := rfl

theorem wsForkRounds_ok : ∀ (n : Nat) (a : Array E) (p : OnBytes.Model.Psc)
    (x : Array E × OnBytes.Model.Psc) (F G : Fork) (c c' : Ctx),
    wsForkRounds n a p F c = .ok ((x, G), c') →
    ∃ rs : List (List E × E),
      (hearMany (List.replicate n 2)).Yields c rs c' ∧
      Stepped p x.2 (List.replicate n (Weight.plain 3)) rs ∧
      x.1.toList = a.toList ++ rs.map (·.2) ∧ G = taken F (2 * n)
  | 0, a, p, x, F, G, c, c', h => by
    simp only [wsForkRounds] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e1, e2, e3]
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl⟩
  | n + 1, a, p, x, F, G, c, c', h => by
    simp only [wsForkRounds] at h
    obtain ⟨⟨r, q⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨w, sent, b1, _, y1, s1, g1⟩ := roundIn_stepped _ _ _ _ _ _ _ _ _ _ h1
    rw [weight_sum2] at b1
    have hw := Option.some.inj b1
    rw [← hw] at y1 s1 g1
    obtain ⟨rs, y2, s2, r2, g2⟩ := wsForkRounds_ok n _ _ _ _ _ _ _ k1
    refine ⟨(sent, r) :: rs, ?_, ?_, ?_, ?_⟩
    · exact hearMany_append [2] _ _ _ _ _ _ y1 y2
    · exact s1.trans s2
    · rw [r2]; simp
    · rw [g2, g1, taken_taken]
      show taken F (2 + 2 * n) = _
      rw [show 2 + 2 * n = 2 * (n + 1) by omega]

theorem merge_seam (lk : Nat) (sv : Array Nat) (o : WsMerged) (rho : Array E) (F G : Fork)
    (c c' : Ctx) (h : wsForkMerge lk sv F c = .ok (((o, rho), G), c')) (hz : Sized F) :
    ∃ (c1 : Ctx) (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta fv : E),
      SubM.batch sv.size F c = .ok ((rho, F), c1) ∧
      F.publicPart (wsForkStart sv rho) = some τ ∧
      Parts c1 c1 c' [] mu o.p.eps (List.replicate lk (Weight.plain 3)) rs 1 sentY beta [fv] ∧
      Ended o.p (wsForkStart sv rho) τ mu o.p.eps F.next (List.replicate lk (Weight.plain 3)) rs 1
        sentY beta ∧
      o.rm.toList = rs.map (·.2) ∧ rs.map (·.1.length) = List.replicate lk 2 ∧
      sentY.length = 1 ∧ o.fvp = fv ∧ o.sFv = F.next + (1 + 2 * lk) + 1 ∧
      Filled (taken F (1 + 2 * lk + (1 + 1))) G o.sFv [fv] beta := by
  unfold wsForkMerge at h
  obtain ⟨rho', F1, c1, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
  have hF1 : F1 = F := ((liftY_ok (trBatch sv.size) F F1 c c1 rho').1 h0).2
  rw [hF1] at h0 k0
  obtain ⟨p0, F2, c2, hb, k1⟩ := (bind_ok _ _ _ _ _).1 k0
  obtain ⟨⟨rm, p1⟩, F3, c3, hr, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨⟨e, p2⟩, G', c4, he, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨fvp, G'', c5, hsn, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k4
  obtain ⟨q1, q2, q3⟩ := (ask_ok _ _ _ _ _ _).1 hsn
  obtain ⟨_, _, _, _, _, hF2⟩ := pscBegin_ok _ F F2 c1 c2 p0 hb
  obtain ⟨rs, y, s, r, g⟩ := wsForkRounds_ok lk _ p0 (rm, p1) F2 F3 c2 c3 hr
  have hF3 : F3 = taken F (1 + 2 * lk) := by rw [g, hF2, taken_taken]
  have hm : (hearMany ((List.replicate lk (Weight.plain 3)).map fun w => w.d - 1)).Yields c2 rs
      c3 := by
    rw [List.map_replicate]
    exact y
  obtain ⟨τ, mu, sentY, beta, v, a1, _, a3, a4, a5, a6, a7, _, a9, a10, a11⟩ :=
    seam [] _ p0 p1 p2 _ rs 1 1 e F F2 F3 G' c1 c1 c2 c3 c4 (recvEs_zero c1) hb hm s he
      (by rw [hF3]; exact sized_taken F _ hz)
  obtain ⟨fv, rfl⟩ : ∃ fv, v = [fv] := by
    cases v with
    | nil => simp at a7
    | cons a l =>
      cases l with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at a7
  have ho : o = { fvp := fvp, beta := p2.r.back?.getD zeroE, rm := rm, p := p2, sFv := e } :=
    congrArg Prod.fst e1
  have hrho : rho = rho' := congrArg Prod.snd e1
  have hε : p2.eps = p0.eps := a5.eps
  have hsh := a11.shown 0 (by simp)
  rw [Nat.add_zero] at hsh
  rw [hrho]
  refine ⟨c1, τ, mu, rs, sentY, beta, fv, h0, a1, ?_, ?_, ?_, ?_, a6, ?_, ?_, ?_⟩
  · rw [ho, e3, q3]
    show Parts c1 c1 c4 [] mu p2.eps _ rs 1 sentY beta [fv]
    rw [hε]
    exact a3
  · rw [ho]
    show Ended p2 _ τ mu p2.eps F.next _ rs 1 sentY beta
    rw [hε]
    exact a5
  · rw [ho]
    show rm.toList = _
    have r' : rm.toList = (Array.emptyWithCapacity lk : Array E).toList ++ rs.map (·.2) := r
    rw [r']
    simp
  · refine sizes_map (List.replicate lk 2) rs (by rw [s.len]; simp) ?_
    rw [List.map_replicate]
    exact s.sizes
  · rw [ho]
    show fvp = fv
    have := q1.symm.trans hsh
    exact Option.some.inj this
  · rw [ho]
    show e = _
    rw [a10, hF3]
    rfl
  · rw [ho, e2, q2]
    show Filled _ G' e [fv] beta
    rw [hF3, taken_taken] at a11
    exact a11

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem merge_fits (L : MergeL K) (st : L.St) :
    Fits ρ (List.replicate L.k (Weight.plain 3) ++ [Weight.atZero (1 + 1)]) L.toSum.T.par.fmt
      (L.toSum.T.par.dat st) (pick (L.toSum.T.par.vars st)) := by
  have h := sum_fits_plain ρ L.toSum st (fun _ => rfl) (fun _ => by norm_num)
  have e : plainWs (List.ofFn L.toSum.M.n) L.toSum.M.DY =
      List.replicate L.k (Weight.plain 3) ++ [Weight.atZero (1 + 1)] := by
    show (List.ofFn fun _ : Fin L.k => 2).map _ ++ _ = _
    rw [List.ofFn_const, List.map_replicate]
  rw [e] at h
  exact h

theorem merge_tie (L : MergeL K) (sv : Array Nat) (o : WsMerged) (rho : Array E) (F G : Fork)
    (c c' : Ctx) (h : wsForkMerge L.k sv F c = .ok (((o, rho), G), c')) (hz : Sized F)
    (hc : NzCtx ρ c) (st : L.St) :
    ∃ (c1 : Ctx) (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta fv : E),
      SubM.batch sv.size F c = .ok ((rho, F), c1) ∧
      F.publicPart (wsForkStart sv rho) = some τ ∧
      Parts c1 c1 c' [] mu o.p.eps (List.replicate L.k (Weight.plain 3)) rs 1 sentY beta [fv] ∧
      Ended o.p (wsForkStart sv rho) τ mu o.p.eps F.next (List.replicate L.k (Weight.plain 3)) rs
        1 sentY beta ∧
      o.rm.toList = rs.map (·.2) ∧ o.fvp = fv ∧ o.sFv = F.next + (1 + 2 * L.k) + 1 ∧
      Filled (taken F (1 + 2 * L.k + (1 + 1))) G o.sFv [fv] beta ∧
      NzCtx ρ c' ∧ ∃ hβ : ρ.val beta ≠ 0,
        SumSaid ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st o.p
          (List.replicate L.k (Weight.plain 3) ++ [Weight.atZero (1 + 1)]) mu rs sentY beta hβ
          (fun _ => ρ.val fv) ∧
        (∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
          L.toSum.T.par.W st m =
            OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) o.p.first →
          L.toSum.T.par.inc st m = ρ.val o.p.target - o.p.start.value ρ W →
          ((o.p.rowForm o.fvp {}).value ρ W = 0 ↔
            L.toSum.T.par.UHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
              o.p.target mu o.p.eps rs sentY beta hβ fun _ => ρ.val fv) m)) ∧
        ∀ m : L.J → K,
          (L.toSum.T.par.EHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
              o.p.target mu o.p.eps rs sentY beta hβ fun _ => ρ.val fv) m () ↔
            L.f st m (L.toSum.Q.outPt L.toSum.M
                (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st o.p.target mu
                  o.p.eps rs sentY beta hβ fun _ => ρ.val fv)) =
              ρ.val fv - m L.cAt * ρ.val beta) := by
  obtain ⟨c1, τ, mu, rs, sentY, beta, fv, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    merge_seam L.k sv o rho F G c c' h hz
  obtain ⟨n1, n2⟩ := parts_nz ρ a3 (keepsS_batch ρ sv.size F c rho F c1 hc a1)
  have hl : rs.map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [a6]
    exact (List.ofFn_const _ _).symm
  have s := sum_said ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st a4 n1
    (fun _ => ρ.val fv) (merge_fits ρ L st) hl a7
  refine ⟨c1, τ, mu, rs, sentY, beta, fv, a1, a2, a3, a4, a5, a8, a9, a10, n2, n1, s, ?_, ?_⟩
  · intro Ex y W m D1 D2
    refine s.row ρ L.pick_ok Ex y W _ {} m D1 D2
      (by
        rw [Aff.value_empty]
        exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) ?_
    rw [a8]
    show ([(1 : K) * [ρ.val fv].prod]).sum = _
    simp
  · intro m
    exact sum_end ρ L.toSum _ st o.p.target mu o.p.eps rs sentY beta n1 (fun _ => ρ.val fv) m ()

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.merge_seam
#print axioms OnBytes.Tie.Pv.Lay.Eng.merge_tie
