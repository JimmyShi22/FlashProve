-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Said.lean: the law's main clause, by the library's own theorems. Where
`mergeHear` (Johnson/Desc/First/Fork/MergeKind.lean) says yes, the sumcheck's record that it leaves
is
the library's `Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean) at what the tape holds; so the library's
sum_said, SumSaid.row, sum_end and merge_fits (OnBytes/Tie/Pv/Lay/) apply to it. General in the
number of claims. Two theorems with their proofs, the second for every reading
(OnBytes.Model.Reading) into a finite field.

Main names:
  `hear_ended`: the record is `Ended`; the tape's shape; the target; the rows `recs`.
  `hear_tie`: for every typed record (Cb.Pv.Lay.MergeL) with as many column bits as the layout and
    every state of it, where the last challenge reads other than 0: `SumSaid` holds of the typed
    output; the record's row form at the sent end value is worth 0 exactly if the typed row claim
    holds, under (D1) and (D2); the typed claim on the end value holds exactly if the summand's map
    at the point is the sent value, read, less the mask entry times the reading of that challenge.

It follows OnBytes/Tie/Pv/Lay/MergeTie.lean (merge_tie), which says the same of the routine
wsForkMerge; merge_tie itself is not used.

The library's lemmas that are spent, each a statement on plain records and pure functions:
`Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), walk_length (Run/PscPure.lean), zipT_eq
(OnBytes/Chain/Lists.lean), sum_said and SumSaid.row (OnBytes/Tie/Pv/Lay/SumSaid.lean), sumOut and
sum_end (SumTie.lean), merge_fits (MergeTie.lean), MergeL.pick_ok (Cb/Pv/Lay/Merge.lean),
Aff.value_empty (OnBytes/Model/HideLaws.lean). A walk over constants, proofs among them, from every
theorem of this folder has reached no routine that runs in a context (Blk, Ctx, Chan, SubM, LinkM).

Limits: one direction: from the text's yes. That the last challenge reads other than 0, (D1) (the
slots from the sumcheck's first one on hold the hiding polynomial's coefficients) and (D2) (the
incoming masks' form is the target less the start's worth) are premises. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Hear
import OnBytes.Tie.Pv.Lay.MergeTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop Cb Cb.Pv.Lay
open OnBytes (E addE mulE zeroE)
open OnBytes.K.Kc (Tape)
open OnBytes.Psc (Weight)
open OnBytes.Model (Reading World Fork WsLay WsClaim WsForkOut wsForkStart wsRowPart wsEpsT)
open OnBytes.Model.Road (Ended)
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sum_said sumOut sum_end merge_fits)
open Johnson.Desc.First.ForkMerge (mergeHear)

/-- **Where `mergeHear` says yes, the sumcheck's record that it leaves is the library's `Ended`**
(OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), at what the tape holds. -/
theorem hear_ended {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape}
    {wo : WsForkOut}
    (h : mergeHear lay cl sv F t = .ok (wo, F', t')) :
    ∃ (x mu c beta v T : E) (r1 rY rV : Nat) (qs : List (Nat × List E × E)),
      qs.length = lay.lk ∧ (∀ q ∈ qs, q.2.1.length = 2) ∧
      t = ⟨some OnBytes.Model.RoundName.batSigma.name, 0, sv.size, [], [x]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [mu], [wo.p.eps]⟩ ::
          (qs.map (rd OnBytes.Model.RoundName.pscRound.name 0) ++
            ⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
            ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: t') ∧
      F.publicPart (wsForkStart sv (OnBytes.Model.powers x sv.size)) = some T ∧
      Ended wo.p (wsForkStart sv (OnBytes.Model.powers x sv.size)) T mu wo.p.eps F.next
        (List.replicate lay.lk (Weight.plain 3)) (qs.map fun q => (q.2.1, q.2.2)) 1 [c] beta ∧
      wo.rm.toList = qs.map (·.2.2) ∧ wo.beta = beta ∧ wo.sFv = F.next + 1 + 2 * lay.lk + 1 ∧
      ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork).hideRun wo.sFv #[v] beta = some F' ∧
      F'.shown wo.sFv = some wo.fvp ∧
      wo.recs = (cl.zip (OnBytes.Model.powers x sv.size)).toList.map (fun y =>
        wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))) := by
  obtain ⟨x, mu, eps, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, heps, htar, hclaim, hrm, hbeta,
      hr, hsFv, hhide,
    hshown, hrecs, hvars, hfirst, hstart, hstarted, hrowMade, hended⟩ := mergeHear_inv h
  have hr' : wo.p.r.toList = (qs.map fun q => (q.2.1, q.2.2)).map (·.2) ++ [beta] := by
    rw [hr]; simp [List.map_map, Function.comp_def]
  have hw : wo.p.walk = OnBytes.Psc.hidingWalk ((List.replicate lay.lk (Weight.plain 3) ++
      [Weight.atZero (1 + 1)]).zip
      ((qs.map fun q => (q.2.1, q.2.2)).map (·.2) ++ [beta])) := by
    unfold OnBytes.Model.Psc.walk
    rw [OnBytes.zipT_eq, hvars, hr']
  refine ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, by rw [heps]; exact et, hT, ?_, hrm, hbeta,
      hsFv, hhide, hshown, hrecs⟩
  refine ⟨by rw [hclaim, heps], hw, ?_, hvars, hr', hstart, htar, rfl, hfirst, hstarted, hended,
      hrowMade⟩
  rw [hw]
  refine OnBytes.Model.Road.walk_length _ _ (by simp) (by simp [hn]) ?_
  intro w hwm
  rcases List.mem_append.1 hwm with hwm | hwm
  · rw [(List.mem_replicate.1 hwm).2]
    show 1 ≤ 3
    omega
  · rw [List.mem_singleton.1 hwm]
    show 1 ≤ 2
    omega

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **The main clause**: see the head. -/
theorem hear_tie {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape} {wo
    : WsForkOut}
    (L : MergeL K) (hk : L.k = lay.lk) (h : mergeHear lay cl sv F t = .ok (wo, F', t')) (st : L.St)
        :
    ∃ (x mu c beta v T : E) (r1 rY rV : Nat) (qs : List (Nat × List E × E)),
      t = ⟨some OnBytes.Model.RoundName.batSigma.name, 0, sv.size, [], [x]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [mu], [wo.p.eps]⟩ ::
          (qs.map (rd OnBytes.Model.RoundName.pscRound.name 0) ++
            ⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
            ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: t') ∧
      F.publicPart (wsForkStart sv (OnBytes.Model.powers x sv.size)) = some T ∧ wo.p.target = T ∧
      wo.rm.toList = qs.map (·.2.2) ∧ wo.beta = beta ∧
      ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork).hideRun wo.sFv #[v] beta = some F' ∧
      F'.shown wo.sFv = some wo.fvp ∧
      ∀ hβ : ρ.val beta ≠ 0,
        SumSaid ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st wo.p
          (List.replicate L.k (Weight.plain 3) ++ [Weight.atZero (1 + 1)]) mu (qs.map fun q =>
              (q.2.1, q.2.2)) [c] beta hβ
          (fun _ => ρ.val v) ∧
        (∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
          L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) wo.p.first →
          L.toSum.T.par.inc st m = ρ.val wo.p.target - wo.p.start.value ρ W →
          ((wo.p.rowForm v {}).value ρ W = 0 ↔
            L.toSum.T.par.UHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
              wo.p.target mu wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ fun _ => ρ.val v)
                  m)) ∧
        ∀ m : L.J → K,
          (L.toSum.T.par.EHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
              wo.p.target mu wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ fun _ => ρ.val v)
                  m () ↔
            L.f st m (L.toSum.Q.outPt L.toSum.M
                (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st wo.p.target mu
                  wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ fun _ => ρ.val v)) =
              ρ.val v - m L.cAt * ρ.val beta) := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, a4, hrm, hbeta, _, hhide, hshown, _⟩
      := hear_ended h
  refine ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, et, hT, a4.target, hrm, hbeta, hhide, hshown, ?_⟩
  intro hβ
  rw [← hk] at a4
  have hl : (qs.map fun q => (q.2.1, q.2.2)).map (·.1.length) = List.ofFn L.toSum.M.n := by
    have h2 : (qs.map fun q => (q.2.1, q.2.2)).map (·.1.length) = List.replicate L.k 2 := by
      rw [List.map_map, List.eq_replicate_iff]
      refine ⟨by simp [hn, hk], ?_⟩
      intro b hb
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hb
      exact hq q hqm
    rw [h2]
    exact (List.ofFn_const _ _).symm
  have s := sum_said ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st a4 hβ
    (fun _ => ρ.val v) (merge_fits ρ L st) hl rfl
  refine ⟨s, ?_, ?_⟩
  · intro Ex y W m D1 D2
    refine s.row ρ L.pick_ok Ex y W _ {} m D1 D2
      (by
        rw [OnBytes.Model.Aff.value_empty]
        exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) ?_
    show ([(1 : K) * [ρ.val v].prod]).sum = _
    simp
  · intro m
    exact sum_end ρ L.toSum _ st wo.p.target mu wo.p.eps _ [c] beta hβ (fun _ => ρ.val v) m ()

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.hear_ended
#print axioms VerifiableInference.Desc.First.MergeLaw.hear_tie
