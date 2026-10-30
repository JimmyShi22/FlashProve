-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsPre.lean: CONDITIONAL: WHO PAYS THE ONE PREMISE ON VALUES OF THE FOUR
RUNS' LAWS (`preK5`, Johnson/Desc/K5/Honest/Law/RunsLaw.lean) IN FRONT OF A RUN: from the lookup's
own cut of the key points, and along the states of one attention link. Statements with their proofs:
each is a few calls of the library's lemmas.

Main names:
  `valsT_of_K3Pts`   **the two tests on values say yes wherever the key points follow the lookup's
    own rule** (K3Pts, Johnson/Desc/First/Att/K05LookAll.lean): by the library's mergedPlanes_at |
    mergedTokens_at (First/Att/K05MergedAt.lean)
  `valsTS_of_K3Pts`   the same at a state
  `in_of_vals`   from the premise, the one Bool of the tables and the tables' array to the runs'
    input
  `pre_forth`   **the premise rides**: where the runs' input is made at a state of an attention
    link, the premise holds, and the same input is made, at every later state to which the
    library's two relations lead (CarK5: what the link's own rounds handed on stands and the ledger
    only grows, First/Att/Claims/WalkK5.lean; Kept5: what the lookup returned stays and every array
    keeps its shape, Claims/WalkShape.lean): by the library's inAt_forth (Claims/InAtOne.lean)

`valsT_of_K3Pts` IS CONDITIONAL on: the library's facts on the plan (UnitsAll, Norm, 1 ≤ lnT, lmS is
at most a plane family's bits); K3Pts at what the lookup returned; the key points' lengths; lmS and
lt + ldh are at most the length of zx; the return of the function of the points. `pre_forth` on: the
input's return at the first state; a sized ledger there; the two relations.
Limits. No challenge's value is asked after: zx and zy are free letters. WHO GIVES K3Pts AT A STATE,
AND THE TWO RELATIONS MEMBER BY MEMBER, IS NOT SAID HERE. No theorem here says that any premise
holds anywhere. THE NEAREST TEXTS OF THE LIBRARY: Johnson/Desc/K1/Law/ArmAttIn.lean (inOf_of_reader,
hin_at_reads) gives the input's return at the state in front of the reads' place in the coin of the
library's public promises; Claims/InAtOne.lean's four speak of ledgers, `pre_forth` of states along
the two relations; Claims/LeftLater.lean has ptsFrom_later (what the function of the points returns
at a ledger it returns at every later one) and inOf_mono, `pre_forth`'s cousin at another seat
(seatCH) and under other premises (the two fields equal; what is shown stays shown; the widths
stay). NOBODY CALLS `in_of_vals` OR `pre_forth`: they are for a caller that walks the states of a
link by the two relations itself, if one comes.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsLaw
import Johnson.Desc.First.Att.K05MergedAt
import Johnson.Desc.First.Att.Claims.InAtOne
import Johnson.Desc.First.Att.Claims.WalkShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard UnitG UnitsAll K3Pts)
open OnBytes.Road.L5 (dimOf callsOf)

/-! ## 1 From the lookup's own cut -/

section
variable (A : Attention.Plan) {r1 r2 u1 u2 wl ix wh : UnitG}

/-- **THE TWO TESTS ON VALUES SAY YES WHEREVER THE KEY POINTS FOLLOW THE LOOKUP's OWN RULE.**
CONDITIONAL: see the head. zx, zy and the key points are free letters under K3Pts. -/
theorem valsT_of_K3Pts (U : UnitsAll A.S A.fs r1 r2 u1 u2 wl ix wh)
    (N : OnBytes.Road.L5.Norm A.S) (h1 : 1 ≤ A.S.lnT)
    (hl : ∀ f : Inst.Model.AttSeg.Fam, Cb.Pv.Att.End.IsPlane f → A.S.cf.lmS ≤ f.l (dimOf A.S))
    {gl : Forest.Heard} {z : ℕ → Cb.Gl.E} (H3 : K3Pts A.fs gl.zx gl.zy gl.zk z)
    (Kz : ∀ q : Fin 4, (gl.zk.getD q.1 #[]).size = (callsOf A.fs).a q)
    (hx : A.S.cf.lmS ≤ gl.zx.size) (hx' : A.S.cf.lt + A.S.cf.ldh ≤ gl.zx.size) {h : Heard}
    {F : Fork} {p : P.Pts} (hp : P.ptsFrom (P.parCOf A).geo gl.zk h F = some p) :
    valsT A gl h F = true := by
  obtain ⟨L, _, hP⟩ := Option.bind_eq_some_iff.1 hp
  unfold valsT
  rw [hp]
  have m1 := P.mergedPlanes_at U H3 Kz hl hx hP
  have m2 := P.mergedTokens_at U N h1 H3 Kz hx' hP
  exact Bool.and_eq_true_iff.2 ⟨m1, m2⟩

/-- The same at a state. -/
theorem valsTS_of_K3Pts (U : UnitsAll A.S A.fs r1 r2 u1 u2 wl ix wh)
    (N : OnBytes.Road.L5.Norm A.S) (h1 : 1 ≤ A.S.lnT)
    (hl : ∀ f : Inst.Model.AttSeg.Fam, Cb.Pv.Att.End.IsPlane f → A.S.cf.lmS ≤ f.l (dimOf A.S))
    {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard} (hh : s.here = .att a)
    (h5 : a.heard5 = some h) (hg : a.g = some gl) {z : ℕ → Cb.Gl.E}
    (H3 : K3Pts A.fs gl.zx gl.zy gl.zk z)
    (Kz : ∀ q : Fin 4, (gl.zk.getD q.1 #[]).size = (callsOf A.fs).a q)
    (hx : A.S.cf.lmS ≤ gl.zx.size) (hx' : A.S.cf.lt + A.S.cf.ldh ≤ gl.zx.size) {p : P.Pts}
    (hp : P.ptsFrom (P.parCOf A).geo gl.zk h a.F = some p) (n : Nat) : preK5 A n s := by
  unfold preK5
  rw [vals_at A hh h5 hg]
  exact valsT_of_K3Pts A U N h1 hl H3 Kz hx hx' hp

end

/-! ## 2 Along the states of one link -/

/-- **From the premise to the runs' input**: where the one Bool of the tables and the two tests on
values say yes, and the tables' array is in the ledger, the runs' input is made. So the first part's
end meets the next statement's premise hx. -/
theorem in_of_vals (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork} {n : Nat}
    (hG : tabsG A (VerifiableInference.Desc.First.Shape.heard5Sh h)
      (VerifiableInference.Desc.First.Shape.heardAll gl)
      (VerifiableInference.Desc.First.Shape.ledSh F) = true) (hV : valsT A gl h F = true)
    (hK : (F.trees[(P.parCOf A).iU3]?).map (·.K) = some n) :
    ∃ x, K5Law.inAt (P.parCOf A) gl h F = some x := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (tabs_returns A hG hV)
  unfold tabsOf at hT
  obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 hT
  obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.1 hT
  exact ⟨_, inAt_of hp ht hK⟩

/-- **THE PREMISE RIDES.** CONDITIONAL on: the runs' input is made at s; s's ledger has its sizes;
the library's two relations lead from s to u. -/
theorem pre_forth (A : Attention.Plan) {s u : First.S} {a : First.AttOwn} {h : Heard}
    {gl : Forest.Heard} {x : P.Runs.In × Nat} (hh : s.here = .att a) (h5 : a.heard5 = some h)
    (hg : a.g = some gl) (hz : PscRun.Sized a.F)
    (hx : K5Law.inAt (P.parCOf A) gl h a.F = some x) (C : K5Law.CarK5 s u)
    (K : K5Law.Kept5 s u) (n : Nat) :
    preK5 A n u ∧ P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) u = some x := by
  have s5 : s.heard5? = some h := by
    unfold First.S.heard5?
    rw [hh]
    exact h5
  have sF : s.fork? = some a.F := by
    unfold First.S.fork?
    rw [hh]
  have sL : s.look? = some gl := by
    unfold First.S.look?
    rw [hh]
    exact hg
  have u5 := C.1 h s5
  obtain ⟨G, uF, lat, zG⟩ := C.2 a.F sF hz
  obtain ⟨b, hb, b5⟩ : ∃ b, u.here = .att b ∧ b.heard5 = some h := by
    unfold First.S.heard5? at u5
    cases hu : u.here with
    | att b =>
      rw [hu] at u5
      exact ⟨b, rfl, u5⟩
    | _ =>
      rw [hu] at u5
      cases u5
  have bF : b.F = G := by
    unfold First.S.fork? at uF
    rw [hb] at uF
    exact Option.some.inj uF
  have bg : b.g = some gl := by
    have e := K.1
    rw [sL] at e
    unfold First.S.look? at e
    rw [hb] at e
    exact e
  have hK : (G.trees[(P.parCOf A).iU3]?).map (·.K) = (a.F.trees[(P.parCOf A).iU3]?).map (·.K) := by
    have e := K5Law.tree_of_shapes K.2 sF uF (P.parCOf A).iU3
    have e' := congrArg (Option.map Prod.snd) e
    simpa only [Option.map_map, Function.comp_def] using e'
  have hx' : K5Law.inAt (P.parCOf A) gl h b.F = some x := by
    rw [bF]
    exact K5Law.inAt_forth (K5Law.later_of_fo lat fun _ => zG) hK hx
  refine ⟨?_, ?_⟩
  · unfold preK5
    rw [vals_at A hb b5 bg]
    exact vals_of_in A hx'
  · rw [inOf_at hb b5 bg]
    exact hx'

end H2K5.Honest

#print axioms H2K5.Honest.valsT_of_K3Pts
#print axioms H2K5.Honest.valsTS_of_K3Pts
#print axioms H2K5.Honest.in_of_vals
#print axioms H2K5.Honest.pre_forth
