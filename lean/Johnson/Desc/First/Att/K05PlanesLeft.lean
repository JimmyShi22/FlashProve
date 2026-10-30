-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanesLeft.lean: kind K5: THE PUBLIC TEST THAT IS TIED TO THE LOOKUP ARGUMENT's RUN "planes" SAYS YES AT THE VERIFIER's STATE AFTER THE KIND's SUB-PROTOCOL (formsInT_planes_behind, Att/K05PlanesIn.lean), WITH THE OTHER FILES' SHARE CALLED, NOT ASSUMED: from ONE test on what the
lookup argument has left and the ledger AFTER the kind's hearing: leftAtB (Johnson/Desc/First/FillBare.lean). (leftAtB_later, Door/Law/K5FillPlus.lean, carries the test there from the ledger in front.)
CALLED: planeClaimsOwn_some (Johnson/Desc/Kinds/Law/SilentPlanes.lean: the three claims' own text returns, from the sumcheck's four marks and the return of hideRun) · planes_slotIn (Johnson/Top/H/Keep/PlanesSlotsIn.lean: each slot that a claim names passes slotIn) ·
the library's hideRun_returns (OnBytes/Tie/Pv/Psc/PscRoom.lean).
Main names:
  leftAt_parts: the test's seven parts, at any g and F (parts_of, Johnson/Desc/First/FillBare.lean, reads them at a layers' segment's state).
  bare_of_named · filledA_of_named: what a form that passes namedB is.
  window_ret: where the sumcheck's window is there and free, hideRun returns.
  formsInT_planes_left: THE END.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PlanesIn
import Johnson.Desc.First.FillBare
import Johnson.Desc.Kinds.Law.SilentPlanes
import Johnson.Top.H.Keep.PlanesSlotsIn
import Johnson.Top.H.K3SeatFits
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt inAt_is firstAt_is secondAt_is readers_at runsN_is)
open VerifiableInference.Desc.K9 (Read lateOf ownRow readerOf RunOf runOfForms)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink LinkHoles formsInT)
open K5Law (Cov)
open OnBytes.Road.Rows (RowsIn Bare)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.Desc.K9 (slotIn affInT entInT lateOk mergeOf)
open VerifiableInference.Desc.First.Look (planeClaimsOwn)
open VerifiableInference.Desc.First.FillBare (leftAtB namedB readyB winFreeB ents_of_named)
open VerifiableInference.Desc.Kinds.Head.Law (planeClaimsOwn_some)
open VerifiableInference.OnPublicFiles (planes_slotIn seatCalls_fits)
open OnBytes.K.Kc (Fl)
open K5Law (SlotsIn)

/-- **The test's seven parts.** -/
theorem leftAt_parts {g : Forest.Heard} {F : Fork} (h : leftAtB g F = true) :
    (∀ f ∈ g.rows.toList, namedB F f = true) ∧ namedB F g.cEnd = true ∧ namedB F (Aff.slot g.sBit) = true ∧
      namedB F g.leaves.start = true ∧ readyB g.leaves = true ∧ g.leaves.first + g.leaves.walk.1.length ≤ F.next ∧
      winFreeB g.leaves F = true := by
  simp only [leftAtB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem bare_of_named {F : Fork} {f : Aff} (h : namedB F f = true) : Bare f := by
  intro Q y hy
  rw [ents_of_named h] at hy
  cases hy

theorem filledA_of_named {F : Fork} {f : Aff} (h : namedB F f = true) : _root_.Fo.FilledA F f := by
  unfold namedB at h
  have e := (Eq.mp (Bool.and_eq_true _ _) h).2
  intro x hx
  have := List.all_eq_true.1 e x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- **Where the sumcheck's window is there and free, hideRun returns.** -/
theorem window_ret {p : Psc} {G : Fork} (hw : winFreeB p G = true) (zG : Sized G) (f : E) :
    ∃ G₁, G.hideRun p.first (Array.replicate p.walk.1.length zeroE) f = some G₁ := by
  refine PscRun.hideRun_returns p.first _ f zG.got fun i hi => ?_
  have hi' : i < p.walk.1.length := by simpa using hi
  unfold winFreeB at hw
  have h0 := List.all_eq_true.1 hw i (List.mem_range.2 hi')
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h0
  refine ⟨h0.1, fun hF => ?_⟩
  have hF' : G.gotF.getD (p.first + i) false = true := hF
  rw [h0.2] at hF'
  cases hF'

/-- **THE END.** -/
theorem formsInT_planes_left (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (own : List (ℕ × ℕ))
    {same : First.S → First.S → Bool} (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f ∧ (claim f).runs.isEmpty = true ∧ (claim f).eqFirst.isNone = true) (A : Attention.Plan) (lm : ℕ)
    {s : First.S} {att : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard} {G : Fork}
    (hh : hear x (att.F, rs, 0) = some (h, G, [], 0)) (hz : Sized att.F) {i : Runs.In} {K : ℕ}
    (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some (i, K)) (U : U3There own s att (parCOf A))
    {gL : Forest.Heard} (hg : att.lookHeard = some gL) {nm : String}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A))))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true)
    (hUnp : VerifiableInference.Desc.K3.unpaid G gL.owedPlanes = true)
    (hleft : leftAtB gL G = true) (hok : VerifiableInference.Desc.First.Look.planesOk gL.shape lm = true)
    (hcols : ∀ r, readersOfO A (behind s att h G) = some r →
      (∀ e col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - lm) → ∃ f, r.1 e col = some f) ∧
        ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - lm) → ∃ f, r.2 col = some f) :
    formsInT (readersOfLink H L) own 1 "planes" (behind s att h G) = true := by
  obtain ⟨_, _, hB, hst, hrd, _, hfree⟩ := leftAt_parts hleft
  obtain ⟨zG, _⟩ := hear_below hh hz
  obtain ⟨G₁, hG₁⟩ := window_ret hfree zG (subE zeroE oneE)
  obtain ⟨eg, _, _, _, _, lk, _, _, _, ht⟩ := inOf_behind hin
  rw [← eg] at ht
  refine formsInT_planes_behind H L own claim hcl A lm hh hz hin U hg hL hsame hUnp (bare_of_named hst) (fun r hr => ?_)
    (fun clP s' G' hrun hG' => ?_)
  · exact ⟨_, planeClaimsOwn_some gL lm r.1 r.2 G G₁ [] hok
      (fun e col hc => Option.isSome_iff_exists.2 ((hcols r hr).1 e col hc))
      (fun col hc => Option.isSome_iff_exists.2 ((hcols r hr).2 col hc)) hrd hG₁⟩
  · have R := fun r' (hr' : readersOfO A (behind s att h G) = some r') =>
      readers_forms (Ps := fun j => j < G.ns ∧ PscRun.Filled G j) hin (K5Law.len_in ht) hr'
    exact planes_slotIn (VerifiableInference.Desc.K3.seatCalls claim) (·.form) (seatCalls_fits claim (·.form) fun f => (hcl f).1) lm
      (readersOfO A) (s := behind s att h G) (g := gL) own none (partAt s att G none) rfl hg hrun hG' ⟨zG.vp, zG.mf, zG.got⟩
      ((filledA_of_named hB) (gL.sBit, oneE) (by simp [Aff.slot])) (filledA_of_named hst)
      (fun r' hr' e col f hf => ((R r' hr').1 e col f hf).1) (fun r' hr' col f hf => ((R r' hr').2 col f hf).1) U.mask
      (fun _ _ _ _ => by simp)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.leftAt_parts
#print axioms VerifiableInference.Desc.First.Att.P.window_ret
#print axioms VerifiableInference.Desc.First.Att.P.formsInT_planes_left
