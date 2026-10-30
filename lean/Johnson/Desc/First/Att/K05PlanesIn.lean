-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanesIn.lean: kind K5: THE PUBLIC TEST THAT IS TIED TO THE LOOKUP ARGUMENT's RUN "planes" (formsInT, Johnson/Desc/First/Batch/FormsIn.lean) SAYS YES AT THE VERIFIER's STATE AFTER THE KIND's SUB-PROTOCOL, at the readers of a link: a JOIN of the kind's share and
the lookup argument's files' share, the latter as named premises.
THE KIND's SHARE, CALLED: the claims' seat reads (hin) · so the two readers of the planes' columns return (Att/Guest.lean's make) · what they hand out lies in the tables' part (readers_forms, Att/K05ReadersThere.lean) · so do the run's three claims (planes_cov, Att/K05PlanesRet.lean) · such
entries pass the test on entries and the reader's side test (form_there, Att/K05JoinThere.lean, under U3There) · the run keeps the number of slots, so the late slots pass lateOk at the ledger in front (planes_ns · lateOk_front) · the guarded run's reader answers (reader_any · guardC_yes ·
hRds_of_link).
THE LOOKUP ARGUMENT's FILES' SHARE, PREMISES: hUnp (the claims are not yet made) · hBare (the start form of the leaves' sumcheck is bare) · hPC (the three claims' own text returns at the readers' return) · hSl (each slot that a claim names passes slotIn).
Main name: formsInT_planes_behind.
IS IT EMPTY HERE? An implication.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PlanesRet
import Johnson.Desc.First.Att.K05ReadersThere
import Johnson.Desc.First.Att.K05CovAtReaders

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
open OnBytes.K.Kc (Fl)
open K5Law (SlotsIn)

theorem formsInT_planes_behind (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (own : List (ℕ × ℕ))
    {same : First.S → First.S → Bool} (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f ∧ (claim f).runs.isEmpty = true ∧ (claim f).eqFirst.isNone = true) (A : Attention.Plan) (lm : ℕ)
    {s : First.S} {att : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard} {G : Fork}
    (hh : hear x (att.F, rs, 0) = some (h, G, [], 0)) (hz : Sized att.F) {i : Runs.In} {K : ℕ}
    (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some (i, K)) (U : U3There own s att (parCOf A))
    {gL : Forest.Heard} (hg : att.lookHeard = some gL) {nm : String}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A))))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true)
    (hUnp : VerifiableInference.Desc.K3.unpaid G gL.owedPlanes = true) (hBare : Bare gL.leaves.start)
    (hPC : ∀ r, readersOfO A (behind s att h G) = some r →
      ∃ z, planeClaimsOwn gL lm (fun e col => Fl.need (r.1 e col)) (fun col => Fl.need (r.2 col)) G [] = some z)
    (hSl : ∀ clP s' G', VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A) 0
        (behind s att h G) = .ok (clP, s') → s'.fork? = some G' →
      ∀ c ∈ clP, ∀ y ∈ c.form.slots.toList, slotIn own none (lateOf G G') (partAt s att G none) y.1 = true) :
    formsInT (readersOfLink H L) own 1 "planes" (behind s att h G) = true := by
  have hF : (behind s att h G).fork? = some G := rfl
  have hgP : (behind s att h G).lookHeard? = some gL := hg
  have hF' : (VerifiableInference.Desc.K3.seatCalls claim).fork (behind s att h G) = some G := rfl
  have hg' : (VerifiableInference.Desc.K3.seatCalls claim).heard (behind s att h G) = some gL := hg
  obtain ⟨eg, eu, hK, _, _, lk, _, _, _, ht⟩ := inOf_behind hin
  obtain ⟨zG, bl⟩ := hear_below hh hz
  rw [← eg] at ht
  obtain ⟨r, hr⟩ : ∃ r, readersOfO A (behind s att h G) = some r := by
    unfold readersOfO readersOfK
    rw [hin]
    exact ⟨_, rfl⟩
  obtain ⟨clP, s', hrun⟩ := planesRun_ret (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A) 0 hF' hg' hUnp hr (hPC r hr)
  obtain ⟨G', es, ens⟩ := planes_ns (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A) hF' hg' ⟨zG.vp, zG.mf, zG.got⟩ hrun
  have es' : s' = (behind s att h G).putFork G' := es
  have hG' : s'.fork? = some G' := by rw [es']; exact First.S.fork_putFork _ G _ hF
  have hcov : ∀ c ∈ clP, Cov (parCOf A).iU3 K (parCOf A).nW c.form := by
    have R := fun r' (hr' : readersOfO A (behind s att h G) = some r') =>
      readers_forms (Ps := fun _ => True) hin (K5Law.len_in ht) hr'
    rw [← eu]
    exact planes_cov (VerifiableInference.Desc.K3.seatCalls claim) (·.form) (fun f => (hcl f).1) lm (readersOfO A) hg' hrun hBare
      (fun r' hr' e col f hf => ((R r' hr').1 e col f hf).2) (fun r' hr' col f hf => ((R r' hr').2 col f hf).2)
  have hthere : ∀ c ∈ clP, (c.form.ents.toList.all fun e => entInT own (partAt s att G none) e) = true ∧
      ∀ e ∈ c.form.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1 := by
    intro c hc
    have q := form_there own zG U bl.trees hK none (f := { c.form with slots := #[] })
      (by intro y hy; cases hy) (hcov c hc)
    refine ⟨?_, q.2⟩
    have q1 := q.1
    unfold affInT at q1
    exact (Bool.and_eq_true _ _ ▸ q1).1
  obtain ⟨_, rows, G₁, _, _, _, ecl, _⟩ := VerifiableInference.OnPublicFiles.planesRun_cut (VerifiableInference.Desc.K3.seatCalls claim) lm
    (readersOfO A) (F := G) (g := gL) hF' hg' hrun
  have hside : (clP.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow G)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    have h3 : c.form.ents.all (ownRow G) = true := all_ownRow (hthere c hc).2
    rw [ecl] at hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.1 hc
    have hc2 : (claim f).runs.isEmpty = true := (hcl f).2.1
    have hc3 : (claim f).eqFirst.isNone = true := (hcl f).2.2
    show ((claim f).runs.isEmpty && (claim f).eqFirst.isNone && (claim f).form.ents.all (ownRow G)) = true
    have h3' : (claim f).form.ents.all (ownRow G) = true := h3
    rw [hc2, hc3, h3']
    rfl
  have hy : (readersOfLink H L).forms 1 "planes" (behind s att h G) = some { forms := clP.map (·.form), late := lateOf G G' } :=
    hRds_of_link H L 1 "planes" _ _ (by decide)
      (reader_any (nm := nm) (r := (guardC same (nm, _)).2) hL hF
        (guardC_yes same (nm, _) hrun (hsame _ _ (by rw [es']; exact out_putFork _ _))) hG' hside)
  unfold formsInT
  rw [segAt_behind, hy]
  show (lateOk (lateOf G G') (partAt s att G none) &&
    (clP.map (·.form)).all fun f => affInT own none (lateOf G G') (partAt s att G none) f) = true
  have hl : lateOk (lateOf G G') (partAt s att G none) = true := lateOk_front (partAt s att G none) G' (Nat.le_of_eq ens)
  rw [hl, Bool.true_and]
  refine List.all_eq_true.2 fun f hf => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
  unfold affInT
  rw [(hthere c hc).1, Bool.true_and]
  exact List.all_eq_true.2 fun y hy' => hSl clP s' G' hrun hG' c hc y hy'

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.formsInT_planes_behind
