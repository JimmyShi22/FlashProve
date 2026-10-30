-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05CovAtReaders.lean: kind K5: EVERY FORM THAT THE READERS OF AN ATTENTION LINK GIVE, AT FIVE RUNS, NAMES ENTRIES OF THE TABLES' PART OF THE ARRAY OF THE READS ALONE (Cov A.iU3 K A.nW: Att/Claims/Covered.lean): the premise hE of the
attention segments' half of the exchange (Att/ArmAtt.lean: armCellIn_att), at Rd := the readers of the link (Johnson/Desc/First/Batch/ReadersOfLink.lean), WHATEVER STANDS IN THEIR TWO HOLES.

"WHATEVER STANDS IN THE HOLES" WANTS THE RUN's OWN YES: where the run under a name is silent the readers of the link answer with their second hole, and nothing can be said of that answer. So each of the five stands under "the run's reader answers R₀ at s".
  (2, "first") · (2, "second") · (2, "join"): readers_hold₀ (Att/K05BehindWorthReaders.lean), under the kind's law's own letters (Returns · Said · BehindOk₀), at the verifier's state after the kind's sub-protocol.
  (2, "keys"): keys_hold₀, here: THE RUN STATES NO FORM (Att/RunsK.lean: keysK returns ([], s)): Cov is vacuous.
  (1, "planes"): from the raw run's yes (hrun), by reader_any, here.
The runs of the seated link stand behind the seat's guard: reader_seated | readerOf_guarded (Att/K05ReadersGuarded.lean).
Main names: cov_at_link (general) · reader_seated · keys_hold₀ · cov_first · cov_second · cov_join · cov_keys · reader_any (general) · cov_planes.
PREMISES THAT ALL FIVE SHARE (cov_of_rows', Att/K05CovOfRows.lean): ha : segAt? s = some a · hT : the public test formsInT accepts at (piece, run) · hC : the layout's array of the reads has at most nW columns · hW : nW ≤ K.
THE LETTERS UNDER "FOR ALL": hsame: a law of the guard's test · hC: c, Ar pinned by two equations at a · in the conclusions R pinned by the readers' equation.
Att/K05BehindWorthReaders.lean is imported by a line of its own: BehindOk₀ and readers_hold₀ stand there.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05CovOfRows
import Johnson.Desc.First.Att.K05PlanesEnts
import Johnson.Desc.First.Att.K05ReadersGuarded
import Johnson.Desc.First.Att.K05BehindWorthReaders
import Johnson.Desc.First.StateLedger

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

/-- **GENERAL: where the run's reader answers R₀ and R₀'s forms name row 0 of the array t alone, every form that the readers of the link give is covered.** -/
theorem cov_at_link (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (hn : (run == "K8.equations") = false) {s : First.S} {a : VerifiableInference.Desc.K9.Part} {t K nW : ℕ} {R₀ : VerifiableInference.Desc.K9.Read}
    (hy : readerOf (statesOfLink L) piece run s = some R₀)
    (hen : ∀ f ∈ R₀.forms, ∀ x ∈ f.ents.toList, x.tree = t ∧ x.row = 0) (ha : segAt? s = some a)
    (hT : formsInT (readersOfLink H L) own piece run s = true)
    (hC : ∀ c Ar, a.L.arrayOf[t]? = some c → reqArray a.L.check.rows.layout c.1 c.2 = some Ar → Ar.sizeC ≤ nW) (hW : nW ≤ K) :
    ∀ R, (readersOfLink H L).forms piece run s = some R → ∀ f ∈ R.forms, Cov t K nW f :=
  cov_of_rows (readersOfLink H L) own piece run ha hT (fun R hR f hf x hx => by
    obtain rfl : R₀ = R := Option.some.inj ((hRds_of_link H L piece run s R₀ hn hy).symm.trans hR)
    exact hen f hf x hx) hC hW

/-- What the reader gives at the kind's own four runs it gives at the seated link's block 2, through the guard. -/
theorem reader_seated {L : VerifiableInference.Desc.Link First.S Claim} {A : Attention.Plan} {same : First.S → First.S → Bool}
    (hL : statesOfLink L 2 = (runsN A).map (guardC same)) (hsame : ∀ s t : First.S, t.out = s.out → same s t = true)
    {name : String} {s : First.S} {R : VerifiableInference.Desc.K9.Read} (hr : readerOf (fun _ => runsN A) 2 name s = some R) :
    readerOf (statesOfLink L) 2 name s = some R :=
  readerOf_guarded same (st₀ := fun _ => runsN A) hL hr fun c z hc hz =>
    hsame s z.2 (runsN_keep A c (List.mem_of_find?_eq_some hc) 0 s z hz)

/-- **The reader's answer at "keys": no form.** -/
theorem keys_hold₀ (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard}
    {G : Fork} (B : BehindOk₀ A Kc gL (behind s₀ att h G)) {l : Left} {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    {kf : Array Aff} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn (padOfO gL.shape) kf G [] xj A.seam.tl A.nW
      (lookOfO (parCOf A).geo.lmb gL)) :
    readerOf (fun _ => runsN A) 2 "keys" (behind s₀ att h G) = some { forms := [], late := [] } := by
  obtain ⟨a₀, g₀, T, he, hg, sm, hlk, hT, hK, hR1, hW, hun⟩ := B
  obtain rfl : a₀ = { att with F := G, heard5 := some h } := by
    have : (First.Here.att { att with F := G, heard5 := some h }) = .att a₀ := he
    cases this
    rfl
  have hT' : G.trees[A.iU3]? = some T := hT
  have u3 : i.iU3 = A.iU3 := Rt.u3.trans eu
  have left : LeftIs (geoOf A.S) g₀.zk h G l := by rw [sm.zk]; exact Rt.left
  have zkI : i.zk = g₀.zk := by rw [sm.zk]; exact Rt.zkI
  have points : pointsOf i.g g₀.zk h l = some i.p := by rw [sm.zk]; exact Rt.points
  have tables : tablesP i.g (K5Law.matsOf A.seam.tl.mats) A.nW (lookOfO (parCOf A).geo.lmb g₀) i.p = some i.t := by
    rw [lookOfO_same sm]; exact Rt.tables
  have hin := inAt_is A left Rt.geo zkI u3 points tables hT' hK
  have hk : keysOfO A (behind s₀ att h G) = some kf :=
    keysOfO_is A (s := behind s₀ att h G) rfl hg rfl rfl hin Rt.first (by rw [sm.shape]; exact Rt.keys)
  refine K5Law.reader_run (K5Law.find_keys A (states := fun _ => runsN A) (runsN_is A)) ?_ (G := G) rfl fun f hf => absurd hf (List.not_mem_nil)
  show VerifiableInference.Desc.named "K5.keys" (keysK (seatCO (parCOf A)) (parCOf A) (behind s₀ att h G)) = .ok ([], behind s₀ att h G)
  have hk' : keysOfK (seatCO (parCOf A)) (parCOf A) (behind s₀ att h G) = some kf := hk
  unfold keysK
  rw [hk']
  rfl

/-- The array of the reads in the ledger after the kind's sub-protocol. -/
theorem u3At_of_behind {A : Attention.Plan} {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard} {G : Fork}
    (B : BehindOk₀ A Kc gL (behind s₀ att h G)) : U3At A Kc G := by
  obtain ⟨a₀, g₀, T, he, _, _, _, hT, hK, hR1, hW', _⟩ := B
  obtain rfl : a₀ = { att with F := G, heard5 := some h } := by
    have : (First.Here.att { att with F := G, heard5 := some h }) = .att a₀ := he
    cases this
    rfl
  exact ⟨T, hT, hK, hW', hR1⟩

section Four
variable (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (own : List (ℕ × ℕ)) {same : First.S → First.S → Bool}
  (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) 
  {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard} {G : Fork}
  {xr : Params.AttentionRounds} {Ls : Lists} (hs : Said xr h G Ls) (B : BehindOk₀ A Kc gL (behind s₀ att h G))
  (hc : gL.cEnd.ents = #[]) {l : Left} {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP} {kf : Array Aff}
  {xj : Aff × Fork × OnBytes.K.Kc.Tape}
  (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn (padOfO gL.shape) kf G [] xj A.seam.tl A.nW
    (lookOfO (parCOf A).geo.lmb gL))
  (hL : statesOfLink L 2 = (runsN A).map (guardC same)) (hsame : ∀ s t : First.S, t.out = s.out → same s t = true)
  {a : VerifiableInference.Desc.K9.Part} {K : ℕ} (ha : segAt? (behind s₀ att h G) = some a)
  (hC : ∀ c Ar, a.L.arrayOf[A.iU3]? = some c → reqArray a.L.check.rows.layout c.1 c.2 = some Ar → Ar.sizeC ≤ A.nW)
  (hW : A.nW ≤ K)
include eu hs B hc Rt hL hsame ha hC hW

theorem cov_first (hT : formsInT (readersOfLink H L) own 2 "first" (behind s₀ att h G) = true) :
    ∀ R, (readersOfLink H L).forms 2 "first" (behind s₀ att h G) = some R → ∀ f ∈ R.forms, Cov A.iU3 K A.nW f :=
  cov_at_link H L own 2 "first" (by decide) (reader_seated hL hsame (readers_hold₀ A A0 eu (states := fun _ => runsN A) rfl hs B hc Rt).1)
    (fun f hf => ents_of_returns Rt eu hs (u3At_of_behind B) hc f (by
      have hf' : f ∈ l₁ := hf
      simp [hf'])) ha hT hC hW

theorem cov_second (hT : formsInT (readersOfLink H L) own 2 "second" (behind s₀ att h G) = true) :
    ∀ R, (readersOfLink H L).forms 2 "second" (behind s₀ att h G) = some R → ∀ f ∈ R.forms, Cov A.iU3 K A.nW f :=
  cov_at_link H L own 2 "second" (by decide) (reader_seated hL hsame (readers_hold₀ A A0 eu (states := fun _ => runsN A) rfl hs B hc Rt).2.1)
    (fun f hf => ents_of_returns Rt eu hs (u3At_of_behind B) hc f (by
      have hf' : f ∈ l₂ := hf
      simp [hf'])) ha hT hC hW

theorem cov_join (hT : formsInT (readersOfLink H L) own 2 "join" (behind s₀ att h G) = true) :
    ∀ R, (readersOfLink H L).forms 2 "join" (behind s₀ att h G) = some R → ∀ f ∈ R.forms, Cov A.iU3 K A.nW f :=
  cov_at_link H L own 2 "join" (by decide) (reader_seated hL hsame (readers_hold₀ A A0 eu (states := fun _ => runsN A) rfl hs B hc Rt).2.2)
    (fun f hf => ents_of_returns Rt eu hs (u3At_of_behind B) hc f (by
      have hf' : f ∈ [xj.1] := hf
      simp [List.mem_singleton.1 hf'])) ha hT hC hW

omit hs hc in
theorem cov_keys (hT : formsInT (readersOfLink H L) own 2 "keys" (behind s₀ att h G) = true) :
    ∀ R, (readersOfLink H L).forms 2 "keys" (behind s₀ att h G) = some R → ∀ f ∈ R.forms, Cov A.iU3 K A.nW f :=
  cov_at_link H L own 2 "keys" (by decide) (reader_seated hL hsame (keys_hold₀ A A0 eu B Rt))
    (fun f hf => absurd hf (List.not_mem_nil)) ha hT hC hW

end Four

/-- **GENERAL: a run's yes, with the reader's side tests, gives the reader's answer.** -/
theorem reader_any {st : ℕ → List (RunOf First.S)} {b : ℕ} {name nm : String}
    {r : ℕ → First.S → Except String (List Claim × First.S)}
    (hf : ((st b).find? fun c => c.1 == name) = some (nm, r)) {t : First.S} {F G' : Fork} {z : List Claim × First.S}
    (hF : t.fork? = some F) (hr : r 0 t = .ok z) (hG : z.2.fork? = some G')
    (hz : (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true) :
    readerOf st b name t = some { forms := z.1.map (·.form), late := lateOf F G' } := by
  unfold readerOf
  rw [hf]
  show (match r 0 t, t.fork? with
    | .ok z, some F => _
    | _, _ => none) = _
  rw [hr, hF]
  show (z.2.fork?.bind fun G => _) = _
  rw [hG]
  show (if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true then
    some ({ forms := z.1.map (·.form), late := lateOf F G' } : VerifiableInference.Desc.K9.Read) else none) = _
  rw [if_pos hz]

/-- **(1, "planes")**, from the raw run's yes. -/
theorem cov_planes (H : LinkHoles) (L : VerifiableInference.Desc.Link First.S Claim) (own : List (ℕ × ℕ))
    {same : First.S → First.S → Bool} (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f ∧ (claim f).runs.isEmpty = true ∧ (claim f).eqFirst.isNone = true) (A : Attention.Plan) (lm : ℕ)
    {sP s' : First.S} {a₀ : First.AttOwn} {g : Forest.Heard} {clP : List Claim} (hs : sP.here = .att a₀)
    (hg : sP.lookHeard? = some g)
    (hrun : VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A) 0 sP = .ok (clP, s'))
    (hb : Bare g.leaves.start) (hU : U3At A (plannedK A) a₀.F) {nm : String}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) lm (readersOfO A))))
    (hsame : ∀ s t : First.S, t.out = s.out → same s t = true) {a : VerifiableInference.Desc.K9.Part} {K : ℕ}
    (ha : segAt? sP = some a) (hT : formsInT (readersOfLink H L) own 1 "planes" sP = true)
    (hC : ∀ c Ar, a.L.arrayOf[A.iU3]? = some c → reqArray a.L.check.rows.layout c.1 c.2 = some Ar → Ar.sizeC ≤ A.nW)
    (hW : A.nW ≤ K) :
    ∀ R, (readersOfLink H L).forms 1 "planes" sP = some R → ∀ f ∈ R.forms, Cov A.iU3 K A.nW f := by
  have hF : sP.fork? = some a₀.F := fork_front hs
  obtain ⟨_, rows, G, _, _, _, ecl, es⟩ := VerifiableInference.OnPublicFiles.planesRun_cut (VerifiableInference.Desc.K3.seatCalls claim) lm
    (readersOfO A) (F := a₀.F) (g := g) hF hg hrun
  have es' : s' = sP.putFork (G.paid g.owedPlanes) := es
  have en := hents_of_run A (VerifiableInference.Desc.K3.seatCalls claim) (·.form) (fun f => (hcl f).1) lm hg hrun hb hs hU
  obtain ⟨T, hT0, _, _, hR1⟩ := hU
  have hz : (clP.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow a₀.F)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    have h3 : c.form.ents.all (ownRow a₀.F) = true := all_ownRow fun e he =>
      ⟨(en c.form (List.mem_map.2 ⟨c, hc, rfl⟩) e he).2, T, by rw [(en c.form (List.mem_map.2 ⟨c, hc, rfl⟩) e he).1]; exact hT0, hR1⟩
    rw [ecl] at hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.1 hc
    have hc2 : (claim f).runs.isEmpty = true := (hcl f).2.1
    have hc3 : (claim f).eqFirst.isNone = true := (hcl f).2.2
    show ((claim f).runs.isEmpty && (claim f).eqFirst.isNone && (claim f).form.ents.all (ownRow a₀.F)) = true
    have h3' : (claim f).form.ents.all (ownRow a₀.F) = true := h3
    rw [hc2, hc3, h3']
    rfl
  exact cov_at_link H L own 1 "planes" (by decide)
    (reader_any (nm := nm) (r := (guardC same (nm, _)).2) hL hF
      (guardC_yes same (nm, _) hrun (hsame _ _ (by rw [es']; exact out_putFork _ _)))
      (G' := G.paid g.owedPlanes) (by rw [es']; exact First.S.fork_putFork sP a₀.F _ hF) hz)
    (fun f hf => en f hf) ha hT hC hW

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.cov_at_link
#print axioms VerifiableInference.Desc.First.Att.P.keys_hold₀
#print axioms VerifiableInference.Desc.First.Att.P.cov_first
#print axioms VerifiableInference.Desc.First.Att.P.cov_second
#print axioms VerifiableInference.Desc.First.Att.P.cov_join
#print axioms VerifiableInference.Desc.First.Att.P.cov_keys
#print axioms VerifiableInference.Desc.First.Att.P.reader_any
#print axioms VerifiableInference.Desc.First.Att.P.cov_planes
