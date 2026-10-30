-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanesBack.lean: kind K5: THE WORTH OF THE LOOKUP ARGUMENT's CLAIMS ON THE PLANES, IN FRONT OF THE KIND's SUB-PROTOCOL, FROM THE TABLE's ITEM formsT m 2 "planes" AT THE VERIFIER's STATE AFTER IT: the row K05_host_planes_door (Att/K05HostPlanesDoor.lean) CALLED, at one state, with
all that it asks of the run drawn FROM THE ITEM's OWN SENTENCE: formsTQ holds "the reader answers R"; link_cut | ranAt_of_cut (Johnson/Top/H/Keep/ReaderIsRun.lean: the reader is the run) give the guarded run's yes; guardC_inv takes the guard off. So no premise "the run
returns" stands here.
Main names: guardC_inv · planes_laterFo (the ledger behind the run is a later one) · lay_of_parts (the kind's lay returns where nothing of the kind's own was received yet, the seat's copy is there, and there is no mark) · worthPlanes_behind.
PAID INSIDE: K3PlanesPaid (k3PlanesPaid_of ∘ planes_worth at bitOf | pinOf of the kind's readers) · K3RanAt · LateLaid (lateLaid_at, from the item's own yes of affInT) · the entries' rows (hents_of_run) · the readers' return below the number of columns (readers_ret_plan).
PREMISES THAT STAY: see the theorem; of the verifier's state only hBare (the start form of the leaves' sumcheck is bare) is not drawn from what the clause has in hand.
IS IT EMPTY HERE? An implication.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05HostPlanesDoor
import Johnson.Desc.First.Att.K05HostPlanesPlan
import Johnson.Desc.First.Att.K05PlanesEnts
import Johnson.Desc.First.Att.K05PlanesRet
import Johnson.Desc.First.Att.K05ReadersRet
import Johnson.Desc.First.Att.K05ReadersGuarded
import Johnson.Desc.First.Att.K05FrontRides
import Johnson.Desc.First.Att.K05FormsMade
import Johnson.Top.H.Keep.ReaderIsRun
import Johnson.Desc.First.StateLedger
import Johnson.Top.H.K3OutPaid
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Road OnBytes.Road.Rows OnBytes.Params
open VerifiableInference.Desc (Wit Claim)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt? RunOf statesOfLink readersOfLink LinkHoles lateOf affInT)
open VerifiableInference.Desc.Sound (GQ Stated Mem seatTab msgsOf MsgT formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu K3PlanesPaid K3RanAt K3WorthPlanes link_cut ranAt_of_cut k3PlanesPaid_of planes_worth
        seatCalls_fits bitOf pinOf planesRun_cut quiet_need paid_laterFo)
open K5Law (funsAt matsOf PosG OfPlan ofPlan_shape ofPlan_rows ofPlan_matsFit)

/-- **The guard taken off**: a guarded run's yes is the run's. -/
theorem guardC_inv (same : First.S → First.S → Bool) (c : RunOf First.S) {n : ℕ} {t : First.S} {z : List Claim × First.S}
    (h : (guardC same c).2 n t = .ok z) : c.2 n t = .ok z := by
  have h' : ((c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y) = .ok z := h
  cases hc : c.2 n t with
  | error e => rw [hc] at h'; cases h'
  | ok y =>
    rw [hc] at h'
    have h2 : ((seatSame same t y.2).map fun _ => y) = .ok z := h'
    cases hs : seatSame same t y.2 with
    | error e => rw [hs] at h2; cases h2
    | ok u =>
      rw [hs] at h2
      exact h2

/-- **The ledger behind the run "planes" is a later one, in the sense that the forms' worlds read** (Fo.Later; planes_later, Johnson/Top/H/K3LedgerKeeps.lean, says it in the sumchecks' sense, PscRun.Later). -/
theorem planes_laterFo {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl) (lm : ℕ) (readers : VerifiableInference.Desc.K3.Readers S)
    {n : ℕ} {s s' : S} {cl : List Cl} {F : Fork} {g : Forest.Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hz : PscRun.Sized F) (hrun : VerifiableInference.Desc.K3.planesRun seat lm readers n s = .ok (cl, s')) :
    ∃ G', s' = seat.mark s G' ∧ _root_.Fo.Later F G' := by
  obtain ⟨r, rows, G, u, hr, h1, _, es⟩ := planesRun_cut seat lm readers hf hg hrun
  obtain ⟨_, row, p', h2, _⟩ := _root_.Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, hh, -, -⟩ := _root_.Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  exact ⟨_, es, (_root_.Fo.hideRun_later hz hh).trans (paid_laterFo G _)⟩

/-- **The kind's lay returns.** -/
theorem lay_of_parts {s : First.S} {a : First.AttOwn} {g : Forest.Heard} (e : s.here = .att a) (h5 : a.heard5 = none) (hg : a.g = some g)
    (hu : s.failed = none) (h : Heard) (G : Fork) : seatSO.lay s h G = some (behind s a h G) := by
  show (match s.here with
      | .att a => a.g.bind fun _ =>
        (First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h).toOption
      | _ => none) = _
  rw [e]
  simp only [hg, Option.bind_some, First.S.hear5?, First.S.hear5, h5, Option.isSome_none,
    Bool.false_eq_true, if_false, First.S.unmarked, hu, Except.toOption, behind]

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat)

/-- **THE WORTH OF THE CLAIMS ON THE PLANES, IN FRONT, FROM THE ITEM BEHIND.** -/
theorem worthPlanes_behind (Ex : Iop.ExtSpec) (Wp : Type) (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)
    (hOP : OfPlan A) (hPos : PosG (parCOf A).geo) (H : LinkHoles)
    (L : VerifiableInference.Desc.Link First.S Claim) {same : First.S → First.S → Bool} (claim : Aff → Claim)
    (hcl : ∀ f, (claim f).form = f) {nm : String}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) A.S.cf.lmb (readersOfO A))))
    {s : First.S} {att : First.AttOwn} {xr : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard} {G : Fork}
    (e : s.here = .att att) (hu : s.failed = none) (h5 : att.heard5 = none)
    (hh : hear xr (att.F, rs, 0) = some (h, G, [], 0))
    (hsil : H.silent 1 "planes" (behind s att h G) = none)
    {i : Runs.In} {K : ℕ} (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some (i, K))
    {gL : Forest.Heard} (hg : att.lookHeard = some gL) (hsh : gL.shape = A.fs) (hok : FoNums.ok gL.shape = true)
    (hBare : Bare gL.leaves.start)
    (hn : gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) ≤
      (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k * ((A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m / 2 ^ A.S.cf.lmb))
    (first ns : ℕ) (N : Nums) (Rds : ℕ → Readers) (hRd : Rds x.link = readersOfLink H L)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated) (Nn : Numbers) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (hfront : FrontAll x A D (Nn.sent x.link 0)
      (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
      (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi gL s)
    (hpub : TiePub D x A.seam.tl hi rad) (hhi : hi ≤ x.ns) {w : Wit Cells Tok MsgT}
    (hItem : ∀ p ∈ runs x.link 2 "planes", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 (behind s att h G) (seatTab D.codes arr ms w))
    (rP : (1, "planes") ∈ runs x.link 2 "planes")
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link → StatedAtt St A (funsAt A) s) :
    K3WorthPlanes (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard gL.shape A.S.cf.lmb
      first (fun w q => attNu x A.S A.seam.tl D rad seat arr w q) s w := by
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  obtain ⟨hz, _, hU⟩ := hfront.ledger att.F led
  obtain ⟨g₀, hg₀, _⟩ := hfront.reads att e
  have hfP := frontAll_rides hfront led hh (lay_of_parts e h5 hg₀ hu h G)
  obtain ⟨zG, bl⟩ := hear_below hh hz
  have zG' : PscRun.Sized G := ⟨zG.vp, zG.mf, zG.got⟩
  have lt : _root_.Fo.Later att.F G := by
    obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh hz
    exact ⟨bl.1, bl.ns, fun j hj => by
      obtain ⟨a, b, d⟩ := st j _ _ ⟨hj, rfl, rfl⟩
      exact ⟨a, b, d⟩⟩
  -- the item's own sentence: the reader answers
  have hI := hItem _ rP
  obtain ⟨a', R, ha', hR, _, hf⟩ := hI
  obtain rfl : partAt s att G none = a' := Option.some.inj ((segAt_behind (s := s) (a := att) (h := h) (G := G)).symm.trans ha')
  have hR' : (readersOfLink H L).forms 1 "planes" (behind s att h G) = some R := by rw [← hRd]; exact hR
  obtain ⟨run, cl, s', F, GP, C⟩ := link_cut (by decide) hsil hR'
  obtain ⟨nm', hfd⟩ := C.found
  obtain rfl : (guardC same (nm, VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) A.S.cf.lmb
      (readersOfO A))).2 = run := congrArg Prod.snd (Option.some.inj (hL.symm.trans hfd))
  obtain rfl : G = F := Option.some.inj ((show (behind s att h G).fork? = some G from rfl).symm.trans C.front)
  have hrun : VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) A.S.cf.lmb (readersOfO A) 0
      (behind s att h G) = .ok (cl, s') := guardC_inv same _ C.ran
  have hF' : (VerifiableInference.Desc.K3.seatCalls claim).fork (behind s att h G) = some G := rfl
  have hg' : (VerifiableInference.Desc.K3.seatCalls claim).heard (behind s att h G) = some gL := hg
  obtain ⟨GP', es, ltP⟩ := planes_laterFo (VerifiableInference.Desc.K3.seatCalls claim) A.S.cf.lmb (readersOfO A) hF' hg' zG' hrun
  obtain rfl : GP = GP' := by
    have e1 : s'.fork? = some GP' := by
      rw [es]
      exact First.S.fork_putFork (behind s att h G) G _ rfl
    exact Option.some.inj (C.behind.symm.trans e1)
  obtain ⟨r, hr⟩ : ∃ r, readersOfK (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some r := by
    unfold readersOfK
    rw [hin]
    exact ⟨_, rfl⟩
  obtain ⟨eg, _, hK, _, _, lk, _, _, _, ht⟩ := inOf_behind hin
  rw [← eg] at ht
  have hW : (parCOf A).nW ≤ K := by
    obtain ⟨T, hT, _, hw, _⟩ := hU
    have hT' : G.trees[(parCOf A).iU3]? = some T := by rw [bl.trees]; exact hT
    rw [hT'] at hK
    obtain rfl : T.K = K := Option.some.inj hK
    exact hw
  have Rr := readers_ret_plan hin hr (K5Law.len_in ht) hW (S := A.S) (tl := A.seam.tl) eg ht (eg ▸ hPos) hn
  obtain ⟨lid, cf, hs⟩ := ofPlan_shape hOP
  have hUG : U3At A (plannedK A) G := by
    obtain ⟨T, hT, a1, a2, a3⟩ := hU
    exact ⟨T, by rw [bl.trees]; exact hT, a1, a2, a3⟩
  refine K05_host_planes_door x A D rad Ex Wp α (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
    (·.form) (planes := VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls claim) A.S.cf.lmb (readersOfO A))
    (bit := bitOf (readersOfO A)) (pin := pinOf (readersOfO A))
    (k3PlanesPaid_of (planes_worth (VerifiableInference.Desc.K3.seatCalls claim) (·.form) (seatCalls_fits claim (·.form) hcl) A.S.cf.lmb
      (readersOfO A))) (behind s att h G) hPos hr
    (fun col hc => Option.isSome_iff_exists.2 (Rr.1 0 col hc)) (fun col hc => Option.isSome_iff_exists.2 (Rr.1 1 col hc))
    (fun col hc => Option.isSome_iff_exists.2 (Rr.2 col hc)) hs (ofPlan_matsFit hOP) hsh (ofPlan_rows hOP) ?_ ?_ first
    (F0 := att.F) (fork_front e) (by show s.lookHeard? = some gL; unfold First.S.lookHeard?; rw [e]; exact hg) cl GP GP hok
    ⟨hg', ⟨G, rfl, lt, zG'⟩, ⟨0, s', hrun, C.behind⟩⟩ (_root_.Fo.Later.refl _) ns N Rds runs St Nn arr seat ms hi rfl segAt_behind hfP hpub hhi
    hItem rP hR (fun y hy => by rw [C.forms]; exact List.mem_map.2 ⟨y, hy, rfl⟩) ?_ hmem hSt
    (hents_of_run A (VerifiableInference.Desc.K3.seatCalls claim) (·.form) hcl A.S.cf.lmb hg' hrun hBare rfl hUG)
  · funext e' col
    unfold bitOf
    have hr' : readersOfO A (behind s att h G) = some r := hr
    rw [hr']
    rfl
  · funext col
    unfold pinOf
    have hr' : readersOfO A (behind s att h G) = some r := hr
    rw [hr']
    rfl
  · rw [C.late]
    exact lateLaid_at (Nn.sent x.link 0) none (partAt s att G none) GP ltP _ fun f hf' => by
      have := (hf f (by rw [C.forms]; exact hf')).1
      rw [C.late] at this
      exact this

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.guardC_inv
#print axioms VerifiableInference.Desc.First.Att.P.planes_laterFo
#print axioms VerifiableInference.Desc.First.Att.P.lay_of_parts
#print axioms VerifiableInference.Desc.First.Att.P.worthPlanes_behind
