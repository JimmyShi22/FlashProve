-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PlanesForward.lean: CONDITIONAL: the sentence of the table of the
verifier's blocks (the two files named here call it the table of joints) on the forms of the
lookup's run "planes" (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean) holds at the state BEHIND the lay
of an attention segment's own rounds, IF that table's item on the worth of the planes
(`K3WorthPlanes`, Johnson/Top/H/K3Worth.lean) holds at the state IN FRONT, at the same witness.

Why it can be had. The library goes the other way (`worthPlanes_behind`,
Johnson/Desc/First/Att/K05PlanesBack.lean: the sentence behind gives the item in front). Each joint
of that road is an equality:
  the values of the run's three claims ARE three written members (`planesAre_of_run`,
    Johnson/Top/H/K3OutParts.lean), under three equations on the caller's readers
    (`k5_host_planes_stated`, Johnson/Desc/First/Att/Claims/PlanesStated.lean);
  the item says that these three members are 0, at all rounds for which what was heard stands;
  a form has one value in the world of the ledger behind the run and in the sentence's own world
    (`value_eq`, Johnson/Desc/Sound/FormsQ.lean, under `WorldTie` and `LateLaid`,
    Johnson/Desc/First/Att/K05WorthAtTable.lean and K05WorthLate.lean beside it).
So the road is walked forward here. That what was heard stands for SOME rounds is a premise (hHI);
the library's `K3LeftOutIs` holds it. That the run returns, and the sentence's tests on the forms,
come from the public test `formsInT`.

Main names:
  `planes_zero_law`: the run's claims are worth 0 in the world of a later ledger. General in the
    seat, the ring and the readers.
  `value_late`: one value in the two worlds.
  `slots_of_in`: a form that passes the sentence's test names slots below the ledger's number.
  `formsPlanes_behind`: **the sentence behind the lay.**

Limits. Conditional on every premise in the statements; none is shown to be met here. The proof of
`formsPlanes_behind` follows that of `worthPlanes_behind` line by line as far as the two go
together.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05PlanesBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Road OnBytes.Road.Rows OnBytes.Params
open VerifiableInference.Desc (Wit Claim)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt? RunOf statesOfLink readersOfLink LinkHoles lateOf
  affInT formsInT slotIn)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated Mem seatTab msgsOf MsgT formsTQ worldOwn dataQ
  value_eq)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu K3RanAt K3WorthPlanes K3OutPlanes K3RunIsWorthAt
        link_cut planes_worth seatCalls_fits bitOf pinOf planesAre_of_run)
open K5Law (funsAt matsOf PosG OfPlan ofPlan_shape ofPlan_rows ofPlan_matsFit entryOf oldOf
  k5_host_planes_stated)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc

/-- **The run's claims are worth 0 in the world of a later ledger**, from the item on the planes'
worth. Conditional: hP: the run's claims' values are the three members at the caller's forms (the
library has it of `planesRun`: `planes_worth`); hO: the item; hI: what was heard stands for the
rounds rs; hok: a test on the shape; rP, lP: the run said yes at a later state, H is later than the
ledger that it leaves; b0, b1, pn: the caller's forms are worth the columns' combinations. -/
theorem planes_zero_law {S Cl K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard) (form : Cl → Aff) (lm : ℕ)
    (planes : ℕ → S → Except String (List Cl × S)) (bit : S → ℕ → ℕ → Aff) (pin : S → ℕ → Aff)
    (hP : K3RunIsWorthAt fork heard form lm planes
      (fun s _ _ g jLK rsK ν val =>
        [_root_.Fo.claimLeaves g.shape lm jLK rsK ν fun col => val (bit s 0 col),
          _root_.Fo.claimBits g.shape lm jLK rsK ν fun col => val (bit s 1 col),
          Pin.countK g.shape lm fun col => val (pin s col)]))
    (g : Forest.Heard) (F0 : Fork) (first : ℕ) (rs : TwV.Rounds K) (ν : _root_.Fo.Pl → K)
    (hO : K3OutPlanes g.shape lm first ν ρ g F0)
    (hI : _root_.Fo.HeardIs ρ g F0 (_root_.Fo.endsOf g.shape lm first rs))
    (hok : FoNums.ok g.shape = true) (sP : S) (clP : List Cl) (GP H : Fork)
    (rP : K3RanAt fork heard g F0 planes sP clP GP) (lP : _root_.Fo.Later GP H)
    (entry : ℕ → ℕ → ℕ → K)
    (b0 : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 0 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        _root_.Fo.colsK g.shape lm (_root_.Fo.rdL ρ g.zb0) ν col)
    (b1 : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 1 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        _root_.Fo.colsK g.shape lm (_root_.Fo.rdL ρ g.zb1) ν col)
    (pn : ∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (pin sP col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = Pin.pinColK lm ν col) :
    ∀ c ∈ clP, (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0 := by
  have hA := planesAre_of_run ρ fork heard form lm planes bit pin hP g F0 first rs hI hok sP clP GP
    H rP lP ν entry (by rw [← hI.zb0]; exact b0) (by rw [← hI.zb1]; exact b1) pn
  obtain ⟨z1, z2, z3⟩ := hO rs hI
  intro c hc
  have hm : (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) ∈
      clP.map (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) :=
    List.mem_map.2 ⟨c, hc, rfl⟩
  rw [hA] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e
  · rw [e]; exact z1
  · rw [e]; exact z2
  · rw [e]; exact z3

/-- **One value in the two worlds**: the sentence's own, and that of a ledger H under whose slots
the sentence's hidden values lie. -/
theorem value_late {St : Stated} {own : List (ℕ × ℕ)} {s : First.S} {a : K9.Part}
    {rd : ℕ × ℕ → MsgQ} {late : List (ℕ × E × E)} {H : Fork} {mask : ℕ → GQ}
    {entry : ℕ → ℕ → ℕ → GQ} {fs : List Aff} (hl : LateLaid a.F late H fs)
    (T : WorldTie St own s a rd mask entry fs) {f : Aff} (hm : f ∈ fs) :
    f.value Reading.gl (H.worldOf Reading.gl mask entry) =
      f.value Reading.gl (worldOwn a late (St.at1 s (dataQ own a rd))) := by
  refine value_eq _ _ f (fun y hy => (T.entry f hm y hy).symm) (fun y hy => ?_)
  show Reading.gl.val (H.vp.getD y.1 zeroE) - Reading.gl.val (H.mf.getD y.1 zeroE) * mask y.1 = _
  rw [← T.mask f hm y hy]
  exact (hl f hm y hy _).symm

/-- A form that passes the sentence's test names slots below the ledger's number of slots. -/
theorem slots_of_in {own : List (ℕ × ℕ)} {free : Option ℕ} {late : List (ℕ × E × E)}
    {pt : K9.Part} {f : Aff} (h1 : affInT own free late pt f = true) :
    ∀ y ∈ f.slots.toList, y.1 < pt.F.ns := by
  intro y hy
  unfold affInT at h1
  obtain ⟨_, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h1
  have h3 := List.all_eq_true.1 h2 y hy
  unfold slotIn at h3
  obtain ⟨h4, _⟩ := Eq.mp (Bool.and_eq_true _ _) h3
  exact of_decide_eq_true h4

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat)

/-- **The sentence on the forms of the run "planes", behind the lay, from the item on the planes'
worth in front.** Conditional. The premises are those of the library's `worthPlanes_behind`, but
that in the place of the sentence behind stand:
  hIn: the public test tied to the sentence accepts behind the lay;
  hWorth: the item on the planes' worth holds in front, at the witness w;
  hHI: what the lookup left stands for some rounds, at the ledger in front.
Ex, Wp, al, ns, N: free letters of the library's law on the two worlds. -/
theorem formsPlanes_behind (Ex : Iop.ExtSpec) (Wp : Type)
    (al : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)
    (hOP : OfPlan A) (hPos : PosG (parCOf A).geo) (H : LinkHoles) (L : Link First.S Claim)
    {same : First.S → First.S → Bool} (claim : Aff → Claim) (hcl : ∀ f, (claim f).form = f)
    {nm : String}
    (hL : ((statesOfLink L 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claim) A.S.cf.lmb (readersOfO A))))
    {s : First.S} {att : First.AttOwn} {xr : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
    {G : Fork} (e : s.here = .att att) (hu : s.failed = none) (h5 : att.heard5 = none)
    (hh : hear xr (att.F, rs, 0) = some (h, G, [], 0))
    (hsil : H.silent 1 "planes" (behind s att h G) = none) {i : Runs.In} {K : ℕ}
    (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some (i, K))
    {gL : Forest.Heard} (hg : att.lookHeard = some gL) (hsh : gL.shape = A.fs)
    (hok : FoNums.ok gL.shape = true) (hBare : Bare gL.leaves.start)
    (hn : gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) ≤
      (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k *
        ((A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m / 2 ^ A.S.cf.lmb))
    (first ns : ℕ) (N : Nums) (Rd : Readers) (hRd : Rd = readersOfLink H L) (St : Stated)
    (Nn : Numbers) (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (ms : List Mem) (hi : ℕ)
    (hfront : FrontAll x A D (Nn.sent x.link 0)
      (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
      (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi gL s)
    (hpub : TiePub D x A.seam.tl hi rad) (hhi : hi ≤ x.ns) {w : Wit Cells Tok MsgT}
    (hIn : formsInT Rd (Nn.sent x.link 0) 1 "planes" (behind s att h G) = true)
    (hWorth : K3WorthPlanes (K3.seatCalls claim).fork (K3.seatCalls claim).heard gL.shape
      A.S.cf.lmb first (fun w q => attNu x A.S A.seam.tl D rad seat arr w q) s w)
    {rsK : TwV.Rounds Cb.Gl.E}
    (hHI : _root_.Fo.HeardIs Reading.gl gL att.F (_root_.Fo.endsOf gL.shape A.S.cf.lmb first rsK))
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s) :
    formsTQ Rd St (Nn.sent x.link 0) 1 "planes" (behind s att h G) (seatTab D.codes arr ms w) := by
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
  -- the public test: the reader answers, and its forms pass the sentence's tests
  unfold formsInT at hIn
  rw [segAt_behind (s := s) (a := att) (h := h) (G := G)] at hIn
  cases hR : Rd.forms 1 "planes" (behind s att h G) with
  | none =>
    rw [hR] at hIn
    cases hIn
  | some R =>
  rw [hR] at hIn
  obtain ⟨hlo, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hIn
  have hf := List.all_eq_true.1 hall
  have hR' : (readersOfLink H L).forms 1 "planes" (behind s att h G) = some R := by
    rw [← hRd]; exact hR
  obtain ⟨run, cl, s', F, GP, C⟩ := link_cut (by decide) hsil hR'
  obtain ⟨nm', hfd⟩ := C.found
  obtain rfl : (guardC same (nm, K3.planesRun (K3.seatCalls claim) A.S.cf.lmb
      (readersOfO A))).2 = run := congrArg Prod.snd (Option.some.inj (hL.symm.trans hfd))
  obtain rfl : G = F :=
    Option.some.inj ((show (behind s att h G).fork? = some G from rfl).symm.trans C.front)
  have hrun : K3.planesRun (K3.seatCalls claim) A.S.cf.lmb (readersOfO A) 0
      (behind s att h G) = .ok (cl, s') := guardC_inv same _ C.ran
  have hF' : (K3.seatCalls claim).fork (behind s att h G) = some G := rfl
  have hg' : (K3.seatCalls claim).heard (behind s att h G) = some gL := hg
  obtain ⟨GP', es, ltP⟩ :=
    planes_laterFo (K3.seatCalls claim) A.S.cf.lmb (readersOfO A) hF' hg' zG' hrun
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
  have Rr := readers_ret_plan hin hr (K5Law.len_in ht) hW (S := A.S) (tl := A.seam.tl) eg ht
    (eg ▸ hPos) hn
  obtain ⟨lid, cf, hs⟩ := ofPlan_shape hOP
  have hUG : U3At A (plannedK A) G := by
    obtain ⟨T, hT, a1, a2, a3⟩ := hU
    exact ⟨T, by rw [bl.trees]; exact hT, a1, a2, a3⟩
  obtain rfl : K = plannedK A :=
    width_of_inOf A (a₀ := { att with F := G, heard5 := some h }) rfl hUG hin
  have hr' : readersOfO A (behind s att h G) = some r := hr
  have hbit : bitOf (readersOfO A) (behind s att h G) =
      fun e' col => (r.1 e' col).getD (Aff.ofConst zeroE) := by
    funext e' col
    unfold bitOf
    rw [hr']
    rfl
  have hpin : pinOf (readersOfO A) (behind s att h G) =
      fun col => (r.2 col).getD (Aff.ofConst zeroE) := by
    funext col
    unfold pinOf
    rw [hr']
    rfl
  -- the facts in front, carried behind the lay
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  obtain ⟨Lc, T⟩ := hfP.facts
  obtain ⟨_, hnsF, _⟩ := hfP.ledger G rfl
  obtain ⟨g1, hg1, hrd⟩ := hfP.reads { att with F := G, heard5 := some h } rfl
  have eL : att.L = Lc := Option.some.inj T.hL
  have hfl : att.L.check.frame.link = x.link := by
    rw [eL]
    exact (liveReqB_at T.hB1 T.hL).1.trans T.hlink
  have hents := hents_of_run A (K3.seatCalls claim) (·.form) hcl A.S.cf.lmb hg' hrun hBare
    (a₀ := { att with F := G, heard5 := some h }) rfl hUG
  have TF := tieFacts_here (rad := rad) (hi := hi) p3 p1
    (fun k hk => (hcov_of D rad x A.seam.tl seat [] k hk).2) T
    (segAt_behind (s := s) (a := att) (h := h) (G := G)) hnsF (hfP.sec Lc T.hL) hents
  -- the host's three equations, and so the claims' worth in the world of the ledger behind the run
  obtain ⟨i', K', hi', Hh⟩ := k5_host_planes_stated (tl := A.seam.tl) (S := A.S) (gL := gL)
    (seatCO (parCOf A)) (parCOf A) (behind s att h G) rfl rfl hPos hr
    (hlook_of_reads A (a₀ := { att with F := G, heard5 := some h }) rfl hg1 hrd)
    (fun col hc => Option.isSome_iff_exists.2 (Rr.1 0 col hc))
    (fun col hc => Option.isSome_iff_exists.2 (Rr.1 1 col hc))
    (fun col hc => Option.isSome_iff_exists.2 (Rr.2 col hc)) hs (ofPlan_matsFit hOP) hsh
    (ofPlan_rows hOP)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hi'.symm.trans hin))
  have HH := Hh (matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w)) GP
    (fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
    (attNu x A.S A.seam.tl D rad seat arr w)
    (fun r _ c _ => cells_are_nu x A D rad seat arr w r c)
  have hlkS : (K3.seatCalls claim).heard s = some gL := by
    show s.lookHeard? = some gL
    unfold First.S.lookHeard?
    rw [e]
    exact hg
  have Z := planes_zero_law Reading.gl (K3.seatCalls claim).fork (K3.seatCalls claim).heard
    (·.form) A.S.cf.lmb (K3.planesRun (K3.seatCalls claim) A.S.cf.lmb (readersOfO A))
    (bitOf (readersOfO A)) (pinOf (readersOfO A))
    (planes_worth (K3.seatCalls claim) (·.form) (seatCalls_fits claim (·.form) hcl) A.S.cf.lmb
      (readersOfO A)) gL att.F first rsK (attNu x A.S A.seam.tl D rad seat arr w)
    (hWorth gL att.F (fork_front e) hlkS) hHI hok (behind s att h G) cl GP GP
    ⟨hg', ⟨G, rfl, lt, zG'⟩, ⟨0, s', hrun, C.behind⟩⟩ (_root_.Fo.Later.refl _)
    (entryOf Reading.gl A.seam.tl (plannedK A)
      (matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w)) (oldOf A.S gL i').t.funs.toList)
    (by rw [hbit]; exact HH.bit0) (by rw [hbit]; exact HH.bit1) (by rw [hpin]; exact HH.pin)
  -- the two worlds
  have hfc : ∀ f ∈ cl.map (·.form),
      affInT (Nn.sent x.link 0) none (lateOf G GP) (partAt s att G none) f = true := by
    intro f hf'
    have := hf f (by rw [C.forms]; exact hf')
    rw [C.late] at this
    exact this
  have hslots : ∀ f ∈ cl.map (·.form), ∀ y ∈ f.slots.toList, y.1 < (partAt s att G none).F.ns :=
    fun f hf' => slots_of_in (hfc f hf')
  have Wt := worldTie_at x A D rad Ex Wp al ns N St (Nn.sent x.link 0) arr seat ms w
    (cl.map (·.form)) hi _ _ (funsAt A) _ p1 p2 p4 (hmem _) (hcov_of D rad x A.seam.tl seat _)
    (hcovM_of D rad x A.seam.tl) (hSt _ { att with F := G, heard5 := some h } rfl hfl) TF hslots
    (funsAt_of_inOf A hin gL)
  have Wt' := Wt.mask_to (mask' := fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
    fun f hf' y hy => mask_is_nu x A.S A.seam.tl D rad seat arr Ex Wp al ns N w y.1
      (Nat.lt_of_lt_of_le (hslots f hf' y hy) (Nat.le_trans TF.hns hhi))
  have hlate : LateLaid (partAt s att G none).F R.late GP (cl.map (·.form)) := by
    rw [C.late]
    exact lateLaid_at (Nn.sent x.link 0) none (partAt s att G none) GP ltP _ hfc
  refine ⟨partAt s att G none, R, segAt_behind, hR, hlo, fun f hfR => ⟨hf f hfR, ?_⟩⟩
  have hfm : f ∈ cl.map (·.form) := by rw [← C.forms]; exact hfR
  rw [← value_late hlate Wt' hfm]
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hfm
  exact Z c hc

end

end H2K5.Honest

#print axioms H2K5.Honest.planes_zero_law
#print axioms H2K5.Honest.value_late
#print axioms H2K5.Honest.slots_of_in
#print axioms H2K5.Honest.formsPlanes_behind
