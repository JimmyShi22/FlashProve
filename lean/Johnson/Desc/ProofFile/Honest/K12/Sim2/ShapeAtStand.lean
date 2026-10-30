-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two tests on the shape at a stand of the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ShapeAtStand.lean: at a stand inside the thread, the state that
stands in is the record that enterFinish returns at the thread's own state (record_at_stand, the first
half of rowsSay_at_run's proof). So closingRecordLaid_at_every_stand
(K12/AtFile/LotLShapeHeadTop.lean) reaches it, and frontFiveB and fitsShapeB say yes there: the second
by one more closed line at the written local shape, whatever stands in front.

  closingShape_passes_fits   the closed line
  fits_of_closingRecordLaid  fitsShapeB at a record that bears the written local shape
  record_at_stand            the state that stands in is a record of the thread
  tests_of_record            the two tests at a record of the thread

Limits. Full size.
No property of the protocol is claimed.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head):
record_at_stand and tests_of_record. record_at_stand keeps the ground of rowsSay_at_run
(RowsSayAtStand.lean's head). tests_of_record: FIRST KIND: hTS reads k, through ThrS: under it stand
H', Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, wv, Said, s, m₀, E₀. T stands under he, which says
«= .ok» of a state of that stand. SECOND KIND: wv holds the index and its trace, and what hTS narrows
the inputs to must be named by the law. OF NEITHER KIND: h, hp. The two tests themselves read only the
shape, and the closed line closingShape_passes_fits and fits_of_closingRecordLaid bear no label: their
premises read no coin. The label bars a premise, never a theorem.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowsSayAtStand
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FitsShapeL
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeHeadTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks viewWordsBelowPrime Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12.LotL
open ProofFile.Honest.Sh (testSh)
open VerifiableInference.Desc.Ground.Sh (CoreSh OrcSh GrpSh TreeSh SrcSh)
open P5J (CellsM TS)
open H2K.Member (piLFull codesFull)

/-- **The test says yes at the written finish**, whatever stands in front. -/
theorem closingShape_passes_fits (frontMessages : ℕ → OrcSh) (frontGroups : ℕ → GrpSh)
    (frontTrees : ℕ → TreeSh) (frontPlaces : ℕ → ℕ × ℕ)
    (carrierLedger maskLedger : Option OnBytes.Ledger) (carrierSpent : Bool)
    (maskRows : ℕ) (maskPad : List (OnBytes.Part × ℕ)) (maskGroups : List ℕ) (source : SrcSh) :
    (finishW.any fun p => fitsShapeB piLFull p
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing,
        some 186⟩) = true := by
  kernel_rfl

/-- **fitsShapeB at a record that bears the written local shape.** -/
theorem fits_of_closingRecordLaid {R : T12} (h : ClosingRecordLaid R) {p : K2.SwitchPlace}
    (hp : finishW = some p) : fitsShapeB piLFull p (testSh R) = true := by
  obtain ⟨hg, hn, hm, hc, hr, carrierLedger, maskLedger, carrierSpent, maskRows, maskPad, maskGroups,
    source, hl⟩ := h
  show fitsShapeB piLFull p
    ⟨VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩, R.g,
      ProofFile.Honest.Sh.passSh R.pass, R.mask⟩ = true
  rw [hg, hn, hm]
  have e := core_is_localCore hl
  rw [show (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).st.codes = codesFull
    from hc, show (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).roots = 77
    from hr] at e
  have t := closingShape_passes_fits
    (fun i => (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).st.oracles.getD i
      (carrierMessage carrierLedger carrierSpent))
    (fun i => (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).st.groups.getD i
      closingGroup)
    (fun i => (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).book.trees.getD i
      (closingTree source))
    (fun i => (VerifiableInference.Desc.Ground.Sh.coreSh ⟨R.st, R.book, R.roots⟩).book.place.getD i
      (0, 0)) carrierLedger maskLedger carrierSpent maskRows maskPad maskGroups source
  rw [← e, hp] at t
  exact t

variable {W₀ Rc Tr : Type}

/-- **The state that stands in is a record of the thread**: the first half of rowsSay_at_run's proof.
NOT IN FRONT OF A LAW OVER COINS (the rule, and the ground of rowsSay_at_run: RowsSayAtStand.lean's
head). -/
theorem record_at_stand {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Ky' X₀' Y' Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky' Tr X₀' Y'} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky' Tr X₀' Y'}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (pl : K2.SwitchPlace) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y')
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob Pb) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y' Pb)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (u : Member (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y' Pb)
    (pre t : List (Block S ProofFile.Cl)) (i : ℕ) (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hlen : pre.length = 354)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y')
    (hm : midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
      .ok (some m))
    (H' : Prover W₀ Rc ProofFile.Inst Ky' Tr X₀' Y')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
    (wv : Local W₀ Rc ProofFile.Inst Tr)
    (hbs : (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.bs = cF.blocksInOrder)
    (hbeg : ∀ v : Local W₀ Rc ProofFile.Inst Tr, v.x = x → ∀ y,
      (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.begun k v [] y →
      y = ProofFile.startS Zp x.pub)
    (hs' : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y'))
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) Y' → Prop) (n' : ℕ)
    (hin : InsideOf .own Bk 0 hs' σ.block
      (ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354)
      n' k m (envOf (P.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.1.take ((pre.flatMap (·.rounds)).length + n'))))
    (hok : viewWordsBelowPrime ⟨m.seen.take (pre.flatMap (·.rounds)).length, []⟩ = true)
    (T : T12)
    (hTs : T = stateAtFirstChainTest Zp x
      ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i)) :
    ∃ (s : S) (m₀ : Mid (Local W₀ Rc ProofFile.Inst Tr) Y') (E₀ : Env),
      ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354 k s m₀ E₀ ∧
      enterFinish s = .ok T := by
  obtain ⟨m', T', a1, -, -, hx, ⟨s', cs, hT', hf, hfill⟩, e⟩ := door_at_firstChainTest h.toAtMg hR σ u
    pre t i St hrun hc D readers closing pl Js fs (hJ ▸ hσ)
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (a1.symm.trans hm))
  have hr := reach_of_stand (Zp := Zp) St.cut x.pub hok (storedWords_lt P w₀ rc) hf hfill
  rw [hlen] at hr
  have he : enterFinish s' = .ok T := by
    rw [hTs, e]
    exact hT'
  obtain ⟨s, m₀, E₀, l, ds, y, ⟨hThr, hSd⟩, hl, hd, hp, em, hE⟩ := hin
  have hmid := play_mid _ _ _ _ _ hp
  have hThr' := hThr
  unfold Thr at hThr'
  obtain ⟨-, hFit, -, -, hMade, -, -⟩ := hThr'
  have hcut : (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.bs =
      pre ++ σ.block :: t := hbs.trans St.cut
  have hN : m₀.seen.length = (pre.flatMap (·.rounds)).length := by
    have e1 := hMade.1
    have l1 := congrArg List.length e1
    rw [List.length_map] at l1
    rw [l1]
    have l2 := drawsFit_length _ _ hFit
    refine l2.trans ?_
    show (declsTo _ 354).length = _
    unfold declsTo
    rw [hcut, ← hlen, List.take_left' rfl]
  have hseen : m'.seen.take (pre.flatMap (·.rounds)).length = m₀.seen := by
    rw [em, hmid.2.2, ← hN]
    simp
  rw [hseen] at hf hfill
  have hx₀ : m₀.st.input.x = x := by
    rw [← hx, em, hmid.1]
  have hadd : E₀.add y.1 = envOf (P.storedWords w₀ rc) (fun _ _ => none)
      (r.run.played.1.take (pre.flatMap (·.rounds)).length ++
        (r.run.played.1.take ((pre.flatMap (·.rounds)).length + n')).drop
          (pre.flatMap (·.rounds)).length) := by
    rw [← hE]
    congr 1
    have : r.run.played.1.take (pre.flatMap (·.rounds)).length =
        (r.run.played.1.take ((pre.flatMap (·.rounds)).length + n')).take
          (pre.flatMap (·.rounds)).length := by
      rw [List.take_take]
      congr 1
      omega
    rw [this, List.take_append_drop]
  have hs₀ := tables_in_front h.toAtMg.laid.planOk hR hrun St.cut
  have est : s = s' := state_of_thread _ hcut rfl rfl rfl (hlen ▸ hMade) hadd
    (hs₀.trans (by rw [hbs]; rfl))
    (fun y' hy' => hbeg _ hx₀ y' hy') hf hfill
  exact ⟨s, m₀, E₀, ⟨hThr, hSd⟩, by rw [est]; exact he⟩

/-- **The two tests at a record of the thread**: the head and the stand hTS.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem tests_of_record {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Ky' X₀' Y' : Type} {Bk : ProverCoinCounts}
    (H' : Prover W₀ Rc ProofFile.Inst Ky' Tr X₀' Y')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
    (wv : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) Y' → Prop)
    {pl : K2.SwitchPlace} (hp : finishW = some pl) {k : Coins Bk} {s : S}
    {m₀ : Mid (Local W₀ Rc ProofFile.Inst Tr) Y'} {E₀ : Env} {T : T12}
    (hTS : ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354 k s m₀ E₀)
    (he : enterFinish s = .ok T) :
    frontFiveB (H2U.p12OfMade Zp.made) codesFull (testSh T) = true ∧
      fitsShapeB (H2U.p12OfMade Zp.made) pl (testSh T) = true := by
  have hl := closingRecordLaid_at_every_stand h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv Said k s m₀
    E₀ T hTS he
  rw [Johnson.AtFull.Shape.p12_at_head h.toAtMg]
  exact ⟨firstShapeTest_of_closingRecordLaid hl, fits_of_closingRecordLaid hl hp⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.closingShape_passes_fits
#print axioms ProofFile.Honest.K12.Sim2.fits_of_closingRecordLaid
#print axioms ProofFile.Honest.K12.Sim2.record_at_stand
#print axioms ProofFile.Honest.K12.Sim2.tests_of_record
