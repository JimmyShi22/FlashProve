-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what is left at a stand of the first chain's last test, built.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/LeftAtL.lean: LeftAtStand (ListPaid.lean) at each stand of
onAtRun_at_maker (ListAtMaker.lean): ok from the invariant's SaidOk, rowsSay from rowsSay_of_closing,
shape and fits from the record at every stand (ShapeAtStand.lean). So the clause of the rule at the filling's own list, with hleft replaced by
what the thread and the record owe.

  pass_of_five     frontFiveB says that nothing passes on entry
  firstPart_moves, rounds_to_first   the rounds of the first part of a job whose fresh table came earlier
  onAtRun_at_maker_thread   the statement

What stays. hH: the run's prover holds the maker's first list. hI: the rule's invariant at 354 gives
the thread's at a Said that holds SaidOk. hbs, hbeg: the thread's blocks and first state. hIM: the tie of
the witness's words to the sender's rows.

Limits. That the list named in the conclusion is a member of G.first at its place is the caller's to
say: hH speaks of halves, not of lists. wv must be the run's own ⟨w₀, rc, x, its trace⟩, and H' is tied
to G.prover H by hI alone: the thread speaks of one input. That T, hH, hbs, hbeg, hSaid, hI, hIM hold
together at any letters is not shown here.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). It calls
rowsSay_of_closing, which bears the label, and keeps its letters. This file's ground, premise by
premise, for onAtRun_at_maker_thread. The coins here: k and ρ (a run's), rc (the committer's). FIRST
KIND. T: the chief tied letter: its type is indexed by w₀, rc, x, k, R, and its fields read k, rc, R.
hI binds the coins itself and names none: it ties H', Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, wv
and Said to T; the tie to the coins runs through T's indices and through wv, which holds rc. Q falls
under the rule's «unless», as a letter for a value. hR, hrun: they say «= .ok», and fail where ready
or runC errs: what lifts them is hready at every k, and Owed's field runs, under ρ.due and
silentAt = none. hbeg reads k. hIM reads k, through the thread's witness, and the record. Ts stands
under hTs, an equation to a term of the run. hρ reads ρ and F alone: what it sets aside is public.
SECOND KIND: hR gives that w₀ is in range and that (w₀, x) has a trace: that the request can be served.
Ts and hIM read the hidden input through the record and the witness, and wv holds the index and its
trace. So a law in front of which this stands must name the relation. OF NEITHER KIND: h, hA, hf, hH
(no coin, no hidden input), hSaid (it binds the coins and holds whatever they are), hbs (no coin).
Made terms and lemmas that lift the bar: none: the bar is flat. So this statement may not be used on
the way to a law over coins as it stands; that the lemmas exist is not claimed. The label bars a
premise, never a theorem. What would lift it:
this statement
called in the order of the binders of RowDebtsP.threads: ∀ (w₀, rc, x) in the relation, ∀ k, ∀ return
of ready, ONE T, then ∀ due ρ outside the silent set, ∀ returned run: letters for values set to the
run's and the committer's own terms; letters for predicates (Said) shown at that made input at every
value of the coins; hI and hIM by lemmas under these binders; Q the term's own Script, so that the
thread narrows the inputs to no less than the image of the served relation: if it asks more, that
more stands in the law's text. What is set aside must be public, or lie inside the private stop set
that the law counts. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListAtMaker
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowsSayAtStand
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OkAtInside
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ShapeAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks viewWordsBelowPrime Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.Sh (testSh)
open P5J (CellsM TS)
open H2K.Member (codesFull)
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh

variable {W₀ : Type}

/-- frontFiveB says that nothing passes on entry. -/
theorem pass_of_five (p : VerifiableInference.Desc.K12.P12) (K : OnBytes.Codes) (t : T12)
    (h : frontFiveB p K (testSh t) = true) : t.pass = .nothing := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩ := h
  have h4' : (match ProofFile.Honest.Sh.passSh t.pass with
      | .nothing => true
      | _ => false) = true := h4
  cases hq : t.pass with
  | nothing => rfl
  | claim _ _ => rw [hq] at h4'; cases h4'
  | single _ _ => rw [hq] at h4'; cases h4'
  | switched _ _ _ => rw [hq] at h4'; cases h4'

/-- The rounds of the side's first part. -/
theorem rounds_to_first {V W X Pb Sx Cx : Type} (J : TestJob W X) (Js : SimJob Pb)
    (f : Addr × ℕ) (hf : J.fresh = some f) (σ : Side Sx Cx V W X Pb)
    (hr : σ.row = testPairs J Js) : σ.roundsTo 1 = firstLen J.p.nums.stages := by
  unfold Side.roundsTo
  rw [hr]
  obtain ⟨p, ms, fr, r, ro, tr⟩ := J
  obtain rfl : fr = some f := hf
  simp [testPairs, firstPart, movesFrom]

/-- **The clause of the rule at the filling's own list, from the thread and the record.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem onAtRun_at_maker_thread {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S' : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S' Op) = .ok A)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl)
    {Ky X₀ : Type} {H : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B W₀ IndexCommitterCoins Ky Cells X₀ Unit} {w₀ : W₀}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k ρ = .ok r)
    (hH : (G.prover H).first = A.H.first)
    (Tl : Local W₀ IndexCommitterCoins Inst Cells → Thread A.B S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells)
      (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd : Local W₀ IndexCommitterCoins Inst Cells → ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins Inst Cells) Unit → Prop)
    (bs : List (Block S ProofFile.Cl))
    (H' : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
    (wv : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hbs : (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.bs = cF.blocksInOrder)
    (hbeg : ∀ v : Local W₀ IndexCommitterCoins ProofFile.Inst Cells, v.x = x → ∀ y,
      (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.begun k v [] y →
      y = ProofFile.startS Zp x.pub)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ k s m E, T.I₁ 354 k s m E →
      ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354 k s m E)
    (Ts : T12)
    (hTs : Ts = stateAtFirstChainTest Zp x
      ((r.run.beforeAt (storedShown ((G.prover H).storedWords w₀ rc) r.run.storedAsked)
        ⟨(H2U.p12OfMade Zp.made).place, 1⟩).cut (firstLen (H2U.p12OfMade Zp.made).nums.stages)))
    (hIM : ∀ (Gp : Group), Ts.st.groups[Ts.g]? = some Gp →
      ∀ (st : S) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
        (J' : TestJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
      J' = atStand (jobOfLot I S' Zp A.G pl) m₀.st.input (frontOf m₀) Ts →
      ∀ c : RowCoins [(firstPart J' : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
          (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit), restPart J'],
      ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354 k st m₀ E₀ →
      enterFinish st = .ok Ts →
      lendRow A.B (A.B.rowsOf 0) (k.look 0) J'.p.place
        [(firstPart J' : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart J'] 0 = .ok c →
      ∀ Rr : Johnson.Prover.Send.Rows,
      carryRows (widerRows S' Zp A.G) (fillReaders I Zp)
          (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl m₀.st.input
          (heardL (frontOf m₀)) (restCoins J' c.2.1).mem = .ok Rr →
      WordsTied Ts.st Ts.g Gp
        (wordsFirst (P5J.At.arr Zp) st.st st.book
          ((lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.wit k
            m₀.st.input (m₀.st.heard ++ [])))
        (layoutOf Ts.st Gp) (plainL Rr (J'.first m₀.st.input (frontOf m₀) (restCoins J' c.2.1)))) :
    OnAtRun₁ T ρ r ((rowOfJob Zp (jobOfLot I S' Zp A.G pl)).lay Tl Sd bs) := by
  refine onAtRun_at_maker h I o S' Op hA hf T hρ hR hrun hH Tl Sd bs ?_
  intro m ca σ pre' t' hcut hσ hin hseen hc hca hm
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have eZ : Zp = A.Z := Except.ok.inj (O.pub.symm.trans hZ)
  have hG' : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by rw [eZ]; exact hG
  have eG : Bs.G₀ = A.G := Option.some.inj (O.blank.symm.trans hG')
  have hfZ : finishAt Zp A.G = some pl := by
    rw [← eG, finish_at_head h.toAtMg O, hf]
  have hfit := fits_at_head h.toAtMg hf
  have hp : (jobOfLot I S' Zp A.G pl : TestJob _ Unit).p = (fourOf Np).L :=
    numbersL_at_head h.toAtMg
  have hpl : σ.block.place = (H2U.p12OfMade Zp.made).place := Blind.testSide_place hσ
  have hplL : (H2U.p12OfMade Zp.made).place = placeL := proxPlace Zp
  obtain ⟨h354, -⟩ := front_public h.toAtMg O hf hcut (hpl.trans hplL)
  rw [h354] at hin
  replace hin : InsideOf .own A.B 0 (G.prover H).first σ.block
      (ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354) (σ.roundsTo 1)
      k m (envOf (H.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) := by
    obtain ⟨s, m₀, E₀, l, ds, y, a, rest⟩ := hin
    exact ⟨s, m₀, E₀, l, ds, y, hI _ _ _ _ a, rest⟩
  have hg' : ((G.prover H).first.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOfLot I S' Zp A.G pl : TestJob _ Unit)) := by
    rw [hH, hpl, hplL]
    have e := last_test_found I o S' Op hA pl (by rw [← eZ]; exact hfZ)
      (by rw [← eZ]; exact hfit)
    rw [← eZ] at e
    exact e
  have St := stands_of_cut h.toAtMg hR (jobOfLot I S' Zp A.G pl : TestJob _ Unit) hp rfl
    (simulatorJobOfLot Zp) (numbersL_at_head h.toAtMg) rfl [] σ hσ hg' pre' t' hcut
  have hrow : σ.row = testPairs (jobOfLot I S' Zp A.G pl : TestJob _ Unit) (simulatorJobOfLot Zp) := by
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    obtain ⟨b, -, e⟩ := Option.map_eq_some_iff.1 hσ'
    rw [← e]
  have hnn := rounds_to_first _ _ _ rfl σ hrow
  have hnb : σ.roundsTo 1 ≤ σ.block.rounds.length := by
    rw [hnn]
    have := St.le
    omega
  have hTs' := hTs
  rw [← hTs]
  have hok : viewWordsBelowPrime ⟨m.seen.take (pre'.flatMap (·.rounds)).length, []⟩ = true :=
    ok_of_inside (fun _ _ _ _ a => hSaid _ _ _ a.2) hin _
  obtain ⟨s₀, m₀, E₀, hTS, he⟩ := record_at_stand h hR (widerRows S' Zp A.G) (fillReaders I Zp)
    (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl _ rfl (simulatorJobOfLot Zp) [] σ
    hσ _ pre' t' _ St h354 hrun (by rw [hpl]; exact hc) m (by rw [hpl]; exact hm) H' Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp wv hbs hbeg (G.prover H).first Said _ hin hok Ts
    (by rw [hpl]; exact hTs')
  obtain ⟨hShape, hFit⟩ := tests_of_record h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv Said hf hTS he
  have hpass := pass_of_five _ _ _ hShape
  refine ⟨hok, hShape, fun Dp Sf => ?_, fun Rw hRw Gp hGp => ?_⟩
  · have e := atStand_here (jobOfLot I S' Zp A.G pl : TestJob _ Unit) m.st.input
      (restFront (jobOfLot I S' Zp A.G pl) m) Ts
    exact fits_of_shape (atStand (jobOfLot I S' Zp A.G pl : TestJob _ Unit) m.st.input
      (restFront (jobOfLot I S' Zp A.G pl) m) Ts) m.st.input
      (restFront (jobOfLot I S' Zp A.G pl) m) codesFull Dp pl (early_public h.toAtMg) Sf
      (by rw [e]; exact hpass) (by rw [e]; exact hFit)
  · exact rowsSay_of_closing h hR (widerRows S' Zp A.G) (fillReaders I Zp)
      (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl _ rfl (simulatorJobOfLot Zp) [] σ
      hσ _ pre' t' _ St h354 hrun (by rw [hpl]; exact hc) m (by rw [hpl]; exact hm) H' Q test carryX
      item n₁ n₂ b₀ Vd Rd Kp wv hbs hbeg (G.prover H).first Said _ hin hok Ts
      (by rw [hpl]; exact hTs') hg' rfl
      hnn hnb ca hca Rw hRw _ Gp hGp (hIM Gp hGp)

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.pass_of_five
#print axioms ProofFile.Honest.K12.Sim2.rounds_to_first
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_at_maker_thread
