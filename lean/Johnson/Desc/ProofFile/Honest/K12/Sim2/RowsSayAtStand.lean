-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause on values at a run, from the thread and the tie of the words.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsSayAtStand.lean: the field rowsSay of LeftAtStand
(ListPaid.lean), at the state that stands in, from says_head_L (AtFile/ClosingSaysAt.lean): the
thread's state at border 354 is the run's own (state_of_thread, RecordOfThread.lean), so the thread's
stand and the run's record are one.

  tables_in_front   the tables of the rounds in front of a block are the block's trees in front
  tied_of_entry     the tie at the part's entry from the tie at the block's
  lend_of_eq        equal parts lend the same
  rowsSay_at_run    the statement, at a tie at the thread's stand
  rowsSay_of_closing   at a tie in the form of wordsTied_at_closing_stand (K12/AtFile/LotLScriptStand.lean)

What stays. hin: the stand lies inside ThrS of lettersHead's thread: so the rule's invariant T.I₁ 354
must be that thread's. hbs, hbeg: the
thread's blocks and first state. hok: paid from SaidOk by ok_of_inside. hw, or hIM: the tie of the
witness's words to the sender's rows: the clause on values. No property of the protocol is claimed.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). It calls
says_head_L, which bears the label, and keeps its letters. This file's ground, for rowsSay_at_run and
rowsSay_of_closing, premise by premise. The coins here: k and ρ (a run's), rc (the committer's). FIRST
KIND. hin: it reads k, through ThrS: under it stand H', Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp,
wv, Said, hs': Q too falls under the rule's «unless», as a letter for a value: the made Script, hin
shown at every value of the coins. hw, hIM: they read k, through the thread's witness: under them
stand Rr, G and what hin holds. hok: it reads the run's rounds. hR, hrun: = .ok fails where ready or
runC errs: lifted by ready at every k and by the run's returning under ρ's due test and no silent
stop. hbeg: it reads k. Letters under an equation to a term of the coins that is no Except, the term
being in the premise: T (hTs). Under one that is: m (hm), ca (hca), Rw (hRw), as hR. Pb' is tied by
nothing: WordsTied does not read that place of plainL. SECOND KIND: hR gives that the index is in
range and has a trace: the request can be served: hin, hw, hIM read the hidden input through the
witness, and wv holds the index and its trace: a law in front of which these stand names the
relation. Of neither kind: h, hbs (no coin, no hidden input); hρ is absent here. Made terms and lemmas that lift the bar: none: the bar is flat. So these two may
not be used on the way to a law over coins as they stand; that the lemmas exist is not claimed.
What would lift it: these two called under the binders of
RowDebtsP.threads, in the row's own order: for all (w₀, rc, x) in the relation, all k, every return,
one T; then for every due ρ outside the silent set, every run: letters for values set to the run's and
the committer's own terms; letters for predicates (Said, hs') shown at that made input at every value
of the coins; hin and hw or hIM by lemmas under these binders; Q the term's own Script, so that hin narrows the inputs to no
less than the image of the served relation: if it asks more, that more stands in the law's text. What
is set aside must be public, or lie inside the private stop set that the law counts. The label bars a
premise, never a theorem.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.AsksAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RecordOfThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingSaysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks viewWordsBelowPrime Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12.Light
open P5J (CellsM TS)
open Johnson.Prover.Link (PS)
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh

variable {W₀ Rc Tr Xi Ky X₀ Y : Type}

/-- **The tables in front of a block.** -/
theorem tables_in_front {F : FileDescription Xi} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F}
    (hpl : F.planOk = true) (hR : ready F Bk P w₀ rc x k = .ok R)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r) {pre t : List (Block F.S₁ F.Cl)}
    {blk : Block F.S₁ F.Cl} (hcut : F.first.blocksInOrder = pre ++ blk :: t) :
    (tablesOf (r.run.played.1.take (pre.flatMap (·.rounds)).length)).length =
      treesTo F.first.blocksInOrder pre.length := by
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  have e2 : (R.first.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
      ((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
    rw [← steps_pairs s1, ← List.map_take, List.map_map]
    rfl
  have hsh : ∀ y ∈ pre, y.oracles.length = y.rounds.length := fun y hy => by
    have h1 := planOk_shaped_first hpl y (by rw [hcut]; simp [hy])
    unfold Block.shaped at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.1
  have hc' := rows_count pre hsh (blk :: t)
  rw [← hcut] at hc'
  have ht : treesTo F.first.blocksInOrder pre.length =
      (pre.flatMap fun y => y.oracles.flatMap id).length := by
    unfold treesTo
    rw [hcut, List.take_left' rfl]
  have ha : ∀ l : List Played, (tablesOf l).length = (l.map (·.tables.length)).sum := by
    intro l
    unfold tablesOf
    rw [List.length_flatMap]
    simp
  rw [ha, ht, ← hc', ← e2, List.map_take, laidAs_tables lS, List.map_take]

/-- **The tie at the part's entry from the tie at the block's**: WordsTied reads the plain rows' main
and mask rows alone, so the fresh table's place in plainL is not read. -/
theorem tied_of_entry {Y' Pb : Type} {Bk : ProverCoinCounts} {k : Coins Bk}
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y') (Js : SimJob Pb) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (c : RowCoins [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y'),
      restPart J])
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) J.p.place
      [(firstPart J : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y'), restPart J] 0 =
        .ok c)
    (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries)
    (hca : carriedAt Bk k 0 ⟨J.p.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part =
      .ok ca)
    (w w' : Local W₀ Rc ProofFile.Inst Tr) (he₁ : w = w') (h₁ h₂ : List Fmt.Drawn) (he₂ : h₁ = h₂)
    (Rw : Johnson.Prover.Send.Rows)
    (hRw : carryRows D readers closing pl w h₁ (carriedCoins J (stretches _ ca)).mem = .ok Rw)
    (Sx : Statement) (g : ℕ) (G : Group) (Wd : Words GE) (Ly : GroupLayout) (Pa Pb' : PS)
    (hIM : ∀ Rr, carryRows D readers closing pl w' h₂ (stretches _ c.2.1.2.2) = .ok Rr →
      WordsTied Sx g G Wd Ly (plainL Rr Pa)) :
    WordsTied Sx g G Wd Ly (plainL Rw Pb') := by
  have h1 := (lendRow_cons_ok (lendRow_cons_ok hl).2).1
  have e : ca = c.2.1.2.2 := by
    unfold carriedAt at hca
    have h1' : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨J.p.place, 1⟩
        (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part = .ok c.2.1 := h1
    rw [h1'] at hca
    exact (Except.ok.inj hca).symm
  subst e
  subst he₁
  subst he₂
  exact hIM Rw hRw

/-- **The clause on values at a run**, at the state that stands in.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem rowsSay_at_run {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
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
        ⟨σ.block.place, u.number⟩).cut i))
    (Rr : PlainRows) (G : Group) (hG : T.st.groups[T.g]? = some G)
    (hw : ∀ (s : S) (m₀ : Mid (Local W₀ Rc ProofFile.Inst Tr) Y') (E₀ : Env)
      (l : List (Step (Local W₀ Rc ProofFile.Inst Tr) Y')) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) Y'),
      ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354
        k s m₀ E₀ → enterFinish s = .ok T → play (l.take n') ds [] m₀ = .ok y → m = y.2 →
      drawsFit (σ.block.rounds.take n') ds = true →
      m.seen.take (pre.flatMap (·.rounds)).length = m₀.seen →
      WordsTied T.st T.g G
        (wordsFirst (P5J.At.arr Zp) s.st s.book
          ((lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.wit k
            m₀.st.input (m₀.st.heard ++ [])))
        (layoutOf T.st G) Rr) :
    AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
      (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G) Rr) := by
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
  subst est
  exact says_head_L h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv hThr hr he Rr hG
    (hw s m₀ E₀ l ds y ⟨hThr, hSd⟩ he hp em hd hseen)

/-- Equal parts lend the same. -/
theorem lend_of_eq {V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : VerifiableInference.Desc.Place} {p q p' q' : Part V W X}
    (e₁ : p = p') (e₂ : q = q') {c : RowCoins [p, q]} (hl : lendRow B rows look a [p, q] 0 = .ok c) :
    ∃ c' : RowCoins [p', q'], lendRow B rows look a [p', q'] 0 = .ok c' ∧
      stretches q'.carries c'.2.1.2.2 = stretches q.carries c.2.1.2.2 := by
  subst e₁
  subst e₂
  exact ⟨c, hl, rfl⟩

/-- **The clause on values at a run, from the tie at the block's entry**, at the part's own rows.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem rowsSay_of_closing {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
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
        ⟨σ.block.place, u.number⟩).cut i))
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hu : u = restMember J Js) (hnn : n' = firstLen J.p.nums.stages)
    (hnb : n' ≤ σ.block.rounds.length)
    (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries)
    (hca : carriedAt Bk k 0 ⟨J.p.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part =
      .ok ca)
    (Rw : Johnson.Prover.Send.Rows)
    (hRw : carryRows D readers closing pl m.st.input (heardL (restFront J m))
      (carriedCoins J (stretches _ ca)).mem = .ok Rw) (Pb' : PS) (G : Group)
    (hG : T.st.groups[T.g]? = some G)
    (hIM : ∀ (st : S) (m₀ : Mid (Local W₀ Rc ProofFile.Inst Tr) Y') (E₀ : Env)
      (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y'), J' = atStand J m₀.st.input (frontOf m₀) T →
      ∀ c : RowCoins [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y'),
        restPart J'],
      ThrS (lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread Said 354 k st m₀ E₀ →
      enterFinish st = .ok T →
      lendRow Bk (Bk.rowsOf 0) (k.look 0) J'.p.place
        [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y'), restPart J']
        0 = .ok c →
      ∀ Rr : Johnson.Prover.Send.Rows,
      carryRows D readers closing pl m₀.st.input (heardL (frontOf m₀)) (restCoins J' c.2.1).mem =
        .ok Rr →
      WordsTied T.st T.g G
        (wordsFirst (P5J.At.arr Zp) st.st st.book
          ((lettersHead h H' Q test carryX item n₁ n₂ b₀ Vd Rd Kp wv).thread.wit k
            m₀.st.input (m₀.st.heard ++ [])))
        (layoutOf T.st G) (plainL Rr (J'.first m₀.st.input (frontOf m₀) (restCoins J' c.2.1)))) :
    AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
      (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G) (plainL Rw Pb')) := by
  subst hJ
  obtain ⟨m', T', a1, -, ag, -, -, eT⟩ := door_at_firstChainTest h.toAtMg hR σ u pre t i St hrun hc D
    readers closing pl Js fs hσ
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (a1.symm.trans hm))
  obtain rfl : T' = T := by rw [hTs, eT]
  have hpl : σ.block.place = (H2U.p12OfMade Zp.made).place := Blind.testSide_place hσ
  obtain ⟨c, l₁, l₂, hl, -, -, -⟩ := block_steps_at_first hR pre σ.block t St.cut (proverSideOfProximityTest _) hg
  rw [hpl] at hl
  refine rowsSay_at_run h hR D readers closing pl _ rfl Js fs σ hσ u pre t i St hlen hrun hc m' hm H' Q
    test carryX item n₁ n₂ b₀ Vd Rd Kp wv hbs hbeg hs' Said n' hin hok T' hTs (plainL Rw Pb') G hG
    (fun s m₀ E₀ l ds y hT₀ he hp em hd hsn => ?_)
  have hmid := play_mid _ _ _ _ _ hp
  have hdl : ds.length = n' := by
    have e := drawsFit_length _ _ hd
    rw [e, List.length_take]
    omega
  have hhe : (restFront (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m').heard =
      (frontOf m₀).heard := by
    show m'.st.heard.take (m'.st.heard.length - firstLen (H2U.p12OfMade Zp.made).nums.stages) = m₀.st.heard
    have hnn' : n' = firstLen (H2U.p12OfMade Zp.made).nums.stages := hnn
    rw [em, play_heard _ _ _ _ _ hp, ← hnn', List.length_append, hdl]
    simp
  have hL : heardL (restFront (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m') =
      heardL (frontOf m₀) := by
    unfold heardL
    rw [hhe]
  have hin₀ : m'.st.input = m₀.st.input := by
    rw [em]
    exact hmid.1
  have hAg : Blind.Agree (doorAtL Zp m₀.st.input (frontOf m₀)) T' := by
    rw [← hin₀]
    exact ag (frontOf m₀) hsn.symm
  have eH := congrArg Placed.parts (testHalf_atStand (V := Local W₀ Rc ProofFile.Inst Tr)
    (J := jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) hAg)
  simp only [proverSideOfProximityTest, List.cons.injEq, and_true] at eH
  obtain ⟨c', hl', ec⟩ := lend_of_eq eH.1.symm eH.2.symm hl
  exact tied_of_entry _ Js D readers closing pl c hl ca hca m'.st.input m₀.st.input hin₀ _ _
    hL Rw hRw _ _ _ _ _
    ((atStand (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m₀.st.input
      (frontOf m₀) T').first m₀.st.input (frontOf m₀)
      (restCoins (atStand (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m₀.st.input
      (frontOf m₀) T') c'.2.1))
    Pb' (fun Rr hr => hIM s m₀ E₀ _ rfl c' hT₀ he hl' Rr (by
      show carryRows D readers closing pl m₀.st.input (heardL (frontOf m₀))
        (stretches _ c'.2.1.2.2) = .ok Rr
      rw [ec]
      exact hr))

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.tables_in_front
#print axioms ProofFile.Honest.K12.Sim2.tied_of_entry
#print axioms ProofFile.Honest.K12.Sim2.rowsSay_at_run
#print axioms ProofFile.Honest.K12.Sim2.lend_of_eq
#print axioms ProofFile.Honest.K12.Sim2.rowsSay_of_closing
