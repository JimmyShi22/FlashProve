-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ShownAtRun.lean

A conditional: nothing here shows that ready or runC returns, that a part is called, or that a
filling holds the halves spoken of.

The library's three premises on what the shared rounds' two sendings and "SPLIT" have shown
(`ShownU`, `ShownO`, `ShownMu`: Johnson/Desc/K14/Honest/ItemsEach.lean), under the head `P5J.AtMg`,
at a run of the frame's walking prover, at a free prover but for three halves of the shared chain.
One definition; six theorems, three of them helpers.

  `heard_at_stand`: what a stand of the shared chain's walk has heard, its input, and the challenges
      that the shared view's rounds bear.
  `heldAt`: what an honest prover holds in front of the eight, as a term of the rows and of the two
      senders' coins.
  `lengths_eight`, `challenge_at`: helpers: how many rounds each of the eight declares; a challenge
      in front of a stand is the one that the shared view's round bears.
  `shownU_at_run`, `shownO_at_run`: `ShownU` and `ShownO` at a run, at `heldAt` of the input and of
      the coins that the book lends each sender.
  `shownMu_at_run`: `ShownMu` at a run, under a named premise on one coin.

By what. The frame's authors' `walk_mid` (Honest/Law/WalkMid.lean), `walk_hears`, `start_hears`,
`start_laid`, `walk_laid_drawn` (Honest/WalkHeard.lean);
`view_is_played`, `sending_at_run`, `split_at_run` (Sim/SendersAtRun.lean); `played_at_run`
(Sim/PlayedAtRun.lean). The shared rounds' authors' `shown_read` (Honest/K14/SendingsAnswers.lean),
`rowsU_read`, `rowsO_read` (SendingsRows.lean), `send_declares` (SendingsPlay.lean), `declares3`,
`declares_split` (Debts.lean), `jobU_par`, `sp_noMain` (SendingsShows.lean), `elems_one`
(MuPaid.lean). The library's `mu_coded` (Johnson/Desc/K14/Honest/MuCoded.lean), `flatOf_carried`
(FlatForm.lean), `Public8.to1`, `Public8.to4` (StepsBack.lean), `blocks_rounds` (ChainSteps.lean).
`planFacts_head`, `own_head` (DoorReturnsAt.lean), `facts_at_head` (NearAtHead.lean).

Limits.
- THREE PREMISES ON THE FILLING STAND IN THE STEAD OF THREE ON VALUES: that the prover's halves at
  the two sendings' places and at the eighth sub-protocol's are the shared rounds' authors' own
  (hg). That any filling holds them is not said here.
- `SendShapes` (Honest/K14/SendingsShows.lean), three public facts on shapes, is a premise; that it
  holds under the head is not shown here.
- `shownMu_at_run` takes hRows and hCoin. hCoin ties two parts' coins: at `heldAt` what is held of
  o_sp is made of the second sender's coins, and the scalar's coin is lent to "SPLIT": that the two
  are one coin is a fact of the book, not shown here.
- Each proof walks the road of those authors' own `showsU_of`, `showsO_of` (SendingsShows.lean) and
  `showsMu_of` (MuPaid.lean), which stand at a stand of their thread; here the stand is a run's.
- `heldAt` is a term: that a prover holds it is said of no prover. How it parts from the shared
  rounds' authors' `holds2`: its docstring.
- The shared chain alone. Of the walk (`runC`). A tie between terms: it names no value and states no
  law over random values. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.SendersAtRun
import Johnson.Desc.ProofFile.Honest.K14.SendingsShows
import Johnson.Desc.ProofFile.Honest.K14.MuPaid
import Johnson.Desc.ProofFile.Honest.K12.DoorReturnsAt
import Johnson.Desc.K14.Honest.StepsTwins
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E zeroE TableKey OracleNotice)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (P14 St blocks first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest
open ProofFile.Honest.K14 (Ask jobU jobOmega readCoins readFresh msgCoins SendShapes sendPlace liftSend
  sendingPart sendShownAt shown_read rowsU_read rowsO_read send_declares sendDeclared_like jobU_par
  sp_noMain elems elems_one declares3 declares_split Data liftK14 splitPart scalarAt entriesOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **What a stand of the shared chain's walk has heard, and its input, at a run.** Where the walk
over the first N prepared rounds, from runC's own start, has produced the first N rounds that the
run has played, and holds the state mb: mb has heard just the first N challenges; its input is the
shared parts' own; and the first N rounds of the shared view bear these challenges. General in the
description, the book and the prover. -/
theorem heard_at_stand {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (N : ℕ)
    (a₂ zb : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (mb : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
    (ha : ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
      (some (F.start₂ (F.pub x))) [] = .ok a₂)
    (hz : walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take N) (ρ.shared.take N) a₂ =
      .ok zb)
    (hl : zb.laid = r.run.played.2.1.take N) (hm : zb.mid = some mb) :
    mb.st.heard = ρ.shared.take N ∧ mb.st.input = R.common ∧
      (r.run.views.2.1.rounds.take N).map (·.drawn) = ρ.shared.take N := by
  have h3 := walk_laid_drawn _ _ _ a₂ zb hz
  rw [start_laid ha, List.map_nil, List.nil_append] at h3
  have h1 := walk_hears _ _ _ _ a₂ zb (start_hears ha) hz mb hm
  rw [h3] at h1
  have h2 := (walk_mid ha hz hm).1
  refine ⟨h1, h2, ?_⟩
  rw [view_is_played hrun]
  unfold roundsOf
  rw [← List.map_take, List.map_map, ← hl]
  exact h3

/-- A challenge of the shared chain in front of the state that the walk of hz holds, where that walk
has produced the run's first n rounds (hl), is the one that the shared view's round of that number
bears. -/
theorem challenge_at {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (n : ℕ)
    (a₂ z : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
    (ha : ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
      (some (F.start₂ (F.pub x))) [] = .ok a₂)
    (hz : walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ (R.shared.take n) (ρ.shared.take n) a₂ = .ok z)
    (hl : z.laid = r.run.played.2.1.take n) (hm : z.mid = some m) (j : ℕ) (hj : j < n) :
    ρ.shared[j]? = (r.run.views.2.1.rounds[j]?).map (·.drawn) := by
  have g := congrArg (·[j]?) (heard_at_stand hrun n a₂ z m ha hz hl hm).2.2
  simp only [List.getElem?_map, List.getElem?_take_of_lt hj] at g
  exact g.symm

/-- How many rounds each of the eight declares: 1, 2, 0, 1, 2, 0, 1, 1. -/
theorem lengths_eight (Q : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) :
    b1.rounds.length = 1 ∧ b2.rounds.length = 2 ∧ b3.rounds.length = 0 ∧ b4.rounds.length = 1 ∧
      b5.rounds.length = 2 ∧ b6.rounds.length = 0 ∧ b7.rounds.length = 1 ∧
      b8.rounds.length = 1 := by
  obtain ⟨-, -, -, r1, -, r4, -, r7, -⟩ := declares3 Q b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨dU, -, dO, -⟩ := send_declares Q 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨a0, a1, a2, r2, -⟩ := dU.rounds
  obtain ⟨a3, a4, a5, r5, -⟩ := dO.rounds
  obtain ⟨-, -, r3, -, -, r6, -, -⟩ := blocks_rounds Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  obtain ⟨-, r8, -⟩ := declares_split Q b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  rw [r1, r2, r3, r4, r5, r6, r7, r8]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **What an honest prover holds in front of the eight, as a term of what the two sendings' parts
are handed**: a: the input as a sending's part is handed it (the rows); csU, csO: the coins of "send
o_u"'s and "send o_omega"'s part. Its five fields are the right sides of the five equations on what
is held that `rowsU_read` and `rowsO_read` (Honest/K14/SendingsRows.lean) ask; no word in front. Kin
of those authors' `holds2` (Honest/K14/Holds2.lean), from which it parts in three things: the coins
are letters, where `holds2` reads a run's coins at an address; the rows are a letter's; and o_u's
shape is the plan's (`Q.par.S.fold.u`), where `holds2` reads the job's first notice with a default:
these two shapes are one under `rowsU_read`'s premise hs0, a fact of the plan. No statement here
says that the two terms are one. Total moves: a coin beyond the end of the array is read as 0; the
shape of the first sending's second message is read with a default; where the test on G_u has no
first stage the first mask's values are read as a plain message's. -/
noncomputable def heldAt (Q : P14) (a : Ask) (csU csO : Array E) : Inputs where
  w₀ := fun _ _ _ => 0
  Rw := fun r j => rdE.val (a.rows r j)
  cU := readCoins Q.codes Q.par.S.fold.u (msgCoins (jobU ⟨Q, 0⟩) csU 0)
  cMask :=
    match Q.S.testU.head? with
    | some s => readFresh Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
        (msgCoins (jobU ⟨Q, 0⟩) csU 1) s.k s.h
    | none => readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
        (msgCoins (jobU ⟨Q, 0⟩) csU 1)
  cOmega := readCoins Q.codes Q.par.S.omega (msgCoins (jobOmega ⟨Q, 0⟩) csO 0)
  cSp := readCoins Q.codes Q.par.S.sharedSplit (msgCoins (jobOmega ⟨Q, 0⟩) csO 1)

/-- **`ShownU` at a run.** Under the head, at a run of the walking prover at which a part of the
shared chain behind "send o_u" is called: where the filling's half at that sending's place is the
shared rounds' authors' own part, at a reader wit of the input, and the shapes of the two sendings'
messages have these authors' three public facts: the book has lent that part coins cU; and at the
eight rounds W and states D8 of a run of steps over the shared view's rounds: the first sending's
answers are the honest ones at `heldAt` of the input as that part is handed it and of cU, whatever
the second sender's coins are. -/
theorem shownU_at_run {W₀ Rc Tr X₀ Y V Pb : Type}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre' t' : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hin : 3 ≤ (pre'.flatMap (·.rounds)).length + i)
    (hSh : SendShapes (K1.qAt Zp Np)) (wit : Common W₀ Rc TableKey → Ask)
    (hg : (P.shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (W : Seen8) (D8 : States8) (rest₈ : List Fmt.RoundView)
    (hW : r.run.views.2.1.rounds =
      [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈)
    (hst : StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
      (first (K1.qAt Zp Np).codes x.pub.key) W D8) :
    ∃ cU : RowCoins
      [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)],
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 2)
      [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cU ∧
      ∀ csO : Array E, ShownU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
        (first (K1.qAt Zp Np).codes x.pub.key) W.view D8
        (heldAt (K1.qAt Zp Np) (wit R.common) (coinsE cU.1.1).toArray csO) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have Sp : Public8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
      (first (K1.qAt Zp Np).codes x.pub.key) := ⟨hP, hBU, hBO, rfl, rfl⟩
  obtain ⟨a₂, zN, m, ha, hzN, hzl, hzm, -⟩ :=
    played_at_run h.laid.planOk hR hrun σ u pre' t' i _ S rfl hc
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1] ++ x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have hN₀ : ([x0, x1].flatMap (·.rounds)).length = 1 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, n1]
    rfl
  have hN : (List.flatMap
      (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl => y.rounds)
      [x0, x1]).length = 1 := hN₀
  obtain ⟨dU, pU, -, -⟩ := send_declares (K1.qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, -⟩ := (sendDeclared_like l2.rounds l2.oracles dU).rounds
  have hpl : x2.place = sendPlace 2 := l2.place.trans pU
  obtain ⟨ab, zb, mb, c, y₀, y₁, qa, q1, q1l, q1m, q2, q3, -, -, -, q7⟩ :=
    sending_at_run h.laid.planOk hR hrun σ u pre' t' i S hc [x0, x1] x2 _ eF'
      (jobU ⟨K1.qAt Zp Np, 0⟩) wit (by rw [hpl]; exact hg) d₀ d₁ os (by rw [hr, ho]; rfl) hf₀ hf₁
      (by rw [hN]; exact hin)
  rw [hN] at q1 q1l q3 q7
  rw [hpl] at q2
  refine ⟨c, q2, fun csO => ?_⟩
  obtain ⟨g1, g2, g3⟩ := heard_at_stand hrun 1 ab zb mb qa q1 q1l q1m
  have hheard : mb.st.heard = [W.R1.drawn] := by
    rw [g1, ← g3, hW]
    rfl
  have c1 := challenge_at hrun _ a₂ zN m ha hzN hzl hzm 1
    (Nat.lt_of_lt_of_le (by decide : 1 < 3) hin)
  rw [hW, q3] at c1
  obtain rfl : y₀ = W.R2a.drawn := Option.some.inj c1
  rw [hW, g2] at q7
  have e2 : W.R2b = ⟨sendShownAt (jobU ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common)
      (mb.st.heard ++ [W.R2a.drawn]), y₁⟩ := Option.some.inj q7
  have t := Sp.to1 hst.front.front.front.front.front.front.front
  have hT : D8.d1.st.codes = (K1.qAt Zp Np).codes := (Sp.at1 t).carried.codes
  have eQ := jobU_par (Q := (K1.qAt Zp Np)) hU 0
  have hs0 : ((jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape =
      (K1.qAt Zp Np).par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) 0
      ⟨(K1.qAt Zp Np).par.S.fold.u, (K1.qAt Zp Np).par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hU)).1
  have hsz : (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent.size ≤ 2 := by
    rw [eQ, Desc.K14.Law.parK1_sent, hP.goesTwo]
  show W.R2b.vals = _
  rw [e2]
  show sendShownAt (jobU ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common)
    (mb.st.heard ++ [W.R2a.drawn]) = _
  rw [shown_read (jobU ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common) mb.st.heard W.R2a.drawn W.R2a.vals
    D8.d1.st (by rw [hT, eQ]; rfl)
    (rowsU (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (wit R.common) (coinsE c.1.1).toArray csO))
    (heldAt (K1.qAt Zp Np) (wit R.common) (coinsE c.1.1).toArray csO).w₀ fun kk hkk part j _ =>
      rowsU_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
        (heldAt (K1.qAt Zp Np) (wit R.common) (coinsE c.1.1).toArray csO) (wit R.common)
        (mb.st.heard ++ [W.R2a.drawn]) (coinsE c.1.1).toArray hsz hs0 hSh.u hSh.mask
        (by
          rw [hheard]
          exact elems_one _)
        t.point (fun _ _ => rfl) rfl rfl kk hkk part j, eQ]
  rfl

/-- **`ShownO` at a run.** The like at "send o_omega": the book has lent that sending's part coins
cO, and the second sending's answers are the honest ones at `heldAt` of the input and of cO,
whatever the first sender's coins are. -/
theorem shownO_at_run {W₀ Rc Tr X₀ Y V Pb : Type}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre' t' : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hin : 6 ≤ (pre'.flatMap (·.rounds)).length + i)
    (hSh : SendShapes (K1.qAt Zp Np)) (wit : Common W₀ Rc TableKey → Ask)
    (hg : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (W : Seen8) (D8 : States8) (rest₈ : List Fmt.RoundView)
    (hW : r.run.views.2.1.rounds =
      [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈)
    (hst : StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
      (first (K1.qAt Zp Np).codes x.pub.key) W D8) :
    ∃ cO : RowCoins
      [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)],
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 5)
      [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO ∧
      ∀ csU : Array E, ShownO (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
        (first (K1.qAt Zp Np).codes x.pub.key) W.view D8
        (heldAt (K1.qAt Zp Np) (wit R.common) csU (coinsE cO.1.1).toArray) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have Sp : Public8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
      (first (K1.qAt Zp Np).codes x.pub.key) := ⟨hP, hBU, hBO, rfl, rfl⟩
  obtain ⟨a₂, zN, m, ha, hzN, hzl, hzm, -⟩ :=
    played_at_run h.laid.planOk hR hrun σ u pre' t' i _ S rfl hc
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1, x2, x3, x4] ++ x5 :: x6 :: x7 :: x8 :: tl := eF
  have hN₀ : ([x0, x1, x2, x3, x4].flatMap (·.rounds)).length = 4 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, n1, n2, n3, n4]
    rfl
  have hN : (List.flatMap
      (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl => y.rounds)
      [x0, x1, x2, x3, x4]).length = 4 := hN₀
  obtain ⟨-, -, dO, pO⟩ := send_declares (K1.qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, -⟩ := (sendDeclared_like l5.rounds l5.oracles dO).rounds
  have hpl : x5.place = sendPlace 5 := l5.place.trans pO
  obtain ⟨ab, zb, mb, c, y₀, y₁, qa, q1, q1l, q1m, q2, q3, -, -, -, q7⟩ :=
    sending_at_run h.laid.planOk hR hrun σ u pre' t' i S hc [x0, x1, x2, x3, x4] x5 _ eF'
      (jobOmega ⟨K1.qAt Zp Np, 0⟩) wit (by rw [hpl]; exact hg) d₀ d₁ os (by rw [hr, ho]; rfl) hf₀
      hf₁ (by rw [hN]; exact hin)
  rw [hN] at q1 q1l q3 q7
  rw [hpl] at q2
  refine ⟨c, q2, fun csU => ?_⟩
  obtain ⟨g1, g2, g3⟩ := heard_at_stand hrun 4 ab zb mb qa q1 q1l q1m
  have hheard : mb.st.heard = [W.R1.drawn, W.R2a.drawn, W.R2b.drawn, W.R4.drawn] := by
    rw [g1, ← g3, hW]
    rfl
  have c1 := challenge_at hrun _ a₂ zN m ha hzN hzl hzm 4
    (Nat.lt_of_lt_of_le (by decide : 4 < 6) hin)
  rw [hW, q3] at c1
  obtain rfl : y₀ = W.R5a.drawn := Option.some.inj c1
  rw [hW, g2] at q7
  have e2 : W.R5b = ⟨sendShownAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common)
      (mb.st.heard ++ [W.R5a.drawn]), y₁⟩ := Option.some.inj q7
  obtain ⟨x2', ids2, t⟩ := Sp.to4 hst.front.front.front.front
  have hT : D8.d4.st.codes = (K1.qAt Zp Np).codes := (Sp.at4 t).carried.codes
  have hw := Desc.K14.Honest.withOmega_two hP.two
  have sO : (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent = Desc.K14.withOmega (K1.qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (K1.qAt Zp Np) 5 _ _
  have hs0 : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape =
      (K1.qAt Zp Np).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 0
      ⟨(K1.qAt Zp Np).par.S.omega, (K1.qAt Zp Np).par.S.omegaLeafClass⟩
      (by rw [sO]; exact hw.2.1)).1
  have hs1 : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 1 default).shape =
      (K1.qAt Zp Np).par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 1
      ⟨(K1.qAt Zp Np).par.S.sharedSplit, (K1.qAt Zp Np).par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact hw.2.2)).1
  have hsz : (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.size ≤ 2 := by
    rw [sO]
    exact Nat.le_of_eq hw.1
  show W.R5b.vals = _
  rw [e2]
  show sendShownAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common)
    (mb.st.heard ++ [W.R5a.drawn]) = _
  rw [shown_read (jobOmega ⟨K1.qAt Zp Np, 0⟩) c.1.1 (wit R.common) mb.st.heard W.R5a.drawn
    W.R5a.vals D8.d4.st hT
    (rowsO (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (wit R.common) csU (coinsE c.1.1).toArray))
    (words1 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (wit R.common) csU (coinsE c.1.1).toArray)) fun kk hkk part j _ =>
      rowsO_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
        (heldAt (K1.qAt Zp Np) (wit R.common) csU (coinsE c.1.1).toArray) (wit R.common)
        (mb.st.heard ++ [W.R5a.drawn]) (coinsE c.1.1).toArray hsz hs0 hs1 hSh.omega
        (sp_noMain ⟨hP, hBU, hBO⟩)
        (by
          rw [hheard]
          exact elems_one _)
        t.front.front.front.point (fun _ _ => rfl) rfl rfl kk hkk part j]
  rfl

/-- **`ShownMu` at a run, under a named premise on one coin.** Under the head, at a run at which a
part of the shared chain behind "SPLIT" is called: where the filling's half at the eighth
sub-protocol's place is the shared rounds' authors' part `splitPart`, at public data A of the plan's
shape that hears the point as the chain's round number 0 and zeta as its number 6: the book has lent
that part coins cS; and at everything H that an honest prover may hold: if H's rows are, at the
places that hold the matrix, the entries that the part is handed, read (hRows), and the entry number
0 of o_sp's mask row as H holds it is the coin that the part spends, read (hCoin): the scalar shown
is the honest one. hCoin ties two parts' coins: what H holds of o_sp is the second sender's; the
scalar's coin is lent to "SPLIT". -/
theorem shownMu_at_run {W₀ Rc Tr X₀ Y V Pb : Type}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre' t' : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hin : 8 ≤ (pre'.flatMap (·.rounds)).length + i)
    (A : Data) (weights : W₀ → Weights) (hS : A.S = (K1.qAt Zp Np).par.S) (h0 : A.atPoint = 0)
    (h6 : A.atZeta = 6)
    (hg : (P.shared.find? fun g => g.place == b8.place) = some ⟨b8.place,
      [(liftK14 A weights (splitPart A) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (W : Seen8) (D8 : States8) (rest₈ : List Fmt.RoundView)
    (hW : r.run.views.2.1.rounds =
      [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈)
    (hst : StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
      (first (K1.qAt Zp Np).codes x.pub.key) W D8) :
    ∃ cS : RowCoins
      [(liftK14 A weights (splitPart A) :
        Part Empty (Common W₀ Rc TableKey) X₀)],
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b8.place
      [(liftK14 A weights (splitPart A) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cS ∧
      ∀ H : Inputs,
        (∀ r < (K1.qAt Zp Np).par.S.fold.index.rows,
          ∀ j < (K1.qAt Zp Np).par.S.matrixRows * 2 ^ (K1.qAt Zp Np).par.S.kLo,
            H.Rw r j = rdE.val (entriesOf A.S (weights R.common.w₀) r j)) →
        kappaOf H.cSp (K1.qAt Zp Np).par.S.sharedSplit.maskRows 0 =
          rdE.val ((coinsE cS.1.2.1.1).headD zeroE) →
        ShownMu (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view H := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have Sp : Public8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
      (first (K1.qAt Zp Np).codes x.pub.key) := ⟨hP, hBU, hBO, rfl, rfl⟩
  obtain ⟨a₂, zN, m, ha, hzN, hzl, hzm, -⟩ :=
    played_at_run h.laid.planOk hR hrun σ u pre' t' i _ S rfl hc
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1, x2, x3, x4, x5, x6, x7] ++ x8 :: tl := eF
  have hN₀ : ([x0, x1, x2, x3, x4, x5, x6, x7].flatMap (·.rounds)).length = 7 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds, n1,
      n2, n3, n4, n5, n6, n7]
    rfl
  have hN : (List.flatMap
      (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl => y.rounds)
      [x0, x1, x2, x3, x4, x5, x6, x7]).length = 7 := hN₀
  obtain ⟨hcut, r8, o8⟩ := declares_split (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb hSN
  obtain ⟨ab, zb, mb, c, y₀, qa, q1, q1l, q1m, q2, -, -, q7⟩ :=
    split_at_run h.laid.planOk hR hrun σ u pre' t' i S hc [x0, x1, x2, x3, x4, x5, x6, x7] x8 _
      eF' A weights (by rw [l8.place]; exact hg) { entry := Desc.K14.Law.entryAt (K1.qAt Zp Np) 3 }
      (by rw [l8.rounds, l8.oracles, r8, o8]; rfl) hcut (by rw [hN]; exact hin)
  rw [hN] at q1 q1l q7
  rw [l8.place] at q2
  refine ⟨c, q2, fun H hRows hCoin => ?_⟩
  obtain ⟨g1, g2, g3⟩ := heard_at_stand hrun 7 ab zb mb qa q1 q1l q1m
  have hheard : mb.st.heard = [W.R1.drawn, W.R2a.drawn, W.R2b.drawn, W.R4.drawn, W.R5a.drawn,
      W.R5b.drawn, W.R7.drawn] := by
    rw [g1, ← g3, hW]
    rfl
  rw [hW] at q7
  have e8 : W.R8 = ⟨[.e (OnBytes.Slice.ofE (scalarAt A c.1 (K14.askOf A weights mb.st)))], y₀⟩ :=
    Option.some.inj q7
  have t := Sp.to1 hst.front.front.front.front.front.front.front
  have p1 : elems (heardFrom (K14.askOf A weights mb.st) A.atPoint 1) =
      Desc.K14.drawn W.view.r1 := by
    rw [h0]
    show elems ((mb.st.heard.drop 0).take 1) = _
    rw [hheard]
    exact elems_one _
  have p7 : elems (heardFrom (K14.askOf A weights mb.st) A.atZeta 1) =
      Desc.K14.drawn W.view.r7 := by
    rw [h6]
    show elems ((mb.st.heard.drop 6).take 1) = _
    rw [hheard]
    exact elems_one _
  have key : scalarAt A c.1 (K14.askOf A weights mb.st) =
      muRun (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 W.view.r7 H := by
    show rdE.val (muAtE A.S (elems (heardFrom (K14.askOf A weights mb.st) A.atPoint 1))
      (elems (heardFrom (K14.askOf A weights mb.st) A.atZeta 1))
      (entriesOf A.S (weights mb.st.input.w₀)) ((coinsE c.1.2.1.1).headD zeroE)) = _
    rw [p1, p7, hS, g2]
    exact mu_coded (K1.qAt Zp Np) _ W.view.r1 W.view.r7 H _ _ t.point
      (fun r hr j hj => by rw [hRows r hr j hj, hS]) hCoin
  show W.R8.vals = _
  rw [e8, ← key]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.heard_at_stand
#print axioms ProofFile.Honest.K12.Light.challenge_at
#print axioms ProofFile.Honest.K12.Light.lengths_eight
#print axioms ProofFile.Honest.K12.Light.heldAt
#print axioms ProofFile.Honest.K12.Light.shownU_at_run
#print axioms ProofFile.Honest.K12.Light.shownO_at_run
#print axioms ProofFile.Honest.K12.Light.shownMu_at_run
