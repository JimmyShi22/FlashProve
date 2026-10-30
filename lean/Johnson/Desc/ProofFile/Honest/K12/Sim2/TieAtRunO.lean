-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the tie of the words at the test on G_omega, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TieAtRunO.lean: CONDITIONAL: nothing here shows that ready or
runC returns, that the part is called, or that the frame lends.

OF WHAT KIND IT IS. A tie between what one part is handed of a run's values and what another part is
handed of them. It names no value and states no law over random values: a tie between terms.

What is here. The twin at the test on G_omega of `tie_at_run` (Honest/K12/TieAtRun.lean, at the test
on G_u): the tie of the words that `saysAt_run_O` (Sim2/SaysAtRunO.lean) asks, to its letter, at a
run of the frame's walking prover under the head: on the tables of the members of the group under
the test on G_omega (2: o_omega; 3: o_sp) the honest words at `heldAt` (Sim/ShownAtRun.lean) are the
words that the test's job makes of its own rows at the carried coins. General in the job's state
function door. No definition; two statements.

  `rounds_in_front_O`   the first ten declare eight rounds at least.
  `tie_at_run_O`   the statement.

The premises, sorted. Public: the head, hb, h10, hσ (the side's place is the test's). On the filling
and the book: hR, S, the lending lO. On the run: hrun, hc, the fold's return over the eight hfold,
the view's rounds hW. At the stand: that m is the walk's own and ca what the book hands at the run's
own coins; the state on entry has the door's public shape (`shape_head_OmegaF` has it at every input
and front) and is the way in at d9. THE TIE OF VALUES: hbk (`bookCutsOmega`, CutOfBookAt.lean: a
test with code on the book's entries; `bookCutsOmega_head` pays it at the library's book). No
premise on the prover's halves. csU is free: the first sender's coins enter no word on the tables 2
and 3.

The chain, link by link. Left: the library's `words2` at the two members' numbers; `rowsO_read`
(Honest/K14/SendingsRows.lean) from right to left, at `heldAt`. Right: `wordsAt_member`
(WordsOfMember.lean) behind the test's beginning. The carried coins are the sender's own cuts:
`cuts_atOmega` (CutOfBookAt.lean), `own_of_lendPart` (Sim/SenderInFront.lean): the sender's own cut
is taken from the lending lO, so no premise on the book's cover or row is asked. One vector on both
sides: `data_same` over `jobOmega_readsBelow`. The stand: `played_at_run`, `heard_at_stand`,
`challenge_at`. The statement's shape at the state on entry: closed lines and laws
off the thread (K12/AtFile/OWords.lean: `codes_real_O`, `orc_O2`, `orc_O3`, `group_at_stand`,
`ellOmega_head`). `tie_omega` and `tie_sp` (K12/AtFile/OTie.lean) are NOT called: they
stand at another term for what is held and at two more premises on the book; their text was the
pattern for the member 2.

The label. K12/AtFile/OWords.lean's head bears "NOT IN FRONT OF A LAW OVER COINS" for its statement
behind a thread's stand. What is called of that file here has no thread, no stand and no coin among
its binders: closed lines on the typed sizes and two laws on a state's public shape.

Limits. At the job's rows at the members alone: off the members nothing is said. The guard on the
field changes no coin: the guarded part is lent what the part is lent, by the texts. Nothing on
completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.TieAtRun
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OWords
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle Group)
open OnBytes.Slice (rdE begun)
open OnBytes.Means (layoutOf tableSize)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (P14 St blocks first withU)
open Desc.K14.Honest
open Desc.K14.Law (parO)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtFile (ellOmegaB ellOmega_head group_at_stand codes_real_O orc_O2 orc_O3
  omegaShape_head orc_of_shape headShape)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K14 (Ask jobOmega sendPlace liftSend sendingPart elems elems_one rowsO_read
  sp_noMain takesOf jobOmega_readsBelow)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL: on the head and the eight. **The shared chain's first ten sub-protocols declare
eight rounds at least.** -/
theorem rounds_in_front_O (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (pre : List (Block St ProofFile.Cl)) (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10) :
    8 ≤ (pre.flatMap (·.rounds)).length := by
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ tl.take 1 := by
    rw [h10, eF']
    rfl
  have h9 : ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length = 8 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
      l8.rounds, n1, n2, n3, n4, n5, n6, n7, n8]
    rfl
  rw [epre, List.flatMap_append, List.length_append, h9]
  exact Nat.le_add_right _ _

set_option maxHeartbeats 1000000 in
/-- CONDITIONAL: see the head. **The tie of the words at a run, at the test on G_omega.** Under the
head, at a run at which the guarded second part of the test on G_omega is called: at the run's stand
m and carried blocks ca, at a state d9 whose way in is the job's state on entry there, at W's first
round, at any array csU and at the coins cO that the book lends the sending of o_omega and o_sp: on
the tables of the group's members, 2 and 3, the honest words at `heldAt` of the input and of cO's
coins are the words that the job's own rows make at the carried coins. OF WHAT KIND IT IS: a tie
between what one part is handed of a run's values and what another part is handed of them. -/
theorem tie_at_run_O {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {pO : P12} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (Js : SimJob TableKey) (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
      (restMember (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest
          Js :
        Member Empty _ _ _).guarded pre t (firstLen pO.nums.stages))
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hσ : σ.block.place = pO.place)
    (hbk : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true)
    (W : Seen8) (d8 d9 : St) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn) (csU : Array E)
    (cO : RowCoins
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)])
    (hfold : foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
      r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest₈, more))
    (hW : r.run.views.2.1.rounds =
      [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈)
    (lO : lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 5)
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO) :
    ∀ (m : Mid (Common W₀ Rc TableKey) X₀)
      (ca : CsAll (restPart (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand
          none).toRun.toTest :
        Part Empty (Common W₀ Rc TableKey) X₀).needsField.carries),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest :
          Part Empty (Common W₀ Rc TableKey) X₀).needsField = .ok ca →
      testSh (door m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights
          rand none).toRun.toTest m)) =
        headShape Zp Np →
      VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) d9 =
        .ok (door m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights
            rand none).toRun.toTest m)) →
    ∀ G, d9.st.groups[d9.loc.gOmega]? = some G →
      WordsTied d9.st d9.loc.gOmega G
        (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
          (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand R.common) csU
            (coinsE cO.1.1).toArray))
        (layoutOf d9.st G)
        (plainMany (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none)
          m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand
              none).toRun.toTest m)
          (carriedCoins (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand
              none).toRun.toTest
            (stretches _ ca))) := by
  intro m ca hm hca hsh hent G hG oM ho pt i hi
  -- the state on entry is the way in at d9
  have et := (Except.ok.inj hent).symm
  have est : (door m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights
      rand none).toRun.toTest m)).st = d9.st := by
    rw [et]
  have eg : (door m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights
      rand none).toRun.toTest m)).g =
      d9.loc.gOmega := by
    rw [et]
  rw [← est] at hG hi ⊢
  rw [← eg] at hG ⊢
  generalize hT : (door m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door
      weights rand none).toRun.toTest m)) = T at hsh hG hi ⊢
  -- public facts under the head
  obtain ⟨hSN, hMA, hU⟩ := facts_at_head h
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have hSh := sendShapes_head h
  have hQf := sendingsFit_head h
  have hw : (Desc.K14.withOmega (K1.qAt Zp Np).S).size = 2 ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[0]? =
        some ⟨(K1.qAt Zp Np).S.omega, (K1.qAt Zp Np).S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[1]? =
        some ⟨(K1.qAt Zp Np).S.sharedSplit, (K1.qAt Zp Np).S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.two
  have hE := ells_head h
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨-, zO1⟩ := hE
  have lO0 := ellOmega_head h
  unfold ellOmegaB at lO0
  rw [beq_iff_eq] at lO0
  -- the fold opened: the first round has the point's length
  obtain ⟨W', D', e1, -, -, u'⟩ :=
    Eight.stepTo8_of_fold (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np))
      hU hSN 0 _ d8 _ rest₈ _ more hfold
  have eW : W'.R1 = W.R1 := by
    have e := e1.symm.trans hW
    simp only [List.cons_append, List.cons.injEq] at e
    exact e.1
  have Sp : Public8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
      (first (K1.qAt Zp Np).codes x.pub.key) := ⟨hP, hBU, hBO, rfl, rfl⟩
  have hpt : (Desc.K14.drawn W.view.r1).length = (K1.qAt Zp Np).par.S.kCol := by
    have t' := (Sp.to1 u'.front.front.front.front.front.front.front).point
    have e : W'.view.r1 = W.view.r1 := by
      simp only [Seen8.view, eW]
    rw [← e]
    exact t'
  have h8 := rounds_in_front_O h b1 b2 b3 b4 b5 b6 b7 b8 hb pre h10
  -- the stand in front of the second part
  obtain ⟨a₂, zN, m'', ha, hzN, hzl, hzm, hm''⟩ :=
    played_at_run h.laid.planOk hR hrun σ _ pre t _ _ S rfl hc
  obtain rfl : m = m'' := Option.some.inj (Except.ok.inj (hm.symm.trans hm''))
  obtain ⟨hheard, hinp, -⟩ := heard_at_stand hrun _ a₂ zN m ha hzN hzl hzm
  have hLen : m.st.heard.length = (pre.flatMap (·.rounds)).length + firstLen pO.nums.stages := by
    rw [hheard, walk_len _ _ _ a₂ zN hzN, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) S.fits)
  have c0 := challenge_at hrun _ a₂ zN m ha hzN hzl hzm 0
    (Nat.lt_of_lt_of_le (by decide : 0 < 8) (Nat.le_trans h8 (Nat.le_add_right _ _)))
  rw [hW] at c0
  have c0' : ρ.shared[0]? = some W.R1.drawn := c0
  have ht1 : ρ.shared.take 1 = [W.R1.drawn] := by
    cases hρ : ρ.shared with
    | nil =>
      rw [hρ] at c0'
      simp at c0'
    | cons a l =>
      rw [hρ] at c0'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at c0'
      rw [c0']
      rfl
  -- one vector on both sides, at both messages
  have hv : ∀ n, vecAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) n (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none
      m.st.input (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand
          none).toRun.toTest m) =
      (jobOmega ⟨K1.qAt Zp Np, 0⟩).data (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input,
        ρ.shared.take 1, ()⟩ : State Ask Unit) n := by
    intro n
    show (jobOmega ⟨K1.qAt Zp Np, 0⟩).data (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input,
      m.st.heard.take (m.st.heard.length - firstLen pO.nums.stages),
      ()⟩ : State Ask Unit) n = _
    refine congrFun (data_same (jobOmega_readsBelow ⟨K1.qAt Zp Np, 0⟩) _ _ _ ?_) n
    show List.take 1 _ = List.take 1 _
    obtain ⟨n', hn⟩ : ∃ n', m.st.heard = ρ.shared.take n' := ⟨_, hheard⟩
    have hn1 : 1 ≤ n' := by
      have e := List.length_take_le n' ρ.shared
      rw [← hn, hLen] at e
      omega
    rw [hLen, Nat.add_sub_cancel, hn, List.take_take, List.take_take, List.take_take,
      Nat.min_eq_left (Nat.le_trans (by decide : 1 ≤ 8) h8), Nat.min_eq_left hn1, Nat.min_self]
  -- what the second part is lent, and the two cuts
  have hca' : (lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨σ.block.place, 1⟩
      (restPart (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest :
        Part Empty (Common W₀ Rc TableKey) X₀)).map (·.2.2) = .ok ca := by
    have e := hca
    unfold carriedAt at e
    rw [lendPart_guarded] at e
    exact e
  obtain ⟨c, hl, rfl⟩ := exMap_ok hca'
  rw [hσ, look_shared] at hl
  have hOc : (sharedLook Bk k.shared ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent
        (jobOmega ⟨K1.qAt Zp Np, 0⟩).sort) = some cO.1.1 :=
    own_of_lendPart (lendRow_cons_ok lO).1
  obtain ⟨sc0, sc1⟩ := cuts_atOmega Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨K1.qAt Zp Np, 0⟩
    pO door weights rand none cO.1.1 hOc c hl hbk
  -- the shapes, the sizes, the finds
  rw [← hinp]
  have sOs : (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent = Desc.K14.withOmega (K1.qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (K1.qAt Zp Np) 5 _ _
  have hs0O : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape =
      (K1.qAt Zp Np).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 0
      ⟨(K1.qAt Zp Np).par.S.omega, (K1.qAt Zp Np).par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 1 default).shape =
      (K1.qAt Zp Np).par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 1
      ⟨(K1.qAt Zp Np).par.S.sharedSplit, (K1.qAt Zp Np).par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have hnoSp : (K1.qAt Zp Np).par.S.sharedSplit.mainRows = 0 := sp_noMain ⟨hP, hBU, hBO⟩
  have hp1 : elems (heardFrom (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input,
    ρ.shared.take 1, ()⟩ : State Ask Unit) 0 1) = Desc.K14.drawn W.view.r1 := by
    rw [ht1]
    exact elems_one _
  -- the statement's shape, by the door's
  obtain ⟨x₀', hx₀, Wr⟩ := written_at_head h
  obtain ⟨x', hx', eS, -, -⟩ := omegaShape_head h
  obtain rfl : x₀' = x' := congrArg Prod.fst (Option.some.inj (hx₀.symm.trans hx'))
  have hsh' := hsh.trans eS
  have hcodes : T.st.codes = (K1.qAt Zp Np).codes := by
    have k₁ := codes_real_O
    rw [hx₀] at k₁
    simp only [Option.all_some, beq_iff_eq] at k₁
    have h1 : (testSh T).core.st.codes = T.st.codes := rfl
    rw [← h1, hsh', k₁, qAt_written Wr Np]
  have hmem : G.members.toList = [2, 3] := (group_at_stand h _ hsh G hG).2
  have hmemA : G.members = #[2, 3] := Array.toList_inj.1 hmem
  obtain ⟨hf2, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two (layoutOf T.st G) 2 3 (by decide)
    (show G.members = #[2, 3] from hmemA)
  have hts : ∀ o' pt', tableSize (begun T.st T.g G) o' pt' = tableSize T.st o' pt' :=
    fun o' pt' => by
      unfold tableSize OnBytes.Statement.tableBits
      rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd := (OnBytes.Slice.begun_codes T.st T.g G).trans hcodes
  have hoo : oM = 2 ∨ oM = 3 := by
    have h' : oM ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl
  · -- o_omega
    have hk0 : 0 < (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.size := by
      rw [sOs, hw.1]
      decide
    have hy2 : ((begun T.st T.g G).oracles[2]?).map (·.shape) =
        some (shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 0) := by
      have k₁ := orc_O2
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy2
    have wM := wordsAt_member (K1.qAt Zp Np) hQf (jobOmega ⟨K1.qAt Zp Np, 0⟩) (Or.inr ⟨rfl, rfl⟩) 0
      hk0 _ rfl ⟨sendPlace 5, 0⟩ _ (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none m.st.input
      (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest m)
      (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input, ρ.shared.take 1, ()⟩ : State Ask Unit) (hv
          0)
      (coinsE cO.1.1).toArray (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none) 0
          rfl
      (carriedCoins (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest
        (stretches _ c.2.2)) sc0 (begun T.st T.g G) (layoutOf T.st G) 2 hf2 y hy hys
      (by rw [hcd]; rfl) (fun _ => lO0)
      (fun hpos => absurd hpos (by
        show ¬ 0 < ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape.maskRows
        rw [hs0O, hSh.omega.noMask]
        exact Nat.lt_irrefl 0)) pt i (by rw [hts]; exact hi)
    have rO := rowsO_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input) csU
        (coinsE cO.1.1).toArray)
      (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input) (ρ.shared.take 1) (coinsE cO.1.1).toArray
      (by rw [sOs, hw.1]) hs0O hs1O hSh.omega hnoSp hp1 hpt (fun _ _ => rfl) rfl rfl 0 hk0 pt i
    refine Eq.trans ?_ wM.symm
    rw [rO]
    show (if 0 + 2 ≤ 2 ∧ 2 < 0 + 2 + (parO (K1.qAt Zp Np)).sent.size then _ else _) = _
    rw [if_pos ⟨by omega, by
      have e : (parO (K1.qAt Zp Np)).sent.size = 2 := by
        rw [Desc.K14.Law.parK1_sent]
        exact hw.1
      rw [e]
      decide⟩]
    rfl
  · -- o_sp
    have hk1 : 1 < (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.size := by
      rw [sOs, hw.1]
      decide
    have hy3 : ((begun T.st T.g G).oracles[3]?).map (·.shape) =
        some (shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 1) := by
      have k₁ := orc_O3
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy3
    have wM := wordsAt_member (K1.qAt Zp Np) hQf (jobOmega ⟨K1.qAt Zp Np, 0⟩) (Or.inr ⟨rfl, rfl⟩) 1
      hk1 _ rfl ⟨sendPlace 5, 0⟩ _ (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none m.st.input
      (restFront (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest m)
      (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input, ρ.shared.take 1, ()⟩ : State Ask Unit) (hv
          1)
      (coinsE cO.1.1).toArray (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none) 1
          rfl
      (carriedCoins (jobAtOmega (X := X₀) ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest
        (stretches _ c.2.2)) sc1 (begun T.st T.g G) (layoutOf T.st G) 3 hf3 y hy hys
      (by rw [hcd]; rfl)
      (fun hpos => absurd hpos (by
        show ¬ 0 < ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 1 default).shape.mainRows
        rw [hs1O, hnoSp]
        exact Nat.lt_irrefl 0)) (fun _ => zO1) pt i (by rw [hts]; exact hi)
    have rO := rowsO_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input) csU
        (coinsE cO.1.1).toArray)
      (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input) (ρ.shared.take 1) (coinsE cO.1.1).toArray
      (by rw [sOs, hw.1]) hs0O hs1O hSh.omega hnoSp hp1 hpt (fun _ _ => rfl) rfl rfl 1 hk1 pt i
    refine Eq.trans ?_ wM.symm
    rw [rO]
    show (if 0 + 2 ≤ 3 ∧ 3 < 0 + 2 + (parO (K1.qAt Zp Np)).sent.size then _ else _) = _
    rw [if_pos ⟨by omega, by
      have e : (parO (K1.qAt Zp Np)).sent.size = 2 := by
        rw [Desc.K14.Law.parK1_sent]
        exact hw.1
      rw [e]
      decide⟩]
    rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.rounds_in_front_O
#print axioms ProofFile.Honest.K12.Sim2.tie_at_run_O
