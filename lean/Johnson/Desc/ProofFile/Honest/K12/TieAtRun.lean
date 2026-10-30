-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TieAtRun.lean

OF WHAT KIND IT IS. A tie between what one part is handed of a run's values and what another part is
handed of them. It names no value and states no law over random values: a tie between terms.

A conditional: nothing here shows that ready or runC returns, that the part is called, or that the
frame lends.

The fifth field of `LeftAt` (OnFreeTAtHeadULeft.lean), the tie of the words, at a run of the frame's
walking prover under the head `P5J.AtMg`: on the tables of the members of the group under the test
on G_u, the honest words at `heldAt` (Sim/ShownAtRun.lean) are the words that the test's job makes
of its own rows at the carried coins. One definition with code; five theorems.

  `ellsB`, `ellsB_plan`, `ells_real`, `ells_bite`, `ells_head`: a public test on two codes' message
      lengths; it reads the codes and the shape alone; it accepts at the typed sizes and can fail
      (two evaluations in Lean's kernel); it accepts at the shared chain's own plan under the head.
  `tie_at_run`: the statement.

The premises of `tie_at_run`, sorted. Public: the head, hb, h9, hσ (the side's place is the seated
test's). On the job: its first member carries no vector of its own (hJ). On the filling and the
book: hR, S, the two lendings lU and lO. On the run: hrun, hc, the fold's return hfold, the view's
rounds hW. THE TIE OF VALUES: hbk (`bookCutsU`, CutOfBookAt.lean: a test with code on the book's
entries). No premise on the prover's halves.

The chain, link by link. The state behind the eight: the group's members in order, the messages'
shapes, the codes (`behind_fold`, PubAtDoor.lean; `facts_at_head`). Left: the library's `words2`
unfolded at the two members' numbers; the shared rounds' authors' `rowsU_read`, `rowsO_read`
(Honest/K14/SendingsRows.lean) from right to left, at `heldAt`. Right: `wordsAt_member`
(WordsOfMember.lean), behind the test's beginning (the library's `begun_shape`, `begun_codes`,
`begun_has`, `begun_rowBits`, `begun_placeBits`), the finds by the library's `find_two`
(Johnson/Desc/K12/Coin/MembersFound.lean). The carried coins are the senders' own cuts: `cuts_atU`
(CutOfBookAt.lean), `own_of_lendPart` (Sim/SenderInFront.lean), the frame's authors'
`lendRow_cons_ok`, `look_shared`. One vector on both sides: `same_vector`, `data_same`
(Sim/SameVectorAtRun.lean) over the shared rounds' authors' `jobOmega_readsBelow`
(Honest/K14/SendingsPaid.lean). The stand: `played_at_run` (Sim/PlayedAtRun.lean), `heard_at_stand`,
`challenge_at`, `lengths_eight` (Sim/ShownAtRun.lean). That o_u has no mask row and o_sp no main
row: `sendShapes_head` (HeldAtCommitter.lean) and those authors' `sp_noMain`.

Limits.
- hbk is paid at the maker's book, under the head, in the side library (`bookCutsU_head`,
  AtFullSide/K12/CutsAtHead.lean); not called here.
- hσ is a premise here; under the head it follows from the side's own cut and h9 (`place9_head`,
  TreesAtHeadUPub.lean); not called here.
- The reader of the input is the job's own (`askOf` at the job's two readers): a caller whose
  senders have another reader must show that the two are one.
- The fold's fresh table, the second message of "send o_u", is no member of the group, and nothing
  is said of it.
- `ells_bite` is at a made-up plan with no code: it shows that the test can say no; it parts no two
  plans of the library's. `ells_real` is a sentence on all values of an optional value: that the
  typed sizes are there the library has with no premise (`real_members`,
  Johnson/Desc/K1/Law/CondReal.lean); here `ells_head` has it from `written_at_head`.
- The test on G_u alone. Of the walk (`runC`). The full size alone.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.WordsOfMember
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadULeft
import Johnson.Desc.ProofFile.Honest.K12.HeldAtCommitter
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt
import Johnson.Desc.ProofFile.Honest.K12.PubAtDoor
import Johnson.Desc.ProofFile.Honest.K12.SendFitAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.SameVectorAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.SenderInFront
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Desc.First.Close.Law.BatOwn
import Johnson.Desc.First.Close.Law.LayBegun
import Johnson.Desc.K12.Coin.MembersFound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle ceilLog2)
open OnBytes.Slice (rdE ofE readE lst)
open OnBytes.Means (layoutOf realRows tableSize)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks first withU)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest
open ProofFile.Honest.K14 (Ask SendPub jobU jobOmega sendPlace liftSend sendingPart elems elems_one
  rowsU_read rowsO_read sp_noMain jobU_par takesOf jobOmega_readsBelow)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **A test with code on two message lengths**: o_u's base code's and o_sp's mask code's message
length is the power of two that its logarithm says. Of o_u's mask code and o_sp's base code nothing
is tested: `wordsAt_member` (WordsOfMember.lean) asks a code's length only where its table has a
row. -/
def ellsB (A : SendPub) : Bool :=
  (((jobU A).Q.codes.base.getD (shapeAt (jobU A) 0).code default).ell ==
    2 ^ ((jobU A).Q.codes.base.getD (shapeAt (jobU A) 0).code default).logEll) &&
  (((jobOmega A).Q.codes.mask.getD (shapeAt (jobOmega A) 1).maskCode default).ell ==
    2 ^ ((jobOmega A).Q.codes.mask.getD (shapeAt (jobOmega A) 1).maskCode default).logEll)

/-- The test reads of the public data the codes and the shape alone. -/
theorem ellsB_plan (A : SendPub) : ellsB A = ellsB (planOf A.P.codes A.P.S) := rfl

/-- It accepts at the typed sizes over a proof file's own codes. An evaluation in Lean's kernel. -/
theorem ells_real : (realSized.all fun q => ellsB (planOf q.2 q.1.shape)) = true := by
  decide +kernel

/-- It can fail: with no code at all it says no. An evaluation in Lean's kernel. -/
theorem ells_bite : ellsB (planOf ⟨#[], #[]⟩ default) = false := by decide +kernel

/-- It accepts at the shared chain's own plan, under the head. -/
theorem ells_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : ellsB ⟨K1.qAt Zp Np, 0⟩ = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := ells_real
  rw [hx] at k
  have k' : ellsB (planOf codesFull2 x.shape) = true := k
  rw [ellsB_plan, qAt_written Wr Np]
  exact k'

/-- **The tie of the words at a run: `LeftAt`'s fifth field.** Under the head, at a run at which the
second part of the test on G_u is called, at the job of `jobHeadU` whose first member carries no
vector of its own: where the side's place is the seated test's (hσ) and the book passes the public
test `bookCutsU` (CutOfBookAt.lean; hbk): at the run's stand m and carried blocks ca, at the
state d8 that the description's fold over the eight returns at the shared view, at W's first round,
and at the coins cU, cO that the book lends the two sendings' parts: on the tables of G_u's members,
the honest words at `heldAt` of the input and of cU's and cO's coins are the words that the job's
own rows make at the carried coins.
OF WHAT KIND IT IS: a tie between what one part is handed of a run's values and what another part is
handed of them. -/
theorem tie_at_run {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hJ : J = (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand
      none).toRun.toTest)
    (Js : SimJob TableKey) (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hσ : σ.block.place = (fourOf Np).U.place)
    (hbk : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true)
    (W : Seen8) (d8 : St) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn)
    (cU : RowCoins
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)])
    (cO : RowCoins
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)])
    (hfold : foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
      r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest₈, more))
    (hW : r.run.views.2.1.rounds =
      [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈)
    (lU : lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 2)
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cU)
    (lO : lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 5)
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO) :
    ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
    ∀ G, d8.st.groups[d8.loc.gU]? = some G →
      WordsTied d8.st d8.loc.gU G
        (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
          (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand R.common)
            (coinsE cU.1.1).toArray (coinsE cO.1.1).toArray))
        (layoutOf d8.st G)
        (plainMany (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand none)
          m.st.input (restFront J m) (carriedCoins J (stretches _ ca))) := by
  intro m ca hm hca G hG oM ho pt i hi
  subst hJ
  -- public facts under the head
  obtain ⟨hSN, hMA, hU⟩ := facts_at_head h
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have hSh := sendShapes_head h
  have hQf := sendingsFit_head h
  have h2 : (sentOf (K1.qAt Zp Np).S).size = 2 := hP.goesTwo
  have hw : (Desc.K14.withOmega (K1.qAt Zp Np).S).size = 2 ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[0]? =
        some ⟨(K1.qAt Zp Np).S.omega, (K1.qAt Zp Np).S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[1]? =
        some ⟨(K1.qAt Zp Np).S.sharedSplit, (K1.qAt Zp Np).S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.two
  have hE := ells_head h
  unfold ellsB at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  obtain ⟨lU0, zO1⟩ := hE
  -- the state behind the eight
  have B := behind_fold (K1.qAt Zp Np) _ hb hSN hMA _ hU x.pub.key _ _ _ hfold
  have B' : Behind (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) d8 := B
  have hg0 := B'.gU
  rw [hg0] at hG ⊢
  have hpub := B'.mid.g0
  rw [hG] at hpub
  have hmem : G.members = #[0, (sentOf (K1.qAt Zp Np).S).size + 1] :=
    congrArg (·.members) (Option.some.inj hpub)
  rw [h2] at hmem
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
    have t := (Sp.to1 u'.front.front.front.front.front.front.front).point
    have e : W'.view.r1 = W.view.r1 := by
      simp only [Seen8.view, eW]
    rw [← e]
    exact t
  -- the nine in front declare eight rounds
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  have h8 : (pre.flatMap (·.rounds)).length = 8 := by
    rw [epre]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
      l8.rounds, n1, n2, n3, n4, n5, n6, n7, n8]
    rfl
  -- the stand in front of the second part
  obtain ⟨a₂, zN, m'', ha, hzN, hzl, hzm, hm''⟩ :=
    played_at_run h.laid.planOk hR hrun σ _ pre t _ _ S rfl hc
  obtain rfl : m = m'' := Option.some.inj (Except.ok.inj (hm.symm.trans hm''))
  obtain ⟨hheard, hinp, -⟩ := heard_at_stand hrun _ a₂ zN m ha hzN hzl hzm
  have hLen : m.st.heard.length = (pre.flatMap (·.rounds)).length +
      firstLen (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand
        none).toRun.toTest.p.nums.stages := by
    rw [hheard, walk_len _ _ _ a₂ zN hzN, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) S.fits)
  have c0 := challenge_at hrun _ a₂ zN m ha hzN hzl hzm 0
    (Nat.lt_of_lt_of_le (by decide : 0 < 8) (h8 ▸ Nat.le_add_right _ _))
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
  -- the same vector, at both members
  have hvU := same_vector ⟨K1.qAt Zp Np, 0⟩ (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand)
    (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand
      none).toRun.toTest m
    { m with st := { m.st with heard := ρ.shared.take 1 } } ρ.shared _ 1 hheard rfl rfl
    Nat.zero_lt_one (by
      rw [hLen, h8]
      show 0 + _ < 8 + _
      omega)
  have hvO : vecAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 1 (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none
    m.st.input
      (restFront (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
        rand none).toRun.toTest m) =
      (jobOmega ⟨K1.qAt Zp Np, 0⟩).data (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input,
        ρ.shared.take 1, ()⟩ : State Ask Unit) 1 := by
    show (jobOmega ⟨K1.qAt Zp Np, 0⟩).data (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input,
      m.st.heard.take (m.st.heard.length -
        firstLen (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
          rand none).toRun.toTest.p.nums.stages),
      ()⟩ : State Ask Unit) 1 = _
    refine congrFun (data_same (jobOmega_readsBelow ⟨K1.qAt Zp Np, 0⟩) _ _ _ ?_) 1
    show List.take 1 _ = List.take 1 _
    obtain ⟨n, hn⟩ : ∃ n, m.st.heard = ρ.shared.take n := ⟨_, hheard⟩
    have hn1 : 1 ≤ n := by
      have e := List.length_take_le n ρ.shared
      rw [← hn, hLen, h8] at e
      omega
    rw [hLen, h8, Nat.add_sub_cancel, hn, List.take_take, List.take_take, List.take_take,
      Nat.min_eq_left (by decide : 1 ≤ 8), Nat.min_eq_left hn1, Nat.min_self]
  -- what the second part is lent, and the two cuts
  obtain ⟨c, hl, rfl⟩ := exMap_ok (show (lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨σ.block.place, 1⟩
    (restPart (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand
      none).toRun.toTest :
      Part Empty (Common W₀ Rc TableKey) X₀)).map (·.2.2) = .ok ca from hca)
  rw [hσ, look_shared] at hl
  have hUc : (sharedLook Bk k.shared ⟨sendPlace 2, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (jobU ⟨K1.qAt Zp Np, 0⟩).Q.codes (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent (jobU ⟨K1.qAt Zp Np,
        0⟩).sort) = some cU.1.1 :=
    own_of_lendPart (lendRow_cons_ok lU).1
  have hOc : (sharedLook Bk k.shared ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (takesOf (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent (jobOmega
        ⟨K1.qAt Zp Np, 0⟩).sort) =
        some cO.1.1 :=
    own_of_lendPart (lendRow_cons_ok lO).1
  obtain ⟨sc0, sc1, -⟩ := cuts_atU Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨K1.qAt Zp Np, 0⟩
    (fourOf Np).U _
    weights rand none cU.1.1 hUc cO.1.1 hOc c hl hbk (fits_at_head h).2.1
  -- the shapes, the sizes, the finds
  rw [← hinp]
  have eQ := jobU_par (Q := (K1.qAt Zp Np)) hU 0
  have sUs : (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent = (sentOf (K1.qAt Zp Np).S) := by
    rw [eQ]
    exact Desc.K14.Law.parK1_sent _ 2 _ _
  have sOs : (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent = Desc.K14.withOmega (K1.qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (K1.qAt Zp Np) 5 _ _
  have hs0U : ((jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape = (K1.qAt Zp Np).par.S.fold.u
    := by
    rw [eQ]
    exact (shapeAt_of_get (parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) 0
      ⟨(K1.qAt Zp Np).par.S.fold.u, (K1.qAt Zp Np).par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hU)).1
  have hs0O : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape = (K1.qAt Zp
    Np).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 0
      ⟨(K1.qAt Zp Np).par.S.omega, (K1.qAt Zp Np).par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 1 default).shape =
      (K1.qAt Zp Np).par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q 1
      ⟨(K1.qAt Zp Np).par.S.sharedSplit, (K1.qAt Zp Np).par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have hnoSp : (K1.qAt Zp Np).par.S.sharedSplit.mainRows = 0 := sp_noMain ⟨hP, hBU, hBO⟩
  have hp1 : elems (heardFrom (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input, ρ.shared.take 1,
    ()⟩ : State Ask Unit) 0 1) = Desc.K14.drawn W.view.r1 := by
    rw [ht1]
    exact elems_one _
  have hts : ∀ o' pt', tableSize (OnBytes.Slice.begun d8.st 0 G) o' pt' = tableSize d8.st o' pt' :=
    fun o' pt' => by
      unfold tableSize OnBytes.Statement.tableBits
      rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd : (OnBytes.Slice.begun d8.st 0 G).codes = (K1.qAt Zp Np).codes :=
    (OnBytes.Slice.begun_codes d8.st 0 G).trans B'.mid.codes
  have hshape : ∀ o' : ℕ,
      ((OnBytes.Slice.begun d8.st 0 G).oracles[o']?).map (fun y : Oracle => y.shape) =
      (((sentOf (K1.qAt Zp Np).S) ++ Desc.K14.withOmega (K1.qAt Zp Np).S)[o']?).map
        (fun n : OracleNotice => n.shape) := fun o' => by
    rw [OnBytes.Slice.begun_shape, ← Array.getElem?_map, B'.mid.shapes, Array.getElem?_map]
  obtain ⟨hf0, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two (layoutOf d8.st G) 0 3 (by decide)
    (show G.members = #[0, 3] from hmem)
  have hoo : oM = 0 ∨ oM = 3 := by
    rw [hmem] at ho
    simpa using ho
  rcases hoo with rfl | rfl
  · -- o_u
    have hk0 : 0 < (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent.size := by
      rw [sUs, h2]
      decide
    obtain ⟨y, hy, hys⟩ : ∃ y, (OnBytes.Slice.begun d8.st 0 G).oracles[0]? = some y ∧
        y.shape = shapeAt (jobU ⟨K1.qAt Zp Np, 0⟩) 0 := by
      have e := hshape 0
      rw [Array.getElem?_append_left (by rw [h2]; decide), withU_zero hU] at e
      obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 e
      exact ⟨y, hy, hys.trans hs0U.symm⟩
    have wM := wordsAt_member (K1.qAt Zp Np) hQf (jobU ⟨K1.qAt Zp Np, 0⟩) (Or.inl ⟨rfl, rfl⟩) 0 hk0
      _ rfl
      ⟨sendPlace 2, 0⟩ _ (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none m.st.input
      (restFront (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
        rand none).toRun.toTest m)
      (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input, ρ.shared.take 1, ()⟩ : State Ask Unit) hvU
        (coinsE cU.1.1).toArray
      (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand none) 0
        rfl
      (carriedCoins (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
        rand none).toRun.toTest
      (stretches _ c.2.2)) sc0 (OnBytes.Slice.begun d8.st 0 G) (layoutOf d8.st G) 0
      hf0 y hy hys hcd (fun _ => lU0)
      (fun hpos => absurd hpos (by
        show ¬ 0 < ((jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 0 default).shape.maskRows
        rw [hs0U, hSh.u.noMask]
        exact Nat.lt_irrefl 0)) pt i (by rw [hts]; exact hi)
    have rU := rowsU_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input)
      (coinsE cU.1.1).toArray (coinsE cO.1.1).toArray)
      (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input) (ρ.shared.take 1) (coinsE cU.1.1).toArray
      (by rw [sUs, h2]) hs0U hSh.u hSh.mask hp1 hpt (fun _ _ => rfl) rfl rfl 0 hk0 pt i
    refine Eq.trans ?_ wM.symm
    rw [rU, eQ]
    show (if 0 ≤ 0 ∧ 0 < 0 + (parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)).sent.size then _ else
      _) = _
    rw [if_pos ⟨Nat.le_refl _, by
      rw [Desc.K14.Law.parK1_sent, h2]
      decide⟩]
    rfl
  · -- o_sp
    have hk1 : 1 < (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.size := by
      rw [sOs, hw.1]
      decide
    obtain ⟨y, hy, hys⟩ : ∃ y, (OnBytes.Slice.begun d8.st 0 G).oracles[3]? = some y ∧
        y.shape = shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 1 := by
      have e := hshape 3
      rw [Array.getElem?_append_right (by rw [h2]; decide), h2] at e
      have e' : ((OnBytes.Slice.begun d8.st 0 G).oracles[3]?).map (fun y : Oracle => y.shape) =
          ((Desc.K14.withOmega (K1.qAt Zp Np).S)[1]?).map (fun n : OracleNotice => n.shape) := e
      rw [hw.2.2] at e'
      obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 e'
      exact ⟨y, hy, hys.trans hs1O.symm⟩
    have wM := wordsAt_member (K1.qAt Zp Np) hQf (jobOmega ⟨K1.qAt Zp Np, 0⟩) (Or.inr ⟨rfl, rfl⟩) 1
      hk1 _ rfl
      ⟨sendPlace 5, 0⟩ _ (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) none m.st.input
      (restFront (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
        rand none).toRun.toTest m)
      (⟨askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input, ρ.shared.take 1, ()⟩ : State Ask Unit) hvO
        (coinsE cO.1.1).toArray
      (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand none) 1
        rfl
      (carriedCoins (jobHeadU (X := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights
        rand none).toRun.toTest
      (stretches _ c.2.2)) sc1 (OnBytes.Slice.begun d8.st 0 G) (layoutOf d8.st G) 3
      hf3 y hy hys hcd
      (fun hpos => absurd hpos (by
        show ¬ 0 < ((jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent.getD 1 default).shape.mainRows
        rw [hs1O, hnoSp]
        exact Nat.lt_irrefl 0)) (fun _ => zO1) pt i (by rw [hts]; exact hi)
    have rO := rowsO_read (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1
      (heldAt (K1.qAt Zp Np) (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand m.st.input)
      (coinsE cU.1.1).toArray (coinsE cO.1.1).toArray)
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

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.ellsB
#print axioms ProofFile.Honest.K12.Light.ellsB_plan
#print axioms ProofFile.Honest.K12.Light.ells_real
#print axioms ProofFile.Honest.K12.Light.ells_bite
#print axioms ProofFile.Honest.K12.Light.ells_head
#print axioms ProofFile.Honest.K12.Light.tie_at_run
