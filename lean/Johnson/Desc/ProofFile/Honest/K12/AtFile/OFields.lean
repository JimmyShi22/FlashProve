-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OFields.lean: the five fields of `K12AtO` (K12/Own/SaysYesOwn.lean) at the
proximity test on G_omega, at a stand of the proof file's shared thread at border 10.

  `rounds_head_O`, `laid_head_O`   the seated test's rounds are the written ones and those of `laidOf`
  `opensFit_head_O`   `OpensFit` at every job at the seated place whose first fold sends its own table
  `enters_at_ten`   at a stand whose field holds the columns that the thread's fold read, the seat's way in
                 is the job's state on entry (`doorOmegaF`). General in the thread
  `agree_head_O`   the two parts' readers agree at the coins that the frame lends
  `jobAtSeatO`, `oldAtO_head`   `OldAtO` (K12/Own/ColsTermOwn.lean): the job's trees 0 and 1 are the sending's own,
                 column for column; tree 2 is the next that the chain sends
  `fresh_head_O`, `opens_head_O`   tree 2 shows what round 1 lists; so `K12AtO.opens`
  `accepts_head_O`   the decision accepts what the term shows, at every list that can be sampled, where
                 `SaysAt` holds

By what. `door_of_opened` (K12/DoorOpened.lean); `agree_of_tiesO_letter` (K12/AgreeAtKey.lean),
`tiesO_at_laid` (AtFullSide/K12/TiesOwnAtLaid.lean); `col_of_send`, `cut_of_cover`, `shapes_O` (TreesSentBeforeTestAtU.lean),
`tree0_lent_head_Omega`, `tree1_lent_head_Omega` (K12/CutOfBookAtHead.lean); `fresh_tree_atOmega`, `treeAt_own`
(K12/Own/ColsTermOwn.lean); `accepts_of_plan_own` (K12/Own/AcceptsOwn.lean), `shapeAsks_of_front_own`,
`dataAsks_of_one_own`, `dataThree_of_front_own`, OAtHead.lean's lines.

The premise hfield of `enters_at_ten`: the field holds just the columns that the fold in `Thread.Made` read. A letter
that keeps the field by the thread's own tables gives it, with nothing in front of the chain's own columns:
that is all this file asks of a letter.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `enters_at_ten`, `oldAtO_head`, `opens_head_O` stand at a stand of `Thr`; the
  first is a tie of the door to the run's columns; `agree_head_O` stands at coins lent.
- `accepts_head_O` has `SaysAt` as a premise: what the rows taken in say of the words is not shown here.
- That a stand is reached is not said.
- wts, rnd are the readers of the thread's witness: the job at other readers is no such tie.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OCuts
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesSentBeforeTestAtU
import Johnson.Desc.ProofFile.Honest.K12.Own.SaysYesOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.AcceptsOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.DataThreeOwn
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import AtFullSide.K12.TiesOwnAtLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendTable sendingPart witOf treesU columnOf readsBelow_mono
  jobOmega_readsBelow)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Own (K12AtO OldAtO fresh_tree_atOmega treeAt_own shapeAsks_of_front_own
  dataAsks_of_one_own dataThree_of_front_own accepts_of_plan_own pass_of_five)
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks noDigest)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St blocks first frontBlock)
open Desc.K14.Honest (Like)
open Johnson.G (proofSendsFull codesFull2)
open H2K.Member (piOFull)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF colsOpened door_of_opened sentOf SaysAt
  bookCutsOmega askOf vecAt tsLenOf written_at_head qAt_written nums_head_O planOk_head_O shape_head_OmegaF
  colsMany plainMany rowsMu_many tree0_lent_head_Omega tree1_lent_head_Omega)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **Under the head the seated test's rounds are the written ones.** -/
theorem rounds_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds = (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds := by
  refine Option.some.inj ?_
  rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ (planOk_head_O h hO),
    ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _
      VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan, nums_head_O h hO]

/-- The block's rounds are those of `laidOf`. -/
theorem laid_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (H2K.JointK.laidOf pO).map (·.1) = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds :=
  (H2K.Sw.k12_rounds guardedProximityTestParts pO (planOk_head_O h hO)).symm

/-- **`OpensFit` at every job at the seated place** whose first fold sends its own table. -/
theorem opensFit_head_O {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (J : TestJob W X) (hJ : J.p = pO) (hfr : J.fresh.isNone = true) :
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds [22, 13, 13]
      (fun k => srcO.getD k (.own 0)) 7 :=
  opensFit_of_B _ _ _ _ _ (by
    rw [hfr, hJ, rounds_head_O h hO, congrArg (·.stages) (nums_head_O h hO)]
    exact opensFit_O)

section
variable {Cl V Pb W₀ Rc X₀ : Type} {Bk : ProverCoinCounts}

/-- **At a stand at border 10, whose field holds the columns that the fold read, the seat's way in is the
job's state on entry.** -/
theorem enters_at_ten (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (c : OnBytes.Model.Verify.Chains) (Q : P14) (sentU : Array OracleNotice)
    (bs : List (Block St Unit)) (pU : P12)
    (hpre : List.Forall₂ Like (T.bs.take 10) (frontBlock c ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)])))
    (hah : T.ahead = []) (hft : T.ft = 0)
    (hbeg : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes w.key)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E)
    (hfield : ∀ cols, T.colsTo 10 m E = .ok cols → m.opened = some cols) :
    VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) s =
      .ok (doorOmegaF Q sentU bs pU (fun w => w.key) colsOpened m.st.input (frontOf m)) := by
  obtain ⟨-, -, -, -, made, -, -⟩ := u
  obtain ⟨-, -, -, -, s₀, cols, hbeg', hcols, hfold⟩ := made
  obtain rfl := hbeg _ _ _ _ hbeg'
  have hfront : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  have hfold' : foldBlocks 0 (T.bs.take 10) (first Q.codes m.st.input.key) m.seen cols =
      .ok (s, [], []) := by
    have e := hfold
    rw [hfront, List.drop_zero, hft] at e
    exact e
  exact door_of_opened c Q sentU bs pU (T.bs.take 10) hpre m.st.input.key m.seen cols s hfold'
    (fun w => w.key) m.st.input (frontOf m) rfl rfl (hfield cols hcols)

end

/-- **`K12AtO.agree` at the job at the seated place**, at every coin that the frame lends, at whatever book
the maker returns. -/
theorem agree_head_O {V W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (A₀ : ProofFile.Honest.K14.SendPub) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E))
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest : Part V _ _),
      restPart (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest])
    (hc : lendRow Bk rows look pO.place
      [(firstPart (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest : Part V _ _),
        restPart (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest w fr
      (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest.s₀
      (firstRd (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest c.1)
      (restCoins (jobAtOmega A₀ pO door weights rand omega?).toRun.toTest c.2.1) :=
  agree_of_tiesO_letter _ rfl Bk rows look c hc w fr
    (by
      show Own.tiesOB Bk pO.place 2 = true
      rw [place_of_four hO]
      exact AtFullSide.K12.tiesO_at_laid h.scope h.laid hB)
    fun mem mem' e => rowsMu_many _ _ w fr mem mem' e

section
variable {W₀ Rc X₀ S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- The job at the seated place of the test on G_omega, at the thread's readers. -/
abbrev jobAtSeatO (Zp : ProofFile.Pub) (Np : H2U.Places4) (pO : P12)
    (door : Common W₀ Rc TableKey → Front X₀ → T12) (wts : W₀ → Weights) (rnd : Rc → TableRand) :
    TestJob (Common W₀ Rc TableKey) X₀ :=
  (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door (fun c => wts c.w₀) (fun c => rnd c.rc) none).toRun.toTest

set_option maxHeartbeats 1000000 in
/-- **`OldAtO` at the job at the seated place**, at a stand of the thread at 10. -/
theorem oldAtO_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (hb : treesTo T.bs 10 = 7) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hf1 : 1 ≤ T.fixed (.own 1)) (hu : treesU (K1.qAt Zp Np) = 1)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hcuts : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E)
    (c : RowCoins [(firstPart (jobAtSeatO Zp Np pO door wts rnd) : Part V _ _),
      restPart (jobAtSeatO Zp Np pO door wts rnd)])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) pO.place
      [(firstPart (jobAtSeatO Zp Np pO door wts rnd) : Part V _ _),
        restPart (jobAtSeatO Zp Np pO door wts rnd)] 0 = .ok c) :
    OldAtO E ((jobAtSeatO Zp Np pO door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1).mem
        ((jobAtSeatO Zp Np pO door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1)))
      (fun j => srcO.getD j (.own 0)) 2 := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hO0 : ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes
      (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [22, 13] := by
    have q := shapes_O
    rw [hx₀] at q
    simp only [Option.all_some] at q
    rw [qAt_written Wr Np]
    exact beq_iff_eq.1 q
  have arm1 : T.table (.own 1) = sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩)
      (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 0 := by
    rw [htb]
    show (if 1 < treesU (K1.qAt Zp Np) then _ else if 1 < 3 then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), hu]
  have arm2 : T.table (.own 2) = sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩)
      (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 1 := by
    rw [htb]
    show (if 2 < treesU (K1.qAt Zp Np) then _ else if 2 < 3 then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), hu]
  have dep1 : ∀ k' w' h', (T.table (.own 1) k' w' h').2.logLength = 22 := fun k' w' h' => by
    rw [arm1, sendTable_depth _ _ _ 1 0 k' w' h' (cut_of_cover k' _ _ c5)
      (by have e := congrArg List.length hO0; simp only [List.length_map, List.length_cons, List.length_nil] at e; omega), hO0]
    rfl
  have dep2 : ∀ k' w' h', (T.table (.own 2) k' w' h').2.logLength = 13 := fun k' w' h' => by
    rw [arm2, sendTable_depth _ _ _ 1 1 k' w' h' (cut_of_cover k' _ _ c5)
      (by have e := congrArg List.length hO0; simp only [List.length_map, List.length_cons, List.length_nil] at e; omega), hO0]
    rfl
  obtain ⟨ownO, hOc⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c5)
  have hl := lendRow_second hc
  have hin : ∀ n, n < 3 → Fmt.TreeSource.own n ∈ T.hand 10 := fun n hn => by
    show _ ∈ T.taken ++ (List.range (treesTo T.bs 10)).map Fmt.TreeSource.own
    rw [ht, hb]
    exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
  obtain ⟨d0, d1, -⟩ := depths_head_O h hO
  have hsent : E.sent = 7 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := u
    rw [h3, hb]
  refine ⟨fun j hj hn n' hm => ?_, fun j hj hn x hx => ?_, ?_⟩
  · have hj3 : j < 3 := hj
    have h' : srcO.getD j (.own 0) = .own n' := hm
    rw [hsent]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · injection h' with h''
      omega
    · injection h' with h''
      omega
  · have hj3 : j < 3 := hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · have hx' : x < 2 ^ 22 := by
        rw [← d0]
        exact hx
      have hv : vecAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 0
          (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀) (fun c => rnd c.rc)) none m.st.input
          (frontOf m) = (jobOmega ⟨K1.qAt Zp Np, 0⟩).data
            ⟨witOf (K1.qAt Zp Np) wts rnd m.st.input, m.st.heard.take (T.fixed (.own 1)), ()⟩ 0 :=
        congrFun (readsBelow_mono (jobOmega_readsBelow ⟨K1.qAt Zp Np, 0⟩) hf1 _ m.st.heard).symm 0
      refine (col_of_send T (hin 1 (by omega)) _ _ _ 0 22 arm1 dep1 (width_head_O h 0).1
        u ownO hOc hx').trans ?_
      exact (tree0_lent_head_Omega h 0 Bk _ _ _ rfl pO _ _ _ none ownO hOc m.st.input (frontOf m) _
        x hO c.2.1 hl hcuts hv).symm
    · have hx' : x < 2 ^ 13 := by
        rw [← d1]
        exact hx
      refine (col_of_send T (hin 2 (by omega)) _ _ _ 1 13 arm2 dep2 (width_head_O h 0).2
        u ownO hOc hx').trans ?_
      exact (tree1_lent_head_Omega h 0 Bk _ _ _ rfl pO _ _ _ none ownO hOc m.st.input (frontOf m) _
        x hO c.2.1 hl hcuts).symm
  · show (Fmt.TreeSource.own 7 : Fmt.TreeSource) = _
    rw [hsent]

/-- **Tree number 2 of the job shows what round 1 lists.** -/
theorem fresh_head_O (J : TestJob (Common W₀ Rc TableKey) X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (hJ : J = jobAtSeatO Zp Np pO door wts rnd) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: rest) (w : Common W₀ Rc TableKey) (fr : Front X₀) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (x : ℕ) :
    ((J.trees₀ w fr C.mem (J.first w fr C)).getD 2 (0, fun _ => [])).2 x = treeAt J w fr C D 1 x := by
  subst hJ
  have e1 := fresh_tree_atOmega ⟨K1.qAt Zp Np, 0⟩ pO door (fun c => wts c.w₀) (fun c => rnd c.rc) none
    w fr C.mem ((jobAtSeatO Zp Np pO door wts rnd).first w fr C) x
  have e2 := congrFun (treeAt_own (jobAtSeatO Zp Np pO door wts rnd) w fr C D a rest hst rfl) x
  have hs : (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door (fun c => wts c.w₀) (fun c => rnd c.rc) none).s₀ = a := by
    show (jobAtSeatO Zp Np pO door wts rnd).p.nums.stages.headD default = a
    rw [hst]
    rfl
  rw [hs] at e1
  exact e1.trans e2.symm

set_option maxHeartbeats 1000000 in
/-- **`K12AtO.opens` at the job at the seated place.** -/
theorem opens_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (hb : treesTo T.bs 10 = 7) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hf1 : 1 ≤ T.fixed (.own 1)) (hu : treesU (K1.qAt Zp Np) = 1)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hcuts : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : (jobAtSeatO Zp Np pO door wts rnd).p.nums.stages = a :: rest)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E)
    (c : RowCoins [(firstPart (jobAtSeatO Zp Np pO door wts rnd) : Part V _ _),
      restPart (jobAtSeatO Zp Np pO door wts rnd)])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) pO.place
      [(firstPart (jobAtSeatO Zp Np pO door wts rnd) : Part V _ _),
        restPart (jobAtSeatO Zp Np pO door wts rnd)] 0 = .ok c) (ds : List Fmt.Drawn) :
    ∃ depths src₀,
      ((jobAtSeatO Zp Np pO door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1).mem
        ((jobAtSeatO Zp Np pO door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1))).map (·.1) = depths ∧
      OpensFit (jobAtSeatO Zp Np pO door wts rnd)
        (proximityTestKind guardedProximityTestParts (jobAtSeatO Zp Np pO door wts rnd).p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAtO E ((jobAtSeatO Zp Np pO door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1).mem
        ((jobAtSeatO Zp Np pO door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1))) src₀ 2 ∧
      ∀ x, x < 2 ^ (((jobAtSeatO Zp Np pO door wts rnd).trees₀ m.st.input (frontOf m)
          (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1).mem
          ((jobAtSeatO Zp Np pO door wts rnd).first m.st.input (frontOf m)
            (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1))).getD 2 (0, fun _ => [])).1 →
        (((jobAtSeatO Zp Np pO door wts rnd).trees₀ m.st.input (frontOf m)
          (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1).mem
          ((jobAtSeatO Zp Np pO door wts rnd).first m.st.input (frontOf m)
            (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1))).getD 2 (0, fun _ => [])).2 x =
          treeAt (jobAtSeatO Zp Np pO door wts rnd) m.st.input (frontOf m)
            (restCoins (jobAtSeatO Zp Np pO door wts rnd) c.2.1) (byNo ds) 1 x := by
  have hsent : E.sent = 7 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := u
    rw [h3, hb]
  obtain ⟨d0, d1, d2⟩ := depths_head_O h hO
  refine ⟨[22, 13, 13], fun j => srcO.getD j (.own 0), ?_, ?_,
    oldAtO_head h hO T wts rnd JU JO own₀ door hb ht htb hf1 hu c5 hcuts u c hc,
    fun x _ => fresh_head_O (Zp := Zp) (Np := Np) (pO := pO) _ door wts rnd rfl a rest hst _ _ _ _ x⟩
  · show [Light.depthOf pO 0, Light.depthOf pO 1, (pO.nums.stages.headD default).Z.a] = [22, 13, 13]
    rw [d0, d1, d2]
  · rw [hsent]
    exact opensFit_head_O h hO _ rfl rfl

end

set_option maxHeartbeats 1000000 in
/-- **The decision accepts what the term shows**, at every list that can be sampled, where `SaysAt` holds. -/
theorem accepts_head_O {W X : Type} (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) :
    let A := jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U key cols) weights rand omega?
    drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true →
    SaysAt A w fr C →
    ∃ t', (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).decide (A.toRun.toTest.rec₀ w fr)
      ((testAll A.toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll A.toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  intro A hd hs
  obtain ⟨Dp, S⟩ := frontAsksO_head h hO bs hb A.toRun.toTest rfl key cols rfl w fr
  have he : A.p.early = true := H2K.JointK.early_of_planOk _ (planOk_head_O h hO)
  have hN : ProofFile.Honest.Sh.testSh (A.rec₀ w fr) = headShape Zp Np :=
    shape_head_OmegaF h bs hb key cols w fr
  have h5 : Own.frontOwnFiveB A.p codesFull2 (ProofFile.Honest.Sh.testSh (A.rec₀ w fr)) = true := by
    rw [hN]
    exact five_head_O h hO
  have hts : Dp.ts.length = 3 := by
    rw [ts_of_front_own A.toRun.toTest w fr codesFull2 Dp he h5 S]
    show tsLenOf pO (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = 3
    rw [hN]
    exact ts_head_O h hO
  have hP : Own.planOB A.p codesFull2 Dp.ts.length = true := by
    rw [hts, ← ProofFile.Honest.K12.Light.codes_two]
    exact planOB_head_O h hO
  obtain ⟨a, next, rest, hs₀⟩ := stages_O
  have hst : A.toRun.toTest.p.nums.stages = a :: next :: rest := by
    show pO.nums.stages = _
    rw [nums_head_O h hO]
    exact hs₀
  have hd' : drawsFit ((H2K.JointK.laidOf A.p).map (·.1)) ds = true := by
    show drawsFit ((H2K.JointK.laidOf pO).map (·.1)) ds = true
    rw [laid_head_O h hO]
    exact hd
  have F := formAsks_of_draws A.toRun.toTest w fr C ds a next rest hst
    (formPub_of_B A.p a next rest hst (formPubB_head_O h hO)) hd'
  have SA := shapeAsks_of_front_own A.toRun.toTest w fr C (byNo ds) codesFull2 Dp hP S F
  have hS : ProofFile.Honest.K12.Light.manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (A.rec₀ w fr))) = true := by
    rw [hN]
    exact many_head_O h hO _ weights rand omega?
  obtain ⟨t1, t2, t3⟩ := dataThree_of_front_own A w fr codesFull2 Dp he (pass_of_five _ _ _ h5) S hS C
  have DF : DataFront A.toRun.toTest w fr C Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) :=
    ⟨t1, t2, t3, hs⟩
  have Dt := dataAsks_of_one_own A.toRun.toTest w fr C (byNo ds) Dp _ _ S.door S.noMask S.tidy
    S.plainRows (bat_head_O h hO) F.bat DF
  exact accepts_of_plan_own A.toRun.toTest w fr C (byNo ds) codesFull2 Dp _ _ (own_head_O h hO) hP SA F Dt

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.rounds_head_O
#print axioms ProofFile.Honest.K12.AtFile.laid_head_O
#print axioms ProofFile.Honest.K12.AtFile.opensFit_head_O
#print axioms ProofFile.Honest.K12.AtFile.enters_at_ten
#print axioms ProofFile.Honest.K12.AtFile.agree_head_O
#print axioms ProofFile.Honest.K12.AtFile.oldAtO_head
#print axioms ProofFile.Honest.K12.AtFile.fresh_head_O
#print axioms ProofFile.Honest.K12.AtFile.opens_head_O
#print axioms ProofFile.Honest.K12.AtFile.accepts_head_O
