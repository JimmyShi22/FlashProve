-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TreesSentBeforeTestAtU.lean: the trees that the test on G_u opens are the
sendings' own, column for column, at a stand of the thread at border 9: `OldAt` (K12/ColsTerm.lean): the
last conjunct of `K12At.opens`; and `K12At.opens` whole.

  `col_of_send`  at a stand, a tree in hand that a sending lays shows the sending's column. General in the
                 thread
  `shapes_U`, `shapes_O`   the depths of the sendings' trees at the written sizes: closed lines
  `oldAt_head_U`   `OldAt` at the job at the seated place, at own 0 and own 2
  `opens_head_U`   `K12At.opens`

By what. `tree0_lent_head_U`, `tree1_lent_head_U` (K12/CutOfBookAtHead.lean): the job's two trees are the
sendings' columns at the coins lent. `col_sent` (K12/TableIsColumn.lean): the table is that column. `Thr`'s
hand: what is in hand shows the thread's table. `opensFit_head_U` (OpensFitLines.lean).

The premises of `oldAt_head_U`. hb, ht, htb: three trees in front, none taken over, the table is
`tableShared`. hf1: own 0 is fixed behind the first challenge. c2, c5: the book covers the sendings. hcut: the
book's cuts at the place. c: the coins that the frame lends the two parts.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind `Thr` and ties a job's trees to the lent coins.
- wts, rnd are the readers of the thread's witness: the job at other readers is no such tie.
- Own 0 and own 2 of this job alone.
- A law on columns at hand: nothing of an accepted column.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensFitLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FieldsAtU
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAtHead
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.Sim.RestTiesAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub SendJob jobU jobOmega sendPlace sendTable sendTablesAt sendingPart witOf
  treesU columnOf readsBelow_mono jobU_readsBelow)
open ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light

/-- **At a stand, a tree in hand that a sending lays shows the sending's column.** -/
theorem col_of_send {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b n : ℕ}
    (hin : Fmt.TreeSource.own n ∈ T.hand b) (Jd : SendJob) (wit : W → K14.Ask) (pl : Place) (i dep : ℕ)
    (harm : T.table (.own n) = sendTable Jd wit pl 1 i)
    (hdep : ∀ k w h, (T.table (.own n) k w h).2.logLength = dep)
    (hw : widthFits Jd i = true) {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (u : Thr T b k s m E)
    (own : Cs (sendingPart Jd).takes)
    (hcut : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart Jd).takes = some own) {x : ℕ}
    (hx : x < 2 ^ dep) :
    colAt E.tree (.own n) x = columnOf Jd.Q.codes Jd.Q.sent
      (Jd.rows ⟨wit m.st.input, m.st.heard.take (T.fixed (.own n)), ()⟩ (coinsE own).toArray) i x := by
  obtain ⟨⟨-, hH⟩, -⟩ := u
  obtain ⟨pt, hE, -, hs⟩ := Thread.handAt_elim _ (hH _ hin)
  obtain ⟨hlen, hcol⟩ := Table.same_elim hs
  obtain ⟨Tt, hT, hc⟩ := col_sent Jd (Jd.rows ⟨wit m.st.input,
    m.st.heard.take (T.fixed (.own n)), ()⟩ (coinsE own).toArray) i hw
  have htab : (T.tableAt (.own n) k m).2 = Tt := by
    show (T.table (.own n) k m.st.input (m.st.heard.take (T.fixed (.own n)))).2 = Tt
    rw [harm]
    unfold sendTable
    simp only [hcut]
    unfold sendTablesAt
    rw [List.getD_eq_getElem?_getD, hT]
    rfl
  have hd : pt.2.logLength = dep := by
    rw [hlen]
    exact hdep k _ _
  unfold colAt
  rw [hE]
  show pt.2.col x = _
  rw [hcol x (by rw [hd]; exact hx), htab, hc]

/-- The depth of the tree of "send o_u". -/
theorem shapes_U : (realSized.all fun q =>
    ((VerifiableInference.Desc.Own.treesMade (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).Q.codes
      (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).Q.sent).getD {}).shapes.toList.map (·.logN) ==
      [24]) = true := by
  decide +kernel

/-- The depths of the trees of "send o_omega". -/
theorem shapes_O : (realSized.all fun q =>
    ((VerifiableInference.Desc.Own.treesMade
      (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).Q.codes
      (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).Q.sent).getD {}).shapes.toList.map
        (·.logN) == [22, 13]) = true := by
  decide +kernel

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W₀ Rc X₀ S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- The job at the seated place of the test on G_u, at the thread's readers. -/
abbrev jobAtSeatU (Zp : ProofFile.Pub) (Np : H2U.Places4) (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) : TestJob (Common W₀ Rc TableKey) X₀ :=
  (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door (fun c => wts c.w₀) (fun c => rnd c.rc) none).toRun.toTest

/-- The trees' depths at the seated place. -/
theorem depths_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    ProofFile.Honest.K12.Light.depthOf (fourOf Np).U 0 = 24 ∧
      ProofFile.Honest.K12.Light.depthOf (fourOf Np).U 1 = 13 := by
  unfold ProofFile.Honest.K12.Light.depthOf
  rw [first_head_U h]
  exact ⟨rfl, rfl⟩

/-- Where a sending's row covers what it takes, the cut returns at every k. -/
theorem cut_of_cover {Bk : ProverCoinCounts} (k : Coins Bk) (pl : Place) (J : SendJob)
    (h : takesCover Bk ⟨pl, 0⟩ J = true) :
    ((k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes).isSome = true := by
  unfold takesCover at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact cut_of_due k 1 (by omega) ⟨pl, 0⟩ _ h

/-- **`OldAt` at the job at the seated place of the test on G_u**, at a stand of the thread at 9. -/
theorem oldAt_head_U (h : P5J.AtMg o Z D r Zp Np cF)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (hb : treesTo T.bs 9 = 3) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hf1 : 1 ≤ T.fixed (.own 0)) (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hcuts : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E)
    (c : RowCoins [(firstPart (jobAtSeatU Zp Np door wts rnd) : Part V _ _),
      restPart (jobAtSeatU Zp Np door wts rnd)])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) (fourOf Np).U.place
      [(firstPart (jobAtSeatU Zp Np door wts rnd) : Part V _ _),
        restPart (jobAtSeatU Zp Np door wts rnd)] 0 = .ok c) :
    OldAt E ((jobAtSeatU Zp Np door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1).mem
        ((jobAtSeatU Zp Np door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1)))
      (fun j => srcU.getD j (.own 0)) := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hU0 : ((VerifiableInference.Desc.Own.treesMade (jobU ⟨K1.qAt Zp Np, 0⟩).Q.codes
      (jobU ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [24] := by
    have q := shapes_U
    rw [hx₀] at q
    simp only [Option.all_some] at q
    rw [qAt_written Wr Np]
    exact beq_iff_eq.1 q
  have hO0 : ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.codes
      (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [22, 13] := by
    have q := shapes_O
    rw [hx₀] at q
    simp only [Option.all_some] at q
    rw [qAt_written Wr Np]
    exact beq_iff_eq.1 q
  have arm0 : T.table (.own 0) = sendTable (jobU ⟨K1.qAt Zp Np, 0⟩)
      (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 2) 1 0 := by
    rw [htb]
    show (if 0 < treesU (K1.qAt Zp Np) then _ else _) = _
    rw [if_pos (by omega)]
  have arm2 : T.table (.own 2) = sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩)
      (witOf (K1.qAt Zp Np) wts rnd) (sendPlace 5) 1 1 := by
    rw [htb]
    show (if 2 < treesU (K1.qAt Zp Np) then _ else if 2 < 3 then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), hu]
  have dep0 : ∀ k' w' h', (T.table (.own 0) k' w' h').2.logLength = 24 := fun k' w' h' => by
    rw [arm0, sendTable_depth _ _ _ 1 0 k' w' h' (cut_of_cover k' _ _ c2)
      (lt_of_lt_of_eq (show 0 < [24].length by decide) (by
        have e := congrArg List.length hU0
        rw [List.length_map] at e
        exact e.symm)), hU0]
    rfl
  have dep2 : ∀ k' w' h', (T.table (.own 2) k' w' h').2.logLength = 13 := fun k' w' h' => by
    rw [arm2, sendTable_depth _ _ _ 1 1 k' w' h' (cut_of_cover k' _ _ c5)
      (lt_of_lt_of_eq (show 1 < [22, 13].length by decide) (by
        have e := congrArg List.length hO0
        rw [List.length_map] at e
        exact e.symm)), hO0]
    rfl
  obtain ⟨ownU, hUc⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c2)
  obtain ⟨ownO, hOc⟩ := Option.isSome_iff_exists.1 (cut_of_cover k _ _ c5)
  have hl := lendRow_second hc
  have hin : ∀ n, n < 3 → Fmt.TreeSource.own n ∈ T.hand 9 := fun n hn => by
    show _ ∈ T.taken ++ (List.range (treesTo T.bs 9)).map Fmt.TreeSource.own
    rw [ht, hb]
    exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  obtain ⟨d0, d1⟩ := depths_head_U h
  have hsent : E.sent = 3 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := u
    rw [h3, hb]
  refine ⟨fun j hj n hn => ?_, fun j hj x hx => ?_⟩
  · have hj2 : j < 2 := hj
    have h' : srcU.getD j (.own 0) = .own n := hn
    rw [hsent]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · injection h' with h''
      omega
    · injection h' with h''
      omega
  · have hj2 : j < 2 := hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · have hx' : x < 2 ^ 24 := by
        rw [← d0]
        exact hx
      have hv : vecAt (jobU ⟨K1.qAt Zp Np, 0⟩) 0
          (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀) (fun c => rnd c.rc)) none m.st.input
          (frontOf m) = (jobU ⟨K1.qAt Zp Np, 0⟩).data
            ⟨witOf (K1.qAt Zp Np) wts rnd m.st.input, m.st.heard.take (T.fixed (.own 0)), ()⟩ 0 :=
        congrFun (readsBelow_mono (jobU_readsBelow ⟨K1.qAt Zp Np, 0⟩) hf1 _ m.st.heard).symm 0
      refine (col_of_send T (hin 0 (by omega)) _ _ _ 0 24 arm0 dep0 (ProofFile.Honest.K12.Light.width_head h 0).1
        u ownU hUc hx').trans ?_
      exact (tree0_lent_head_U h 0 Bk _ _ _ rfl _ _ _ _ none ownU hUc ownO hOc m.st.input (frontOf m) _
        x rfl c.2.1 hl hcuts hv).symm
    · have hx' : x < 2 ^ 13 := by
        rw [← d1]
        exact hx
      refine (col_of_send T (hin 2 (by omega)) _ _ _ 1 13 arm2 dep2 (ProofFile.Honest.K12.Light.width_head h 0).2
        u ownO hOc hx').trans ?_
      exact (tree1_lent_head_U h 0 Bk _ _ _ rfl _ _ _ _ none ownU hUc ownO hOc m.st.input (frontOf m) _
        x rfl c.2.1 hl hcuts).symm

/-- **`K12At.opens` at the job at the seated place of the test on G_u.** -/
theorem opens_head_U (h : P5J.AtMg o Z D r Zp Np cF)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (hb : treesTo T.bs 9 = 3) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hf1 : 1 ≤ T.fixed (.own 0)) (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hcuts : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E)
    (c : RowCoins [(firstPart (jobAtSeatU Zp Np door wts rnd) : Part V _ _),
      restPart (jobAtSeatU Zp Np door wts rnd)])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) (fourOf Np).U.place
      [(firstPart (jobAtSeatU Zp Np door wts rnd) : Part V _ _),
        restPart (jobAtSeatU Zp Np door wts rnd)] 0 = .ok c) :
    ∃ depths src₀,
      ((jobAtSeatU Zp Np door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1).mem
        ((jobAtSeatU Zp Np door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1))).map (·.1) = depths ∧
      OpensFit (jobAtSeatU Zp Np door wts rnd)
        (proximityTestKind guardedProximityTestParts (jobAtSeatU Zp Np door wts rnd).p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E ((jobAtSeatU Zp Np door wts rnd).trees₀ m.st.input (frontOf m)
        (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1).mem
        ((jobAtSeatU Zp Np door wts rnd).first m.st.input (frontOf m)
          (restCoins (jobAtSeatU Zp Np door wts rnd) c.2.1))) src₀ := by
  have hsent : E.sent = 3 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := u
    rw [h3, hb]
  obtain ⟨d0, d1⟩ := depths_head_U h
  refine ⟨[24, 13], fun j => srcU.getD j (.own 0), ?_, ?_,
    oldAt_head_U h T wts rnd JU JO own₀ door hb ht htb hf1 hu c2 c5 hcuts u c hc⟩
  · show [ProofFile.Honest.K12.Light.depthOf (fourOf Np).U 0, ProofFile.Honest.K12.Light.depthOf (fourOf Np).U 1] =
      [24, 13]
    rw [d0, d1]
  · rw [hsent]
    exact opensFit_head_U h _ rfl rfl

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.oldAt_head_U
#print axioms ProofFile.Honest.K12.AtFile.opens_head_U
#print axioms ProofFile.Honest.K12.AtFile.col_of_send
#print axioms ProofFile.Honest.K12.AtFile.shapes_U
#print axioms ProofFile.Honest.K12.AtFile.shapes_O
